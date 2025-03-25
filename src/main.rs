use clap::Parser;
use proc_macro2::TokenTree;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::process::exit;
use syn::visit::Visit;
use syn::Type;
use syn::{Fields, ItemStruct};
use walkdir::WalkDir;

pub struct SynVisitor {
    types: Vec<String>,
    type_fingerprint: HashMap<String, String>,
    type_deps: HashMap<String, Vec<String>>,
    store_types: Vec<String>,
    dir: String,
    in_rpc: bool,
    has_error: bool,
    current_file: String,
}

impl SynVisitor {
    pub fn new(dir: &str) -> Self {
        SynVisitor {
            types: Vec::new(),
            type_fingerprint: HashMap::new(),
            type_deps: HashMap::new(),
            store_types: Vec::new(),
            dir: dir.to_string(),
            in_rpc: false,
            has_error: false,
            current_file: String::new(),
        }
    }

    fn calc_dep_types(&self, ty: Type) -> Vec<String> {
        let mut dep_types = vec![];
        match ty {
            Type::Path(type_path) => {
                for elem in quote::quote! { #type_path } {
                    match elem {
                        TokenTree::Ident(ident) => {
                            dep_types.push(format!("{}", quote::quote! { #ident }));
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        dep_types
    }

    fn should_skip_field(&self, field: &syn::Field) -> bool {
        field.attrs.iter().any(|attr| {
            let attr_name = attr.path.segments.last().unwrap().ident.to_string();
            let attr_value = attr.tokens.to_string();
            attr_name == "serde" && attr_value.contains("skip")
        })
    }

    // check if the field is a number and has the serde_as attribute
    // with the expected value
    // e.g. #[serde_as(as = "Option<u8>")]
    // or #[serde_as(as = "u8")]
    fn check_rpc_field(&mut self, struct_name: &str, field: &syn::Field) {
        let ty = field.ty.clone();
        let dep_types = self.calc_dep_types(ty);
        if dep_types.len() > 2 {
            return;
        }
        let last = dep_types.last().unwrap();
        if !(last == "u8" || last == "u16" || last == "u32" || last == "u64" || last == "u128") {
            //eprintln!("Field type is not a number: {}", last);
            return;
        }
        let is_option = dep_types.len() == 2 && dep_types[0] == "Option";

        let serde_attrs = field
            .attrs
            .iter()
            .filter(|attr| attr.path.is_ident("serde_as"))
            .collect::<Vec<_>>();
        let expected_hex = format!("{}Hex", last.to_uppercase());
        let expected_serde_as_value = if is_option {
            format!("Option<{}>", expected_hex)
        } else {
            expected_hex
        };

        if !serde_attrs.iter().any(|attr| {
            let attr_str = attr.tokens.to_string();
            if let Some(attr_value) = attr_str.split('=').nth(1) {
                attr_value.contains(&expected_serde_as_value)
            } else {
                false
            }
        }) {
            eprintln!(
                "File: {} struct/enum: {} field_name: {} expected serde_as: {}, but you missed it",
                self.current_file,
                struct_name,
                field.ident.as_ref().unwrap(),
                expected_serde_as_value
            );
            self.has_error = true;
        }
    }

    fn inner_visit_item_struct(&mut self, item_struct: &ItemStruct) {
        let struct_name = item_struct.ident.to_string();
        self.types.push(struct_name.clone());

        let mut fingerprint = String::new();

        fingerprint.push_str(&format!("struct_name:{}\n", struct_name));

        let mut dep_types = vec![];
        match &item_struct.fields {
            Fields::Named(fields) => {
                for field in &fields.named {
                    if self.should_skip_field(field) {
                        continue;
                    }
                    if self.in_rpc {
                        self.check_rpc_field(&struct_name, field);
                        continue;
                    }

                    //let field_name = field.ident.as_ref().unwrap().to_string();
                    let field_type = quote::quote! { #field.ty }.to_string();
                    let field_type = field_type.split(":").last().unwrap_or_default();
                    fingerprint.push_str(&format!("field: {}\n", field_type));
                    dep_types.extend(self.calc_dep_types(field.ty.clone()));
                }
            }
            _ => {}
        }

        if !self.in_rpc {
            let mut hasher = Sha256::new();
            hasher.update(fingerprint.as_bytes());
            let finger_hash = format!("{:x}", hasher.finalize());
            self.type_fingerprint
                .insert(struct_name.clone(), finger_hash.clone());
            self.add_type_deps(&struct_name, dep_types.clone());
        }
    }

    fn inner_visit_item_enum(&mut self, item_enum: &'_ syn::ItemEnum) {
        let enum_name = item_enum.ident.to_string();
        let mut dep_types = vec![];
        self.types.push(enum_name.clone());

        let mut fingerprint = String::new();
        fingerprint.push_str(&format!("enum_name:{}\n", enum_name));

        for variant in &item_enum.variants {
            let variant_name = variant.ident.to_string();
            fingerprint.push_str(&format!("variant:{}\n", variant_name));

            for field in &variant.fields {
                if self.should_skip_field(field) {
                    continue;
                }
                if self.in_rpc {
                    self.check_rpc_field(&enum_name, field);
                    continue;
                }

                let field_type = quote::quote! { #field.ty }.to_string();
                fingerprint.push_str(&format!("field:{}\n", field_type));
                dep_types.extend(self.calc_dep_types(field.ty.clone()));
            }
        }

        if !self.in_rpc {
            let mut hasher = Sha256::new();
            hasher.update(fingerprint.as_bytes());
            let finger_hash = format!("{:x}", hasher.finalize());
            self.type_fingerprint.insert(enum_name.clone(), finger_hash);
            self.add_type_deps(&enum_name, dep_types.clone());
            if enum_name == "KeyValue" {
                self.store_types = dep_types.clone();
            }
        }
    }

    fn add_type_deps(&mut self, type_name: &str, dep_types: Vec<String>) {
        let mut deps = dep_types.clone();
        if !deps.is_empty() {
            deps.sort();
            deps.dedup();
            self.type_deps
                .entry(type_name.to_string())
                .or_default()
                .extend(deps.clone());
        }
    }

    fn visit_source_file(&mut self, file_path: &std::path::Path) {
        let code = std::fs::read_to_string(file_path).unwrap();
        if let Ok(file) = syn::parse_file(&code) {
            let file_path = file_path.to_string_lossy();
            if file_path.contains("/gen/") || file_path.contains("/migrations/") {
                return;
            }
            self.in_rpc = file_path.contains("/rpc/");
            self.current_file = file_path.to_string();
            self.visit_file(&file);
            self.in_rpc = false;
        }
    }

    fn collect_fingerprints(
        &self,
        type_name: &str,
        visited: &mut HashMap<String, bool>,
        fingerprints: &mut BTreeMap<String, String>,
    ) {
        if visited.contains_key(type_name) {
            return;
        }
        let finger = self.type_fingerprint.get(type_name);
        if let Some(finger) = finger {
            fingerprints.insert(type_name.to_string(), finger.clone());
        }

        visited.insert(type_name.to_string(), true);
        if let Some(deps_vec) = self.type_deps.get(type_name) {
            for dep in deps_vec {
                self.collect_fingerprints(dep, visited, fingerprints);
            }
        }
    }

    fn construct_finger_print(&self) -> BTreeMap<String, String> {
        let mut dump_fingers = BTreeMap::new();
        let mut visited = HashMap::new();
        for type_name in &self.store_types {
            self.collect_fingerprints(type_name, &mut visited, &mut dump_fingers);
        }
        dump_fingers
    }

    fn recurisve_find_type(
        &self,
        target_type: &str,
        type_name: &str,
        current_chain: &mut Vec<String>,
        result: &mut Vec<Vec<String>>,
    ) {
        if target_type == type_name {
            current_chain.push(type_name.to_string());
            result.push(current_chain.clone());
            return;
        }
        current_chain.push(type_name.to_string());
        if let Some(deps_vec) = self.type_deps.get(type_name) {
            for dep in deps_vec {
                let mut next_chain = current_chain.clone();
                self.recurisve_find_type(target_type, dep, &mut next_chain, result);
            }
        }
    }

    fn try_find_type_chain(&self, target_type: &str) -> Vec<String> {
        let mut result = vec![];
        for type_name in &self.store_types {
            let mut current_chain = vec![];
            self.recurisve_find_type(target_type, type_name, &mut current_chain, &mut result);
        }
        result
            .iter()
            .map(|chain| chain.join(" -> "))
            .collect::<Vec<String>>()
    }

    pub fn report_and_dump(&self, output: String, update: bool) {
        if self.has_error {
            eprintln!("Please fix the errors in src/rpc");
            exit(1);
        }

        let old_finger: HashMap<String, String> = if !std::path::Path::new(&output).exists() {
            Default::default()
        } else {
            let old_finger = std::fs::read_to_string(&output).unwrap();
            serde_json::from_str(&old_finger).unwrap()
        };
        let new_finger = self.construct_finger_print();

        let mut failed = false;
        if !update {
            for (type_name, old_finger) in old_finger.iter() {
                if let Some(new_finger) = new_finger.get(type_name) {
                    if old_finger != new_finger {
                        eprintln!(
                            "Type fingerprint changed: {} {} -> {}",
                            type_name, old_finger, new_finger
                        );
                        eprintln!("Type dependency chain:");
                        for chain in self.try_find_type_chain(type_name) {
                            eprintln!("  {}", chain);
                        }
                        failed = true;
                    }
                }
            }
        }
        if failed {
            eprintln!("migration check failed ...");
            eprintln!(
                "Please use `migration-check -s {} -o {} -u` to update the fingerprint, and remember to write a migration",
                self.dir, output
            );
            exit(1);
        } else {
            eprintln!("dumped to: {}", output.clone());
            let dump_json = serde_json::to_string_pretty(&new_finger).unwrap();
            let mut file = std::fs::File::create(output).unwrap();
            std::io::Write::write_all(&mut file, dump_json.as_bytes()).unwrap();
            eprintln!("migration check passed ...");
        }
    }

    pub fn walk_dir(&mut self) {
        let dir = self.dir.clone();
        for entry in WalkDir::new(dir).follow_links(true).into_iter() {
            match entry {
                Ok(ref e)
                    if !e.file_name().to_string_lossy().starts_with('.')
                        && e.file_name().to_string_lossy().ends_with(".rs") =>
                {
                    self.visit_source_file(e.path());
                }
                _ => (),
            }
        }
    }
}

impl Visit<'_> for SynVisitor {
    fn visit_item_struct(&mut self, item_struct: &ItemStruct) {
        self.inner_visit_item_struct(item_struct);
    }

    fn visit_item(&mut self, item: &syn::Item) {
        match item {
            syn::Item::Struct(item_struct) => self.inner_visit_item_struct(item_struct),
            syn::Item::Enum(item_enum) => self.visit_item_enum(item_enum),
            syn::Item::Type(item_type) => {
                let type_name = item_type.ident.to_string();
                self.types.push(type_name.clone());
                let type_deps = self.calc_dep_types(*item_type.ty.clone());
                self.add_type_deps(&type_name, type_deps.clone());
            }
            _ => {}
        }
    }

    fn visit_item_enum(&mut self, item_enum: &'_ syn::ItemEnum) {
        self.inner_visit_item_enum(item_enum);
    }
}

#[derive(Parser)]
#[command(author, version, about = "Schema migration checking tool")]
struct Cli {
    /// Output file path
    #[clap(short, long)]
    source_code_dir: String,

    /// Output file path
    #[clap(short, long)]
    output: Option<String>,

    /// for update fingerprint
    /// Force update fingerprint
    #[arg(short = 'u', long, default_value_t = false)]
    update: bool,
}

fn main() {
    let cli = Cli::parse();
    let mut visitor = SynVisitor::new(&cli.source_code_dir);
    visitor.walk_dir();

    let output = cli.output.clone().unwrap_or_else(|| {
        let mut path = cli.source_code_dir.clone();
        path.push_str(".schema.json");
        path
    });
    visitor.report_and_dump(output, cli.update);
}
