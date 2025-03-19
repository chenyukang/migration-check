use clap::Parser;
use proc_macro2::TokenTree;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::process::exit;
use syn::Type;
use syn::visit::Visit;
use syn::{Fields, ItemStruct};
use walkdir::WalkDir;

pub struct SynVisitor {
    types: Vec<String>,
    type_fingerprint: HashMap<String, String>,
    type_deps: HashMap<String, Vec<String>>,
    store_types: Vec<String>,
    dir: String,
}

impl SynVisitor {
    pub fn new(dir: &str) -> Self {
        SynVisitor {
            types: Vec::new(),
            type_fingerprint: HashMap::new(),
            type_deps: HashMap::new(),
            store_types: Vec::new(),
            dir: dir.to_string(),
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

    fn visit_item_struct(&mut self, item_struct: &ItemStruct) {
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

                    let field_name = field.ident.as_ref().unwrap().to_string();
                    let field_type = quote::quote! { #field.ty }.to_string();
                    fingerprint.push_str(&format!("field:{}:{}\n", field_name, field_type));
                    dep_types.extend(self.calc_dep_types(field.ty.clone()));
                }
            }
            _ => {}
        }

        let mut hasher = Sha256::new();
        hasher.update(fingerprint.as_bytes());
        let finger_hash = format!("{:x}", hasher.finalize());
        self.type_fingerprint
            .insert(struct_name.clone(), finger_hash.clone());
        self.add_type_deps(&struct_name, dep_types.clone());
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
            if file_path.to_string_lossy().contains("/gen/")
                || file_path.to_string_lossy().contains("/migrations/")
            {
                return;
            }
            self.visit_file(&file);
        }
    }

    fn recurisve_dupm_finger(
        &self,
        type_name: &str,
        visited: &mut HashMap<String, bool>,
        dump_fingers: &mut BTreeMap<String, String>,
    ) {
        if visited.contains_key(type_name) {
            return;
        }
        let finger = self.type_fingerprint.get(type_name);
        if let Some(finger) = finger {
            dump_fingers.insert(type_name.to_string(), finger.clone());
        }

        visited.insert(type_name.to_string(), true);
        if let Some(deps_vec) = self.type_deps.get(type_name) {
            for dep in deps_vec {
                self.recurisve_dupm_finger(dep, visited, dump_fingers);
            }
        }
    }

    fn construct_finger_print(&self) -> BTreeMap<String, String> {
        let mut dump_fingers = BTreeMap::new();
        let mut visited = HashMap::new();
        for type_name in &self.store_types {
            self.recurisve_dupm_finger(type_name, &mut visited, &mut dump_fingers);
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

    pub fn check_finger_and_dump(&self, output: String, update: bool) {
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
                "Please use `migration-check -d {} -o {} -u` to update the fingerprint, and remember to write a migration",
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
        self.visit_item_struct(item_struct);
    }

    fn visit_item(&mut self, item: &syn::Item) {
        match item {
            syn::Item::Struct(item_struct) => self.visit_item_struct(item_struct),
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

                let field_type = quote::quote! { #field.ty }.to_string();
                fingerprint.push_str(&format!("field:{}\n", field_type));

                dep_types.extend(self.calc_dep_types(field.ty.clone()));
            }
        }

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
        path.push_str(".store_digest.json");
        path
    });
    visitor.check_finger_and_dump(output, cli.update);
}
