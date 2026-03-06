use clap::Parser;
use proc_macro2::TokenTree;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::process::exit;
use syn::visit::Visit;
use syn::Type;
use syn::{Fields, ItemStruct};
use walkdir::WalkDir;

/// Well-known primitive types and external crate types that are not expected
/// to be defined in the scanned source directories. These are excluded from
/// the "store types must live in types-dir" check.
const BUILTIN_TYPES: &[&str] = &[
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "f32",
    "f64",
    "bool",
    "String",
    "str",
    "usize",
    "isize",
    "Option",
    "Vec",
    "HashMap",
    "HashSet",
    "BTreeMap",
    "BTreeSet",
    "Box",
    "Arc",
    "Rc",
    "Cow",
    "PhantomData",
    "Duration",
    // External crate types commonly seen in KeyValue
    "PeerId",
    "OutPoint",
];

pub struct SynVisitor {
    types: Vec<String>,
    type_fingerprint: HashMap<String, String>,
    type_deps: HashMap<String, Vec<String>>,
    store_types: Vec<String>,
    /// KeyValue variant info: (variant_name, dep_types) for each variant.
    /// Used to produce meaningful dep chains like `KeyValue::Variant -> Type -> Target`.
    store_variants: Vec<(String, Vec<String>)>,
    /// All source directories to scan
    dirs: Vec<String>,
    /// Optional: the types-dir path prefix. Types defined in files under this
    /// directory are considered "in the types crate".
    types_dir: Option<String>,
    /// Records which file each type was first defined in.
    type_file: HashMap<String, String>,
    /// Types that derive `Serialize` via `#[derive(Serialize)]`.
    /// For these types, we know ALL non-skipped fields are serialized, so we
    /// follow their field deps in the types-dir check.
    derive_serializable_types: HashSet<String>,
    /// Types that have a custom `impl Serialize for T`.
    /// For these, we can't determine which fields are serialized from syntax
    /// alone, so we include them in the check but DON'T follow their field deps.
    custom_serializable_types: HashSet<String>,
    in_rpc: bool,
    has_error: bool,
    current_file: String,
}

impl SynVisitor {
    pub fn new(dirs: Vec<String>, types_dir: Option<String>) -> Self {
        SynVisitor {
            types: Vec::new(),
            type_fingerprint: HashMap::new(),
            type_deps: HashMap::new(),
            store_types: Vec::new(),
            store_variants: Vec::new(),
            dirs,
            types_dir,
            type_file: HashMap::new(),
            derive_serializable_types: HashSet::new(),
            custom_serializable_types: HashSet::new(),
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
            Type::Tuple(type_tuple) => {
                for elem in &type_tuple.elems {
                    dep_types.extend(self.calc_dep_types(elem.clone()));
                }
            }
            _ => {}
        }
        dep_types
    }

    /// Check if the item attributes include `#[derive(Serialize, ...)]`.
    fn has_serialize_derive(attrs: &[syn::Attribute]) -> bool {
        attrs.iter().any(|attr| {
            if !attr.path().is_ident("derive") {
                return false;
            }
            if let syn::Meta::List(meta_list) = &attr.meta {
                let tokens_str = meta_list.tokens.to_string();
                // Check for "Serialize" as a standalone token in the derive list
                tokens_str.split(',').any(|part| part.trim() == "Serialize")
            } else {
                false
            }
        })
    }

    /// Returns true if the field should be excluded from the fingerprint and
    /// dependency graph. This includes:
    /// - `#[serde(skip)]`, `#[serde(skip_serializing)]`, `#[serde(skip_deserializing)]`
    /// - `#[skip_store]` - explicit annotation for migration-check
    /// - `#[cfg_attr(any(), skip_store)]` - conditional skip_store annotation
    fn should_skip_field(&self, field: &syn::Field) -> bool {
        field.attrs.iter().any(|attr| {
            let attr_name = attr.path().segments.last().unwrap().ident.to_string();

            // Check for #[skip_store] attribute
            if attr_name == "skip_store" {
                return true;
            }

            // Check for #[cfg_attr(any(), skip_store)] pattern
            if attr_name == "cfg_attr" {
                let tokens = self.get_attr_tokens(attr);
                // Check if tokens contain "skip_store"
                if tokens.contains("skip_store") {
                    return true;
                }
            }

            // Check for serde skip attributes
            if attr_name == "serde" {
                let tokens = self.get_attr_tokens(attr);
                // Split by comma to check each individual directive.
                // e.g. #[serde(skip, default)] → tokens = "skip , default"
                return tokens.split(',').any(|part| {
                    let trimmed = part.trim();
                    trimmed == "skip"
                        || trimmed == "skip_serializing"
                        || trimmed == "skip_deserializing"
                });
            }

            false
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
        let Some(last) = dep_types.last() else {
            return;
        };
        if field.ident.is_none() {
            return;
        }
        if !(last == "u8" || last == "u16" || last == "u32" || last == "u64" || last == "u128") {
            return;
        }
        let is_option = dep_types.len() == 2 && dep_types[0] == "Option";

        let serde_attrs = field
            .attrs
            .iter()
            .filter(|attr| attr.path().is_ident("serde_as") || attr.path().is_ident("serde"))
            .collect::<Vec<_>>();
        let expected_hex = format!("{}Hex", last.to_uppercase());
        let expected_serde_as_value = if is_option {
            format!("Option<{}>", expected_hex)
        } else {
            expected_hex
        };

        if !serde_attrs.iter().any(|attr| {
            let attr_str = self.get_attr_tokens(attr);
            if let Some(attr_value) = attr_str.split('=').nth(1) {
                attr_value.contains(&expected_serde_as_value)
            } else {
                false
            }
        }) {
            eprintln!(
                "File: {} struct/enum: {} field_name: {:?} expected serde_as: {}, but you missed it",
                self.current_file, struct_name, field.ident, expected_serde_as_value
            );
            self.has_error = true;
        }
    }

    fn get_attr_tokens(&self, attr: &syn::Attribute) -> String {
        match &attr.meta {
            syn::Meta::List(meta_list) => meta_list.tokens.to_string(),
            syn::Meta::NameValue(_meta_name_value) => "".to_string(),
            _ => String::new(),
        }
    }

    /// Returns true if the current file is under a `/rpc/` directory.
    /// Types defined there are RPC-specific wrappers and should not shadow
    /// the canonical definitions in the types crate.
    fn is_rpc_file(&self) -> bool {
        self.current_file.contains("/rpc/")
    }

    /// Record the file where a type is defined, preferring non-RPC locations.
    /// If the type was previously recorded from an RPC file and we now see it
    /// in a non-RPC file, overwrite the record.
    fn record_type_file(&mut self, type_name: &str) {
        if self.is_rpc_file() {
            // Only insert if this type has never been seen before
            self.type_file
                .entry(type_name.to_string())
                .or_insert_with(|| self.current_file.clone());
        } else {
            // Non-RPC file always takes priority — overwrite any previous entry
            self.type_file
                .insert(type_name.to_string(), self.current_file.clone());
        }
    }

    fn inner_visit_item_struct(&mut self, item_struct: &ItemStruct) {
        let struct_name = item_struct.ident.to_string();
        self.types.push(struct_name.clone());
        self.record_type_file(&struct_name);

        if Self::has_serialize_derive(&item_struct.attrs) {
            self.derive_serializable_types.insert(struct_name.clone());
        }

        let mut fingerprint = String::new();

        fingerprint.push_str(&format!("struct_name:{}\n", struct_name));

        let mut dep_types = vec![];
        match &item_struct.fields {
            Fields::Named(fields) => {
                for field in &fields.named {
                    if self.in_rpc {
                        // RPC check runs on all fields (regardless of serde attrs)
                        self.check_rpc_field(&struct_name, field);
                    } else {
                        // For fingerprint/deps, skip fields with #[serde(skip)]
                        if self.should_skip_field(field) {
                            continue;
                        }
                        let field_type = quote::quote! { #field.ty }.to_string();
                        let field_type = field_type.split(":").last().unwrap_or_default();
                        fingerprint.push_str(&format!("field: {}\n", field_type));
                        dep_types.extend(self.calc_dep_types(field.ty.clone()));
                    }
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
        self.record_type_file(&enum_name);

        if Self::has_serialize_derive(&item_enum.attrs) {
            self.derive_serializable_types.insert(enum_name.clone());
        }

        let is_key_value = enum_name == "KeyValue";

        let mut fingerprint = String::new();
        fingerprint.push_str(&format!("enum_name:{}\n", enum_name));

        for variant in &item_enum.variants {
            let variant_name = variant.ident.to_string();
            fingerprint.push_str(&format!("variant:{}\n", variant_name));

            let mut variant_dep_types = vec![];
            for field in &variant.fields {
                if self.in_rpc {
                    // RPC check runs on all fields (regardless of serde attrs)
                    self.check_rpc_field(&enum_name, field);
                } else {
                    // For fingerprint/deps, skip fields with #[serde(skip)]
                    if self.should_skip_field(field) {
                        continue;
                    }
                    let field_type = quote::quote! { #field.ty }.to_string();
                    fingerprint.push_str(&format!("field:{}\n", field_type));
                    variant_dep_types.extend(self.calc_dep_types(field.ty.clone()));
                }
            }

            if is_key_value && !self.in_rpc {
                self.store_variants
                    .push((variant_name, variant_dep_types.clone()));
            }
            dep_types.extend(variant_dep_types);
        }

        if !self.in_rpc {
            let mut hasher = Sha256::new();
            hasher.update(fingerprint.as_bytes());
            let finger_hash = format!("{:x}", hasher.finalize());
            self.type_fingerprint.insert(enum_name.clone(), finger_hash);
            self.add_type_deps(&enum_name, dep_types.clone());
            if is_key_value {
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

        // For types with custom `impl Serialize`: don't record their fingerprint.
        // But still traverse their dependencies to find the actual serialized types.
        // Dependencies from fields marked with `skip_store` have already been excluded
        // when building type_deps.
        let is_custom_serialize = self.custom_serializable_types.contains(type_name);
        if !is_custom_serialize {
            let finger = self.type_fingerprint.get(type_name);
            if let Some(finger) = finger {
                fingerprints.insert(type_name.to_string(), finger.clone());
            }
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

    /// Collect types reachable from the store types that are actually part of
    /// serialized data. A type is included if:
    /// 1. It is a direct KeyValue variant type, OR
    /// 2. It is a dependency of a type with `#[derive(Serialize)]`
    ///
    /// Types with custom `impl Serialize` are included but their field deps
    /// are NOT followed (since we can't know which fields the custom impl
    /// actually serializes).
    ///
    /// Types without any Serialize impl are NOT traversed — they appear in
    /// fields that are never serialized (actor messages, error types, etc.).
    fn collect_serializable_store_types(&self) -> HashSet<String> {
        let builtin: HashSet<&str> = BUILTIN_TYPES.iter().copied().collect();
        let mut result = HashSet::new();
        let mut visited = HashSet::new();

        fn collect_recursive(
            visitor: &SynVisitor,
            type_name: &str,
            visited: &mut HashSet<String>,
            result: &mut HashSet<String>,
            builtin: &HashSet<&str>,
        ) {
            if visited.contains(type_name) || builtin.contains(type_name) {
                return;
            }
            visited.insert(type_name.to_string());

            // For types with custom `impl Serialize`: don't add to result,
            // but still traverse their dependencies to find the actual serialized types.
            // The dependencies have already been filtered to exclude skip_store fields.
            let is_custom_serialize = visitor.custom_serializable_types.contains(type_name);
            if !is_custom_serialize {
                // Only include this type if it has a fingerprint (i.e., it was defined
                // in the scanned source)
                if visitor.type_fingerprint.contains_key(type_name) {
                    result.insert(type_name.to_string());
                }
            }

            // For types with #[derive(Serialize)] or custom impl Serialize:
            // follow their field deps. For derive-serializable, we know all non-skipped
            // fields are serialized. For custom Serialize, deps are already filtered.
            if visitor.derive_serializable_types.contains(type_name) || is_custom_serialize {
                if let Some(deps_vec) = visitor.type_deps.get(type_name) {
                    for dep in deps_vec {
                        collect_recursive(visitor, dep, visited, result, builtin);
                    }
                }
                return;
            }

            // Types without any Serialize: don't traverse further.
            // They appear in the dep graph but are not part of serialized data.
        }

        for type_name in &self.store_types {
            collect_recursive(self, type_name, &mut visited, &mut result, &builtin);
        }
        result
    }

    /// Check that all types included in the migration schema are defined in
    /// the types-dir. Only checks types that are serializable and reachable
    /// from KeyValue. Returns true if all checks pass.
    pub fn check_store_types_in_types_dir(&self) -> bool {
        let types_dir = match &self.types_dir {
            Some(d) => d,
            None => return true, // no types-dir specified, skip check
        };

        let builtin: HashSet<&str> = BUILTIN_TYPES.iter().copied().collect();
        let store_types = self.collect_serializable_store_types();
        let mut has_error = false;

        for type_name in store_types.iter() {
            // Skip builtin/external types
            if builtin.contains(type_name.as_str()) {
                continue;
            }
            // Check where this type is defined
            if let Some(file_path) = self.type_file.get(type_name) {
                if !file_path.contains(types_dir) {
                    eprintln!(
                        "WARNING: Store type `{}` is NOT defined in types-dir ({}), found in: {}",
                        type_name, types_dir, file_path
                    );
                    // Print dependency chains for context
                    let chains = self.try_find_type_chain(type_name, true);
                    for chain in &chains {
                        eprintln!("  Dependency chain: {}", chain);
                    }
                    has_error = true;
                }
            }
        }

        if has_error {
            eprintln!();
            eprintln!("Some store types are defined outside of the types crate.");
            eprintln!("Please move them to the types crate to ensure migration safety.");
        }

        !has_error
    }

    /// Find dependency chains from KeyValue variants to a target type.
    /// Returns chains like: `KeyValue::PaymentHistoryTimedResult -> Direction`
    /// or `KeyValue::PaymentSession -> PaymentData -> SomeType`
    ///
    /// If `serialize_aware` is true, only follows deps through derive-Serialize types
    /// (matching the collect_serializable_store_types logic). Otherwise follows all deps.
    fn try_find_type_chain(&self, target_type: &str, serialize_aware: bool) -> Vec<String> {
        let builtin: HashSet<&str> = BUILTIN_TYPES.iter().copied().collect();
        let mut result = vec![];

        for (variant_name, variant_deps) in &self.store_variants {
            // Check if this variant can reach target_type
            for dep in variant_deps {
                let mut visited = HashSet::new();
                let mut chain = vec![format!("KeyValue::{}", variant_name)];
                if self.find_chain_to_target(
                    target_type,
                    dep,
                    &mut chain,
                    &mut visited,
                    &builtin,
                    serialize_aware,
                ) {
                    result.push(chain.join(" -> "));
                }
            }
        }

        // Deduplicate chains
        result.sort();
        result.dedup();
        result
    }

    /// DFS to find a chain from `current` to `target_type`.
    /// If `serialize_aware` is true, only follows deps through derive-Serialize types
    /// and skips custom-Serialize types.
    fn find_chain_to_target(
        &self,
        target_type: &str,
        current: &str,
        chain: &mut Vec<String>,
        visited: &mut HashSet<String>,
        builtin: &HashSet<&str>,
        serialize_aware: bool,
    ) -> bool {
        if current == target_type {
            chain.push(current.to_string());
            return true;
        }

        if visited.contains(current) || builtin.contains(current) {
            return false;
        }
        visited.insert(current.to_string());

        if serialize_aware {
            // Skip custom-Serialize types (we don't follow their deps)
            if self.custom_serializable_types.contains(current) {
                return false;
            }

            // Only follow deps for derive-Serialize types
            if !self.derive_serializable_types.contains(current) {
                return false;
            }
        }

        if let Some(deps) = self.type_deps.get(current) {
            chain.push(current.to_string());
            for dep in deps {
                let mut branch_chain = chain.clone();
                let mut branch_visited = visited.clone();
                if self.find_chain_to_target(
                    target_type,
                    dep,
                    &mut branch_chain,
                    &mut branch_visited,
                    builtin,
                    serialize_aware,
                ) {
                    *chain = branch_chain;
                    visited.extend(branch_visited);
                    return true;
                }
            }
            chain.pop(); // backtrack
        }

        false
    }

    /// Query a single type: print whether it is reachable from KeyValue (store-related)
    /// and if so, print all dependency chains from KeyValue to it.
    pub fn query_type(&self, type_name: &str) {
        // First check if the type exists at all in the scanned source
        if !self.types.contains(&type_name.to_string()) {
            eprintln!(
                "Type `{}` was not found in the scanned source directories.",
                type_name
            );
            eprintln!("Scanned directories: {:?}", self.dirs);
            exit(1);
        }

        // Check if it's reachable from KeyValue (using serialize-aware collection)
        let store_types = self.collect_serializable_store_types();
        if store_types.contains(type_name) {
            println!(
                "Type `{}` is STORE-RELATED (reachable from KeyValue).",
                type_name
            );
            println!();

            // Print file location
            if let Some(file) = self.type_file.get(type_name) {
                println!("Defined in: {}", file);
            }

            // Print dependency chains (serialize-aware to match the actual tracking)
            let chains = self.try_find_type_chain(type_name, true);
            if chains.is_empty() {
                println!("  (direct KeyValue variant type)");
            } else {
                println!("Dependency chain(s) from KeyValue:");
                for chain in &chains {
                    println!("  {}", chain);
                }
            }

            // Also show what types this type depends on (that are also store types)
            if let Some(deps) = self.type_deps.get(type_name) {
                let store_deps: Vec<&String> = deps
                    .iter()
                    .filter(|d| store_types.contains(d.as_str()))
                    .collect();
                if !store_deps.is_empty() {
                    println!();
                    println!("Store-related dependencies of `{}`:", type_name);
                    for dep in &store_deps {
                        println!("  -> {}", dep);
                    }
                }
            }
        } else {
            println!("Type `{}` is NOT related to the store.", type_name);
            println!(
                "It is not reachable from KeyValue and can be changed without a store migration."
            );
            if let Some(file) = self.type_file.get(type_name) {
                println!("Defined in: {}", file);
            }
        }
    }

    /// Collect ALL type names reachable from KeyValue, following all deps
    /// (not serialize-aware — includes everything in the transitive closure).
    fn collect_all_store_reachable_types(&self) -> HashSet<String> {
        let builtin: HashSet<&str> = BUILTIN_TYPES.iter().copied().collect();
        let mut visited = HashSet::new();

        fn walk(
            visitor: &SynVisitor,
            type_name: &str,
            visited: &mut HashSet<String>,
            builtin: &HashSet<&str>,
        ) {
            if visited.contains(type_name) || builtin.contains(type_name) {
                return;
            }
            // Only include types that were actually defined in scanned source
            if !visitor.type_fingerprint.contains_key(type_name)
                && !visitor.type_deps.contains_key(type_name)
            {
                return;
            }
            visited.insert(type_name.to_string());
            if let Some(deps) = visitor.type_deps.get(type_name) {
                for dep in deps {
                    walk(visitor, dep, visited, builtin);
                }
            }
        }

        for type_name in &self.store_types {
            walk(self, type_name, &mut visited, &builtin);
        }
        visited
    }

    /// List all types NOT reachable from KeyValue.
    /// Groups output by file path for readability.
    pub fn list_non_store_types(&self) {
        let all_store_types = self.collect_all_store_reachable_types();

        // Collect all defined types (with fingerprints, i.e., structs/enums)
        // that are NOT in the store reachable set
        let mut non_store: Vec<(&String, Option<&String>)> = self
            .types
            .iter()
            .filter(|t| !all_store_types.contains(t.as_str()))
            .filter(|t| !BUILTIN_TYPES.contains(&t.as_str()))
            .filter(|t| self.type_fingerprint.contains_key(t.as_str()))
            .map(|t| (t, self.type_file.get(t)))
            .collect();

        // Sort by file path then by name
        non_store.sort_by(|a, b| {
            let fa = a.1.map(|s| s.as_str()).unwrap_or("");
            let fb = b.1.map(|s| s.as_str()).unwrap_or("");
            fa.cmp(fb).then(a.0.cmp(b.0))
        });
        non_store.dedup();

        // Also collect store types for comparison
        let mut store_list: Vec<(&String, Option<&String>)> = self
            .types
            .iter()
            .filter(|t| all_store_types.contains(t.as_str()))
            .filter(|t| !BUILTIN_TYPES.contains(&t.as_str()))
            .filter(|t| self.type_fingerprint.contains_key(t.as_str()))
            .map(|t| (t, self.type_file.get(t)))
            .collect();
        store_list.sort_by(|a, b| {
            let fa = a.1.map(|s| s.as_str()).unwrap_or("");
            let fb = b.1.map(|s| s.as_str()).unwrap_or("");
            fa.cmp(fb).then(a.0.cmp(b.0))
        });
        store_list.dedup();

        println!(
            "=== Types RELATED to store ({} types) ===",
            store_list.len()
        );
        let mut last_file = "";
        for (type_name, file) in &store_list {
            let f = file.map(|s| s.as_str()).unwrap_or("(unknown)");
            if f != last_file {
                println!();
                println!("  # {}", f);
                last_file = f;
            }
            println!("    {}", type_name);
        }

        println!();
        println!(
            "=== Types NOT related to store ({} types) ===",
            non_store.len()
        );
        last_file = "";
        for (type_name, file) in &non_store {
            let f = file.map(|s| s.as_str()).unwrap_or("(unknown)");
            if f != last_file {
                println!();
                println!("  # {}", f);
                last_file = f;
            }
            println!("    {}", type_name);
        }
    }

    pub fn report_and_dump(&self, output: String, update: bool) {
        if self.has_error {
            eprintln!("Please fix the errors in src/rpc");
            exit(1);
        }

        // Check store types are in types-dir (before generating schema)
        if !self.check_store_types_in_types_dir() {
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
                        for chain in self.try_find_type_chain(type_name, false) {
                            eprintln!("  {}", chain);
                        }
                        failed = true;
                    }
                }
            }
        }
        if failed {
            let dirs_str = self.dirs.join(" -s ");
            eprintln!("migration check failed ...");
            eprintln!(
                "Please use `migration-check -s {} -o {} -u` to update the fingerprint, and remember to write a migration",
                dirs_str, output
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
        let dirs = self.dirs.clone();
        let mut files = vec![];
        for dir in &dirs {
            for entry in WalkDir::new(dir).follow_links(true).into_iter() {
                match entry {
                    Ok(ref e)
                        if !e.file_name().to_string_lossy().starts_with('.')
                            && e.file_name().to_string_lossy().ends_with(".rs") =>
                    {
                        files.push(e.path().to_owned());
                    }
                    _ => (),
                }
            }
        }
        // different order may produce different hash
        files.sort();
        for file_path in files {
            self.visit_source_file(&file_path);
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
                self.record_type_file(&type_name);
                let type_deps = self.calc_dep_types(*item_type.ty.clone());
                self.add_type_deps(&type_name, type_deps.clone());
            }
            syn::Item::Impl(item_impl) => {
                // Detect `impl Serialize for TypeName` to track custom Serialize impls
                if let Some((_, ref trait_path, _)) = item_impl.trait_ {
                    let trait_name = trait_path
                        .segments
                        .last()
                        .map(|s| s.ident.to_string())
                        .unwrap_or_default();
                    if trait_name == "Serialize" {
                        if let Type::Path(ref type_path) = *item_impl.self_ty {
                            if let Some(seg) = type_path.path.segments.last() {
                                self.custom_serializable_types.insert(seg.ident.to_string());
                            }
                        }
                    }
                }
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
    /// Source code directories to scan (can be specified multiple times)
    #[clap(short, long, required = true, num_args = 1..)]
    source_code_dir: Vec<String>,

    /// Output file path
    #[clap(short, long)]
    output: Option<String>,

    /// Types crate source directory. When specified, the tool will check that
    /// all store-reachable types (from KeyValue enum) are defined within this
    /// directory and error if any are found outside it.
    #[clap(short, long)]
    types_dir: Option<String>,

    /// Force update fingerprint
    #[arg(short = 'u', long, default_value_t = false)]
    update: bool,

    /// Query a type's store dependency chain. If the type is reachable from
    /// KeyValue (i.e., it is persisted to the store), prints the dependency
    /// chain(s). Otherwise prints that the type is not related to the store.
    #[clap(short, long)]
    query_type: Option<String>,

    /// List all types defined in the scanned source that are NOT related to
    /// the store (i.e., not reachable from KeyValue). Useful for identifying
    /// types that can be safely moved without migration concerns.
    #[clap(long, default_value_t = false)]
    list_non_store_types: bool,
}

fn main() {
    let cli = Cli::parse();
    let mut visitor = SynVisitor::new(cli.source_code_dir.clone(), cli.types_dir.clone());
    visitor.walk_dir();

    // --query-type: query a single type and exit
    if let Some(ref type_name) = cli.query_type {
        visitor.query_type(type_name);
        return;
    }

    // --list-non-store-types: list all non-store types and exit
    if cli.list_non_store_types {
        visitor.list_non_store_types();
        return;
    }

    let output = cli.output.clone().unwrap_or_else(|| {
        let mut path = cli.source_code_dir.first().unwrap().clone();
        path.push_str(".schema.json");
        path
    });
    visitor.report_and_dump(output, cli.update);
}
