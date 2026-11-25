use super::SynVisitor;

fn rpc_struct_has_hex_error(item: syn::ItemStruct) -> bool {
    let mut visitor = SynVisitor::new(Vec::new(), None);
    visitor.in_rpc = true;
    visitor.current_file = "test/rpc/types.rs".to_string();
    visitor.inner_visit_item_struct(&item);
    visitor.has_error
}

fn rpc_enum_has_hex_error(item: syn::ItemEnum) -> bool {
    let mut visitor = SynVisitor::new(Vec::new(), None);
    visitor.in_rpc = true;
    visitor.current_file = "test/rpc/types.rs".to_string();
    visitor.inner_visit_item_enum(&item);
    visitor.has_error
}

#[test]
fn rpc_runtime_helper_does_not_require_hex_annotation() {
    assert!(!rpc_struct_has_hex_error(syn::parse_quote! {
        struct QuotaReservationGuard { reservation_id: u64 }
    }));
}

#[test]
fn namespaced_serde_derive_still_requires_hex_annotation() {
    assert!(rpc_struct_has_hex_error(syn::parse_quote! {
        #[derive(serde::Serialize)]
        struct RpcResponse { reservation_id: u64 }
    }));
}

#[test]
fn plain_serde_derive_still_requires_hex_annotation() {
    assert!(rpc_struct_has_hex_error(syn::parse_quote! {
        #[derive(Serialize, Deserialize)]
        struct RpcResponse { reservation_id: u64 }
    }));
}

#[test]
fn namespaced_serde_enum_derive_still_requires_hex_annotation() {
    assert!(rpc_enum_has_hex_error(syn::parse_quote! {
        #[derive(serde::Deserialize)]
        enum RpcResponse { Item { reservation_id: u64 } }
    }));
}

#[test]
fn serde_as_without_serde_derive_is_not_a_json_type() {
    assert!(!rpc_struct_has_hex_error(syn::parse_quote! {
        #[serde_as]
        struct InternalHelper { reservation_id: u64 }
    }));
}

#[test]
fn serde_skipped_runtime_field_does_not_require_hex_annotation() {
    assert!(!rpc_struct_has_hex_error(syn::parse_quote! {
        #[derive(Serialize)]
        struct RpcResponse {
            #[serde(skip)]
            reservation_id: u64,
        }
    }));
}
