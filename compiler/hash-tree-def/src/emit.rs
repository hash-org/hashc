//! Functions to emit tree definitions, visitors, walkers, given a parsed
//! [`TreeDef`].

use proc_macro2::TokenStream;
use quote::quote;

use crate::definitions::{
    EnumNodeDef, EnumNodeVariant, NodeFieldData, StructNodeDef, StructNodeField, TreeDef,
    TreeNodeDef, NODE_DEF_ATTR_NAME,
};

fn emit_other_items(def: &TreeDef) -> TokenStream {
    def.other_items.iter().map(|item| -> TokenStream { quote!(#item) }).collect()
}

fn emit_node_field_data(data: &NodeFieldData, tree_def: &TreeDef) -> TokenStream {
    match data {
        NodeFieldData::Child { node_name } => {
            let node_type_name = &tree_def.opts.node_type_name;
            quote!(#node_type_name<#node_name>)
        }
        NodeFieldData::ChildList { node_name } => {
            let nodes_type_name = &tree_def.opts.nodes_type_name;
            quote!(#nodes_type_name<#node_name>)
        }
        NodeFieldData::OptionalChild { node_name } => {
            let nodes_type_name = &tree_def.opts.nodes_type_name;
            quote!(Option<#nodes_type_name<#node_name>>)
        }
        NodeFieldData::Other { ty } => quote!(#ty),
    }
}

fn emit_struct_def(struct_def: &StructNodeDef, tree_def: &TreeDef) -> TokenStream {
    let rendered_fields = struct_def
        .fields
        .iter()
        .map(|field| {
            let field_data = emit_node_field_data(&field.data, tree_def);
            let StructNodeField { visibility, attrs, name, .. } = field;
            quote! {
                #(#attrs)*
                #visibility #name: #field_data
            }
        })
        .collect::<Vec<_>>();

    let StructNodeDef { visibility, attrs, name, .. } = struct_def;

    // Remove the #[tree_node] attribute
    let filtered_attrs = attrs.iter().filter(|attr| !attr.path.is_ident(NODE_DEF_ATTR_NAME));

    quote! {
        #(#filtered_attrs)*
        #visibility struct #name {
            #(#rendered_fields),*
        }
    }
}

fn emit_enum_def(enum_def: &EnumNodeDef, tree_def: &TreeDef) -> TokenStream {
    let rendered_variants = enum_def
        .variants
        .iter()
        .map(|variant| {
            let EnumNodeVariant { attrs, name, variant_data } = variant;
            variant_data
                .as_ref()
                .map(|variant_data| {
                    let data = variant_data.iter().map(|data| emit_node_field_data(data, tree_def));
                    quote! { #(#attrs)* #name(#(#data),*) }
                })
                .unwrap_or_else(|| {
                    quote! { #(#attrs)* #name }
                })
        })
        .collect::<Vec<_>>();

    let EnumNodeDef { visibility, attrs, name, .. } = enum_def;

    // Remove the #[tree_node] attribute
    let filtered_attrs = attrs.iter().filter(|attr| !attr.path.is_ident(NODE_DEF_ATTR_NAME));

    quote! {
        #(#filtered_attrs)*
        #visibility enum #name {
            #(#rendered_variants),*
        }
    }
}

fn emit_node_defs(def: &TreeDef) -> TokenStream {
    def.nodes
        .values()
        .map(|node| match node {
            TreeNodeDef::EnumNodeDef(enum_def) => emit_enum_def(enum_def, def),
            TreeNodeDef::StructNodeDef(struct_def) => emit_struct_def(struct_def, def),
        })
        .collect()
}

pub(crate) fn emit_tree(def: &TreeDef) -> Result<TokenStream, syn::Error> {
    // @@Todo: implement this
    Ok([emit_node_defs(def), emit_other_items(def)].into_iter().collect())
}
