#![allow(dead_code)]

use std::collections::HashMap;

use proc_macro::TokenStream;
use syn::{parse::Parse, parse_macro_input, Attribute, Item};

#[derive(Clone, Debug, PartialEq, Eq)]
struct EnumNodeVariant {
    name: syn::Ident,
    attrs: Vec<Attribute>,
    node_name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct EnumNodeDef {
    visibility: syn::Visibility,
    attrs: Vec<Attribute>,
    name: syn::Ident,
    variants: Vec<EnumNodeDef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum StructNodeFieldData {
    Child { node_name: String },
    ChildList { node_name: String },
    Other { ty: syn::Type },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StructNodeField {
    visibility: syn::Visibility,
    attrs: Vec<Attribute>,
    name: syn::Ident,
    data: StructNodeFieldData,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StructNodeDef {
    visibility: syn::Visibility,
    attrs: Vec<Attribute>,
    name: syn::Ident,
    fields: Vec<StructNodeField>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TreeNodeDef {
    EnumNodeDef(EnumNodeDef),
    StructNodeDef(StructNodeDef),
}

impl TryFrom<&Item> for TreeNodeDef {
    type Error = syn::Error;
    fn try_from(_value: &Item) -> Result<Self, Self::Error> {
        todo!()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TreeDef {
    nodes: HashMap<syn::Ident, TreeNodeDef>,
    other_items: Vec<syn::Item>,
}

impl Parse for TreeDef {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut other_items: Vec<syn::Item> = Vec::new();
        let mut nodes: HashMap<syn::Ident, TreeNodeDef> = HashMap::new();

        // Something is a node if it is annotated with #[tree_node]
        let is_node = |item: &syn::Item| -> Option<syn::Ident> {
            match item {
                syn::Item::Struct(syn::ItemStruct { ident, attrs, .. })
                | syn::Item::Enum(syn::ItemEnum { ident, attrs, .. })
                    if attrs.iter().any(|attr| attr.path.is_ident("tree_node")) =>
                {
                    Some(ident.clone())
                }
                _ => None,
            }
        };

        // Parse a list of items, and filter out the ones which are nodes into their own
        // data structure.
        while !input.is_empty() {
            let item: syn::Item = input.parse()?;
            if let Some(node_name) = is_node(&item) {
                nodes.insert(node_name, TreeNodeDef::try_from(&item)?);
            } else {
                other_items.push(item);
            }
        }

        Ok(TreeDef { nodes, other_items })
    }
}

#[proc_macro]
pub fn define_tree(input: TokenStream) -> TokenStream {
    let _input = parse_macro_input!(input as TreeDef);
    todo!()
}
