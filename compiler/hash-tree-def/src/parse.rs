//! Utilities for parsing the structures defined in [`super::definitions`] using
//! the [`syn`] crate.

use std::collections::HashMap;

use proc_macro2::TokenStream;
use syn::{
    Attribute, Field, FieldsNamed, Ident, Item, ItemEnum, ItemMacro, ItemStruct, Path, Type,
    Variant, parse::Parse, spanned::Spanned,
};

use super::definitions::{
    EnumNodeDef, EnumNodeVariant, NODE_DEF_ATTR_NAME, NODE_TYPE_NAME, NODE_TYPE_NAME_OPTS_FIELD,
    NODES_TYPE_NAME_OPTS_FIELD, NodeFieldData, OPTS_MACRO_NAME, StructNodeDef, StructNodeField,
    TreeDef, TreeNodeDef,
};
use crate::definitions::{
    GET_REF_FROM_NODE_FUNCTION_BASE_NAME_OPTS_FIELD, NODES_TYPE_NAME, OPTIONAL_NODE_TYPE_NAME,
    REF_CHANGE_BODY_FUNCTION_BASE_NAME_OPTS_FIELD, ROOT_MODULE_OPTS_FIELD, TreeDefOpts,
    VISITOR_NODE_REF_BASE_TYPE_NAME_OPTS_FIELD, VISITOR_TRAIT_BASE_NAME_OPTS_FIELD,
};

/// Ensure that the given generics are empty, by returning an error otherwise.
///
/// Generics are not allowed in node definitions due to the complexity of
/// generating visitors and walkers for them.
fn ensure_generics_empty(generics: &syn::Generics) -> Result<(), syn::Error> {
    if generics.const_params().next().is_some()
        || generics.type_params().next().is_some()
        || generics.lifetimes().next().is_some()
    {
        Err(syn::Error::new(
            generics.span(),
            "Generics and lifetimes are not supported in node definitions",
        ))
    } else {
        Ok(())
    }
}

impl TryFrom<&Variant> for EnumNodeVariant {
    type Error = syn::Error;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        Ok(EnumNodeVariant {
            attrs: value.attrs.clone(),
            name: value.ident.clone(),
            variant_data: match &value.fields {
                syn::Fields::Named(_) => {
                    return Err(syn::Error::new(
                        value.span(),
                        "Named fields are not supported in enum node definitions",
                    ));
                }
                syn::Fields::Unnamed(fields) => Some(
                    fields
                        .unnamed
                        .iter()
                        .map(|field| NodeFieldData::try_from(&field.ty))
                        .collect::<Result<_, _>>()?,
                ),
                syn::Fields::Unit => None,
            },
        })
    }
}

impl TryFrom<&ItemEnum> for EnumNodeDef {
    type Error = syn::Error;
    fn try_from(value: &ItemEnum) -> Result<Self, Self::Error> {
        ensure_generics_empty(&value.generics)?;
        Ok(EnumNodeDef {
            visibility: value.vis.clone(),
            attrs: value.attrs.clone(),
            name: value.ident.clone(),
            variants: value
                .variants
                .iter()
                .map(EnumNodeVariant::try_from)
                .collect::<Result<_, _>>()?,
        })
    }
}

/// Ensure that the given token stream is in the form some identifier returning
/// the name of the identifier.
fn ensure_single_macro_ident_argument(tokens: TokenStream) -> Result<syn::Ident, syn::Error> {
    let token_span = tokens.span();
    syn::parse2::<syn::Ident>(tokens).map_err(|_| {
        syn::Error::new(
            token_span,
            "A single argument in the form of a type identifier is required here",
        )
    })
}

impl TryFrom<&Type> for NodeFieldData {
    type Error = syn::Error;
    fn try_from(value: &Type) -> Result<Self, Self::Error> {
        // Try to match a type in the form Child!(A)/Children!(A)/OptionalChild!(A) for
        // some identifier A, and if so it is a child node(s).
        // Otherwise it is some other data.
        match value {
            Type::Macro(type_macro) => {
                let node_name =
                    || ensure_single_macro_ident_argument(type_macro.mac.tokens.clone());
                if type_macro.mac.path.is_ident(NODE_TYPE_NAME) {
                    Ok(NodeFieldData::Child { node_name: node_name()? })
                } else if type_macro.mac.path.is_ident(NODES_TYPE_NAME) {
                    Ok(NodeFieldData::ChildList { node_name: node_name()? })
                } else if type_macro.mac.path.is_ident(OPTIONAL_NODE_TYPE_NAME) {
                    Ok(NodeFieldData::OptionalChild { node_name: node_name()? })
                } else {
                    Ok(NodeFieldData::Other { ty: Box::new(value.clone()) })
                }
            }
            _ => Ok(NodeFieldData::Other { ty: Box::new(value.clone()) }),
        }
    }
}

impl TryFrom<&Field> for StructNodeField {
    type Error = syn::Error;
    fn try_from(value: &Field) -> Result<Self, Self::Error> {
        match &value.ident {
            Some(ident) => Ok(StructNodeField {
                visibility: value.vis.clone(),
                attrs: value.attrs.clone(),
                name: ident.clone(),
                data: NodeFieldData::try_from(&value.ty)?,
            }),
            None => Err(syn::Error::new(value.span(), "Struct node fields must be named")),
        }
    }
}

impl TryFrom<&ItemStruct> for StructNodeDef {
    type Error = syn::Error;
    fn try_from(value: &ItemStruct) -> Result<Self, Self::Error> {
        ensure_generics_empty(&value.generics)?;
        Ok(StructNodeDef {
            visibility: value.vis.clone(),
            attrs: value.attrs.clone(),
            name: value.ident.clone(),
            fields: value.fields.iter().map(StructNodeField::try_from).collect::<Result<_, _>>()?,
        })
    }
}

/// Helper type so that we can implement [`TryFrom<&Item>`] for optional
/// [`TreeNodeDef`].
#[derive(Clone, Debug, PartialEq, Eq)]
struct MaybeTreeNodeDef(Option<TreeNodeDef>);

impl TryFrom<&Item> for MaybeTreeNodeDef {
    type Error = syn::Error;
    fn try_from(value: &Item) -> Result<Self, Self::Error> {
        // Something is a node if it is annotated with #[node]
        let has_tree_node =
            |attrs: &[Attribute]| attrs.iter().any(|attr| attr.path().is_ident(NODE_DEF_ATTR_NAME));

        match value {
            Item::Enum(enum_item) if has_tree_node(&enum_item.attrs) => Ok(MaybeTreeNodeDef(Some(
                TreeNodeDef::EnumNodeDef(EnumNodeDef::try_from(enum_item)?),
            ))),
            Item::Struct(struct_item) if has_tree_node(&struct_item.attrs) => Ok(MaybeTreeNodeDef(
                Some(TreeNodeDef::StructNodeDef(StructNodeDef::try_from(struct_item)?)),
            )),
            _ => Ok(MaybeTreeNodeDef(None)),
        }
    }
}

/// Parse a field in the form `ident_name: a::b::c::...` the path `a::b::c::...`
fn parse_path_field(fields: &FieldsNamed, field_name: &str) -> Result<Path, syn::Error> {
    fields
        .named
        .iter()
        .find_map(|field| {
            if let Some(ident) = &field.ident {
                if ident == field_name {
                    if let Type::Path(path) = &field.ty {
                        return Some(Ok(path.path.clone()));
                    }
                    return Some(Err(syn::Error::new(field.ty.span(), "Expected a path")));
                }
            }
            None
        })
        .unwrap_or_else(|| {
            Err(syn::Error::new(
                fields.named.span(),
                format!("Expected a field named `{field_name}`"),
            ))
        })
}

/// Parse a field in the form `ident_name: A` for some identifier A, returning
/// the identifier A.
fn parse_ident_field(fields: &FieldsNamed, field_name: &str) -> Result<Ident, syn::Error> {
    fields
        .named
        .iter()
        .find_map(|field| {
            if let Some(ident) = &field.ident {
                if ident == field_name {
                    if let Type::Path(path) = &field.ty {
                        if let Some(name) = path.path.get_ident() {
                            return Some(Ok(name.clone()));
                        }
                    }
                    return Some(Err(syn::Error::new(
                        field.ty.span(),
                        "Expected a type identifier",
                    )));
                }
            }
            None
        })
        .unwrap_or_else(|| {
            Err(syn::Error::new(
                fields.named.span(),
                format!("Expected a field named `{field_name}`"),
            ))
        })
}

/// Helper type so that we can implement [`TryFrom<&Item>`] for optional
/// [`TreeDefOpts`].
#[derive(Clone, Debug, PartialEq, Eq)]
struct MaybeTreeDefOpts(Option<TreeDefOpts>);

impl TryFrom<&Item> for MaybeTreeDefOpts {
    type Error = syn::Error;
    fn try_from(value: &Item) -> Result<Self, Self::Error> {
        // Options are given by a macro opts! { ... }
        match value {
            Item::Macro(ItemMacro { mac, .. }) if mac.path.is_ident(OPTS_MACRO_NAME) => {
                let opts = syn::parse2::<FieldsNamed>(mac.tokens.clone())?;

                // Parse each option:
                let node_type_name = parse_ident_field(&opts, NODE_TYPE_NAME_OPTS_FIELD)?;
                let nodes_type_name = parse_ident_field(&opts, NODES_TYPE_NAME_OPTS_FIELD)?;
                let visitor_trait_base_name =
                    parse_ident_field(&opts, VISITOR_TRAIT_BASE_NAME_OPTS_FIELD)?;
                let visitor_node_ref_base_type_name =
                    parse_ident_field(&opts, VISITOR_NODE_REF_BASE_TYPE_NAME_OPTS_FIELD)?;
                let get_ref_from_node_function_base_name =
                    parse_ident_field(&opts, GET_REF_FROM_NODE_FUNCTION_BASE_NAME_OPTS_FIELD)?;
                let ref_change_body_function_base_name =
                    parse_ident_field(&opts, REF_CHANGE_BODY_FUNCTION_BASE_NAME_OPTS_FIELD)?;
                let root_module = parse_path_field(&opts, ROOT_MODULE_OPTS_FIELD)?;

                Ok(MaybeTreeDefOpts(Some(TreeDefOpts {
                    node_type_name,
                    nodes_type_name,
                    visitor_node_ref_base_type_name,
                    visitor_trait_base_name,
                    get_ref_from_node_function_base_name,
                    ref_change_body_function_base_name,
                    root_module,
                })))
            }
            _ => Ok(MaybeTreeDefOpts(None)),
        }
    }
}

impl Parse for TreeDef {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut other_items: Vec<syn::Item> = Vec::new();
        let mut nodes: HashMap<syn::Ident, TreeNodeDef> = HashMap::new();
        let mut parsed_opts = None;

        // Parse a list of items, and filter out the ones which are nodes into their own
        // data structure.
        while !input.is_empty() {
            let item: syn::Item = input.parse()?;
            if let MaybeTreeDefOpts(Some(tree_def_opts)) = MaybeTreeDefOpts::try_from(&item)? {
                if parsed_opts.is_some() {
                    return Err(syn::Error::new(
                        item.span(),
                        format!("Only one {OPTS_MACRO_NAME}! macro invocation is allowed"),
                    ));
                }
                parsed_opts = Some(tree_def_opts);
            } else if let MaybeTreeNodeDef(Some(tree_node_def)) = MaybeTreeNodeDef::try_from(&item)?
            {
                nodes.insert(tree_node_def.name().clone(), tree_node_def);
            } else {
                other_items.push(item);
            }
        }

        match parsed_opts {
            Some(opts) => Ok(TreeDef { nodes, other_items, opts }),
            None => Err(syn::Error::new(
                input.span(),
                format!("Expected a {OPTS_MACRO_NAME}! macro invocation"),
            )),
        }
    }
}
