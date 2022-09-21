//! Utilities for parsing the structures defined in [`super::definitions`] using
//! the [`syn`] crate.

use std::collections::HashMap;

use syn::{
    parse::Parse, spanned::Spanned, Attribute, Field, Item, ItemEnum, ItemStruct, Type, Variant,
};

use super::definitions::{
    EnumNodeDef, EnumNodeVariant, StructNodeDef, StructNodeField, StructNodeFieldData, TreeDef,
    TreeNodeDef,
};

const NODE_ATTR_NAME: &str = "tree_node";
const NODE_TYPE_NAME: &str = "Node";
const NODES_TYPE_NAME: &str = "Nodes";

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

/// Ensure that the given variant is in the form Foo(A) for some identifier A.
fn ensure_variant_single_nameless_ident_field(value: &Variant) -> Result<syn::Ident, syn::Error> {
    if value.fields.len() == 1 {
        let field = value.fields.iter().next().unwrap();
        if field.ident.is_none() {
            if let Type::Path(path) = &field.ty {
                if let Some(ident) = path.path.get_ident() {
                    return Ok(ident.clone());
                }
            }
        }
    }
    Err(syn::Error::new(
        value.span(),
        "Only nameless single-identifier-member variants are supported in enum node definitions",
    ))
}

impl TryFrom<&Variant> for EnumNodeVariant {
    type Error = syn::Error;
    fn try_from(value: &Variant) -> Result<Self, Self::Error> {
        let variant_struct_name = ensure_variant_single_nameless_ident_field(value)?;
        Ok(EnumNodeVariant {
            attrs: value.attrs.clone(),
            name: value.ident.clone(),
            variant_struct_name,
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

/// Ensure that the given path segments are in the form <A> for some type A,
/// returning the name of the type.
fn ensure_single_type_argument(segment: &syn::PathSegment) -> Result<syn::Ident, syn::Error> {
    if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
        if let Some(syn::GenericArgument::Type(Type::Path(path))) = args.args.first() {
            if let Some(ident) = path.path.get_ident() {
                return Ok(ident.clone());
            }
        }
    }
    Err(syn::Error::new(
        segment.arguments.span(),
        "A single type argument in the form of a single identifier is required here",
    ))
}

impl TryFrom<&Type> for StructNodeFieldData {
    type Error = syn::Error;
    fn try_from(value: &Type) -> Result<Self, Self::Error> {
        // Try to match a type in the form Node<A> or Nodes<A> for some identifier A,
        // and if so it is a child node(s).
        // Otherwise it is some other data.
        match value {
            Type::Path(type_path) => match type_path.path.segments.first() {
                Some(segment) if type_path.path.segments.len() == 1 => {
                    let ident = &segment.ident;
                    if ident == NODE_TYPE_NAME {
                        let node_name = ensure_single_type_argument(segment)?;
                        Ok(StructNodeFieldData::Child { node_name })
                    } else if ident == NODES_TYPE_NAME {
                        let node_name = ensure_single_type_argument(segment)?;
                        Ok(StructNodeFieldData::ChildList { node_name })
                    } else {
                        Ok(StructNodeFieldData::Other { ty: value.clone() })
                    }
                }
                _ => Ok(StructNodeFieldData::Other { ty: value.clone() }),
            },
            _ => Ok(StructNodeFieldData::Other { ty: value.clone() }),
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
                data: StructNodeFieldData::try_from(&value.ty)?,
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
        // Something is a node if it is annotated with #[tree_node]
        let has_tree_node =
            |attrs: &[Attribute]| attrs.iter().any(|attr| attr.path.is_ident(NODE_ATTR_NAME));

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

impl Parse for TreeDef {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut other_items: Vec<syn::Item> = Vec::new();
        let mut nodes: HashMap<syn::Ident, TreeNodeDef> = HashMap::new();

        // Parse a list of items, and filter out the ones which are nodes into their own
        // data structure.
        while !input.is_empty() {
            let item: syn::Item = input.parse()?;
            if let MaybeTreeNodeDef(Some(tree_node_def)) = MaybeTreeNodeDef::try_from(&item)? {
                nodes.insert(tree_node_def.name().clone(), tree_node_def);
            } else {
                other_items.push(item);
            }
        }

        Ok(TreeDef { nodes, other_items })
    }
}
