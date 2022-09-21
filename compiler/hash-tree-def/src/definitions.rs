//! Data types for storing the parsed tree definition given to the
//! [`super::define_tree`] macro.

use std::collections::HashMap;

/// An enum node variant, which has to point to another struct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EnumNodeVariant {
    pub(crate) attrs: Vec<syn::Attribute>,
    pub(crate) name: syn::Ident,
    pub(crate) variant_struct_name: syn::Ident,
}

/// A node definition that is an enum, containing a set of variants with single
/// members.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EnumNodeDef {
    pub(crate) visibility: syn::Visibility,
    pub(crate) attrs: Vec<syn::Attribute>,
    pub(crate) name: syn::Ident,
    pub(crate) variants: Vec<EnumNodeVariant>,
}

/// The data type of a struct node field.
///
/// This is either another node, a list of nodes, or some other type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum StructNodeFieldData {
    Child { node_name: syn::Ident },
    ChildList { node_name: syn::Ident },
    Other { ty: syn::Type },
}

/// The field of a struct node definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StructNodeField {
    pub(crate) visibility: syn::Visibility,
    pub(crate) attrs: Vec<syn::Attribute>,
    pub(crate) name: syn::Ident,
    pub(crate) data: StructNodeFieldData,
}

/// A node definition that is a struct, containing a set of field members.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StructNodeDef {
    pub(crate) visibility: syn::Visibility,
    pub(crate) attrs: Vec<syn::Attribute>,
    pub(crate) name: syn::Ident,
    pub(crate) fields: Vec<StructNodeField>,
}

/// A node definition, which is either a struct or an enum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TreeNodeDef {
    EnumNodeDef(EnumNodeDef),
    StructNodeDef(StructNodeDef),
}

impl TreeNodeDef {
    /// Get the name of the node.
    pub(crate) fn name(&self) -> &syn::Ident {
        match self {
            TreeNodeDef::EnumNodeDef(def) => &def.name,
            TreeNodeDef::StructNodeDef(def) => &def.name,
        }
    }
}

/// The definition of a tree of nodes, as well as other items that might have
/// been defined alongside it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TreeDef {
    pub(crate) nodes: HashMap<syn::Ident, TreeNodeDef>,
    pub(crate) other_items: Vec<syn::Item>,
}
