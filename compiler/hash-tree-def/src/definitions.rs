//! Data types for storing the parsed tree definition given to the
//! [`super::define_tree`] macro.

use std::collections::HashMap;

pub(crate) const NODE_DEF_ATTR_NAME: &str = "node";
pub(crate) const NODE_TYPE_NAME: &str = "Child";
pub(crate) const NODES_TYPE_NAME: &str = "Children";
pub(crate) const OPTIONAL_NODE_TYPE_NAME: &str = "OptionalChild";

pub(crate) const OPTS_MACRO_NAME: &str = "opts";
pub(crate) const NODE_TYPE_NAME_OPTS_FIELD: &str = "node_type_name";
pub(crate) const NODES_TYPE_NAME_OPTS_FIELD: &str = "nodes_type_name";
pub(crate) const VISITOR_TRAIT_BASE_NAME_OPTS_FIELD: &str = "visitor_trait_base_name";
pub(crate) const VISITOR_NODE_REF_BASE_TYPE_NAME_OPTS_FIELD: &str =
    "visitor_node_ref_base_type_name";
pub(crate) const GET_REF_FROM_NODE_FUNCTION_BASE_NAME_OPTS_FIELD: &str =
    "get_ref_from_node_function_base_name";
pub(crate) const REF_CHANGE_BODY_FUNCTION_BASE_NAME_OPTS_FIELD: &str =
    "ref_change_body_function_base_name";

/// An enum node variant, which has to point to another struct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EnumNodeVariant {
    pub(crate) attrs: Vec<syn::Attribute>,
    pub(crate) name: syn::Ident,
    pub(crate) variant_data: Option<Vec<NodeFieldData>>,
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

/// The data type of a node field.
///
/// This is either another node, a list of nodes, an optional node, or some
/// other type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NodeFieldData {
    Child { node_name: syn::Ident },
    ChildList { node_name: syn::Ident },
    OptionalChild { node_name: syn::Ident },
    Other { ty: syn::Type },
}

impl NodeFieldData {
    #[allow(unused)]
    pub(crate) fn node_name(&self) -> Option<&syn::Ident> {
        match self {
            NodeFieldData::Child { node_name } => Some(node_name),
            NodeFieldData::ChildList { node_name } => Some(node_name),
            NodeFieldData::OptionalChild { node_name } => Some(node_name),
            NodeFieldData::Other { .. } => None,
        }
    }
}

/// The field of a struct node definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StructNodeField {
    pub(crate) visibility: syn::Visibility,
    pub(crate) attrs: Vec<syn::Attribute>,
    pub(crate) name: syn::Ident,
    pub(crate) data: NodeFieldData,
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

/// A set of auxiliary options given to the tree definition macro.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TreeDefOpts {
    /// The type name of the tree node wrapper type. This type must take a
    /// single type argument.
    pub(crate) node_type_name: syn::Ident,
    /// The type name of the tree node list wrapper type. This type must take a
    /// single type argument.
    pub(crate) nodes_type_name: syn::Ident,
    /// The base name to use for the created visitor
    pub(crate) visitor_trait_base_name: syn::Ident,
    /// The base name to use for the created visitor's node reference types
    pub(crate) visitor_node_ref_base_type_name: syn::Ident,
    pub(crate) get_ref_from_node_function_base_name: syn::Ident,
    pub(crate) ref_change_body_function_base_name: syn::Ident,
}

/// The definition of a tree of nodes, as well as other items that might have
/// been defined alongside it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TreeDef {
    pub(crate) nodes: HashMap<syn::Ident, TreeNodeDef>,
    pub(crate) other_items: Vec<syn::Item>,
    pub(crate) opts: TreeDefOpts,
}
