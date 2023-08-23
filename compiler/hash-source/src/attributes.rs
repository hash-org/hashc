//! This defines the [ItemAttributes] structure which is used to store
//! arbitrary attributes on an item that are specified on the item in
//! the source. Item attributes are used to provide additional information
//! about any item, including labelling internal language items, calling
//! conventions, representations, etc.

use std::sync::LazyLock;

use hash_utils::{fxhash::FxHashMap, lazy_static::lazy_static, thin_vec::ThinVec};

use crate::identifier::{Identifier, IDENTS};

/// The [Attribute] structure represents a single attribute on an item.
/// Attributes are specified on items in the source code, and are used
/// to provide additional information about the item. These attributes
/// are computed from the parsed AST for items.
#[derive(Default, Debug, Clone)]
pub struct ItemAttributes {
    /// The inner attributes of the item.
    attributes: ThinVec<Attribute>,
}

impl ItemAttributes {
    /// Create a new [ItemAttributes] structure.
    pub fn new() -> Self {
        Self { attributes: ThinVec::new() }
    }

    /// Add an attribute to the item.
    pub fn add(&mut self, attribute: Attribute) {
        self.attributes.push(attribute);
    }

    /// Check if an attribute exists on the item.
    pub fn contains(&self, name: Identifier) -> bool {
        self.attributes.iter().any(|a| a.name == name)
    }

    /// Get the attributes of the item.
    pub fn attributes(&self) -> &[Attribute] {
        &self.attributes
    }

    /// Get the attributes of the item.
    pub fn attributes_mut(&mut self) -> &mut [Attribute] {
        &mut self.attributes
    }
}

/// A singular attribute with a name and an optional
/// value that is associated with the attribute.
#[derive(Debug, Clone)]
pub struct Attribute {
    /// The name of the attribute.
    name: Identifier,

    /// The value of the attribute. This is used to validate
    /// the specified attributes in the source.
    pub kind: AttributeKind,
}

impl Attribute {
    /// Create a new word [Attribute].
    pub fn word(name: Identifier) -> Self {
        Self { name, kind: AttributeKind::Word }
    }
}

/// Defines the kind of attribute that is being used.
///
/// @@Incomplete: This is currently incomplete, and will be
/// extended as the attribute system is extended.
#[derive(Debug, Clone)]
pub enum AttributeKind {
    /// Just the attribute itself
    Word,
}

lazy_static! {
    pub static ref BUILTIN_ATTRIBUTES: [Attribute; 1] =
        [Attribute { name: IDENTS.no_mangle, kind: AttributeKind::Word }];
}

pub static BUILTIN_ATTRIBUTE_MAP: LazyLock<FxHashMap<Identifier, &Attribute>> =
    LazyLock::new(|| {
        let mut map = FxHashMap::default();
        for attr in BUILTIN_ATTRIBUTES.iter() {
            if map.insert(attr.name, attr).is_some() {
                panic!("duplicate builtin attribute `{}`", attr.name);
            }
        }

        map
    });
