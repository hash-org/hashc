//! Defines the structure of attributes that can appear on functions.

use std::sync::OnceLock;

use hash_ast::{ast, ast::AstNodeId};
use hash_source::identifier::Identifier;
use hash_storage::store::DefaultPartialStore;
use hash_utils::fxhash::FxHashMap;

use crate::register::AttrId;

#[derive(Debug, Clone)]
pub struct Attr {
    /// The id of the attribute.
    id: AttrId,

    /// The kind of attribute that this is, either named, or with arguments.
    args: Option<FxHashMap<AttrArgIdx, AttrValue>>,
}

impl Attr {
    /// Create a new attribute without arguments.
    pub fn new(id: AttrId) -> Self {
        Self { id, args: None }
    }

    /// Create a new attribute with arguments.
    pub fn new_with_args(id: AttrId, args: FxHashMap<AttrArgIdx, AttrValue>) -> Self {
        Self { id, args: Some(args) }
    }

    /// Get an attribute value with the given [AttrArgIdx].
    pub fn get_arg(&self, index: AttrArgIdx) -> Option<&AttrValue> {
        self.args.as_ref()?.get(&index)
    }
}

/// An index into an attribute's arguments. The index can either be
/// the name of the argument to the attribute, or just the positional
/// value of the supplied argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AttrArgIdx {
    Named(Identifier),
    Positional(usize),
}

/// A literal value, represented as a token stream.
///
/// @@Future: replace this with a `hash-attrs` specific representation
/// for literals.
#[derive(Debug, Clone)]
pub struct AttrValue(ast::Lit);

/// A map of all of the attributes that exist on a particular [AstNodeId].
#[derive(Default, Debug, Clone)]
pub struct Attrs {
    /// The attributes that exist on this node.
    pub attrs: FxHashMap<AttrId, Attr>,
}

impl Attrs {
    /// Create a new empty set of attributes.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an attribute to the set of attributes.
    pub fn add_attr(&mut self, attr: Attr) {
        self.attrs.insert(attr.id, attr);
    }

    /// Check whether an attribute exists on this node.
    pub fn has_attr(&self, id: AttrId) -> bool {
        self.attrs.contains_key(&id)
    }
}

pub type AttrStore = DefaultPartialStore<AstNodeId, Attrs>;

/// The global [`AttrStore`] instance.
static STORES: OnceLock<AttrStore> = OnceLock::new();

/// Access the global [`AttrStore`] instance.
#[inline]
pub fn attr_store() -> &'static AttrStore {
    STORES.get_or_init(AttrStore::new)
}
use hash_storage::store::PartialCloneStore;
pub fn foo() {
    let store = attr_store();
    store.get(AstNodeId::new(0));
}
