//! Defines the structure of attributes that can appear on functions.

use std::{fmt, sync::OnceLock};

use derive_more::From;
use hash_ast::{ast, ast::AstNodeId};
use hash_source::{
    constant::{InternedFloat, InternedInt, InternedStr},
    identifier::Identifier,
};
use hash_storage::store::{DefaultPartialStore, PartialStore};
use hash_tir::params::ParamIndex;
use hash_utils::fxhash::FxHashMap;

#[derive(Debug, Clone)]
pub struct Attr {
    /// The name of the attribute.
    pub name: Identifier,

    /// The origin of the attribute.
    pub origin: AstNodeId,

    /// The kind of attribute that this is, either named, or with arguments.
    pub args: FxHashMap<AttrArgIdx, AttrValue>,
}

impl Attr {
    /// Create a new attribute without arguments.
    pub fn new(name: Identifier, origin: AstNodeId) -> Self {
        Self { name, origin, args: FxHashMap::default() }
    }

    /// Create a new attribute with arguments.
    pub fn with_args(
        name: Identifier,
        origin: AstNodeId,
        args: FxHashMap<AttrArgIdx, AttrValue>,
    ) -> Self {
        Self { name, origin, args }
    }

    /// Add an argument to the attribute.
    pub fn add_arg(&mut self, index: AttrArgIdx, value: AttrValue) {
        self.args.insert(index, value);
    }

    /// Get argument [AttrValueKind] by positional index.
    pub fn get_arg_value_at(&self, index: impl Into<AttrArgIdx>) -> Option<&AttrValueKind> {
        self.args.get(&index.into()).map(|arg| &arg.value)
    }

    /// Get an attribute value with the given [AttrArgIdx].
    pub fn get_arg(&self, index: impl Into<AttrArgIdx>) -> Option<&AttrValue> {
        self.args.get(&index.into())
    }
}

/// An index into an attribute's arguments. The index can either be
/// the name of the argument to the attribute, or just the positional
/// value of the supplied argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum AttrArgIdx {
    Name(Identifier),
    Position(u32),
}

impl From<ParamIndex> for AttrArgIdx {
    fn from(index: ParamIndex) -> Self {
        match index {
            ParamIndex::Name(name) => AttrArgIdx::Name(name),
            ParamIndex::Position(index) => AttrArgIdx::Position(index as u32),
        }
    }
}

impl fmt::Display for AttrArgIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AttrArgIdx::Name(name) => write!(f, "{name}"),
            AttrArgIdx::Position(pos) => write!(f, "{pos}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AttrValue {
    /// The origin (in source) of the attribute value.
    pub origin: AstNodeId,

    /// The kind of value that this attribute is.
    pub value: AttrValueKind,
}

impl fmt::Display for AttrValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            AttrValueKind::Str(value) => write!(f, "{}", value),
            AttrValueKind::Int(value) => write!(f, "{}", value),
            AttrValueKind::Float(value) => write!(f, "{}", value),
            AttrValueKind::Char(value) => write!(f, "'{}'", value),
        }
    }
}

/// A literal value, represented as a token stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttrValueKind {
    /// A string literal.
    Str(InternedStr),

    /// An integer constant.
    Int(InternedInt),

    /// A float constant.
    Float(InternedFloat),

    /// A char literal.
    Char(char),
}

impl AttrValueKind {
    /// Try to convert an [ast::Expr] into an [AttrValue].
    pub fn try_from_expr(expr: &ast::Expr) -> Option<Self> {
        match expr {
            ast::Expr::Lit(ast::LitExpr { data }) => match data.body() {
                ast::Lit::Str(ast::StrLit { data }) => Some(Self::Str(*data)),
                ast::Lit::Char(ast::CharLit { data }) => Some(Self::Char(*data)),
                ast::Lit::Int(ast::IntLit { value, .. }) => Some(Self::Int(*value)),
                ast::Lit::Float(ast::FloatLit { value, .. }) => Some(Self::Float(*value)),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn ty_name(&self) -> &'static str {
        match self {
            Self::Str(_) => "string",
            Self::Int(_) => "integer",
            Self::Float(_) => "float",
            Self::Char(_) => "character",
        }
    }

    /// Ensure that the [AttrValueKind] is a string value, and return it.
    pub fn as_str_value(&self) -> InternedStr {
        match self {
            Self::Str(value) => *value,
            value => panic!("value is not a string, but a {}", value.ty_name()),
        }
    }
}

/// A map of all of the attributes that exist on a particular [AstNodeId].
#[derive(Default, Debug, Clone)]
pub struct Attrs {
    /// The attributes that exist on this node.
    pub attrs: FxHashMap<Identifier, Attr>,
}

impl Attrs {
    /// Create a new empty set of attributes.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create an [Attrs] with a specific capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self { attrs: FxHashMap::with_capacity_and_hasher(capacity, Default::default()) }
    }

    /// Add an attribute to the set of attributes.
    pub fn add_attr(&mut self, attr: Attr) {
        self.attrs.insert(attr.name, attr);
    }

    /// Check whether an attribute exists on this node.
    pub fn has_attr(&self, id: Identifier) -> bool {
        self.attrs.contains_key(&id)
    }

    /// Get an attribute by name.
    pub fn get_attr(&self, id: Identifier) -> Option<&Attr> {
        self.attrs.get(&id)
    }
}

#[derive(Default)]
pub struct AttrStore(DefaultPartialStore<AstNodeId, Attrs>);

lazy_static! {
    static ref EMPTY_ATTR: Attrs = Attrs { attrs: FxHashMap::default() };
}

impl AttrStore {
    /// Insert a new set of attributes into the store.
    pub fn insert(&self, id: AstNodeId, attrs: Attrs) {
        self.0.insert(id, attrs);
    }

    /// Get the attributes of a particular [AstNodeId] or return
    /// an empty set of attributes.
    pub fn map_with_default<T>(&self, id: AstNodeId, f: impl FnOnce(&Attrs) -> T) -> T {
        self.0.map_fast(id, |attrs| f(attrs.unwrap_or(&EMPTY_ATTR)))
    }

    /// Check whether a particular [AstNodeId] has a specific
    /// attribute.
    pub fn node_has_attr(&self, id: AstNodeId, attr: Identifier) -> bool {
        self.0.borrow(id).map_or(false, |attrs| attrs.has_attr(attr))
    }

    /// Get an [Attr] by name, from a node.
    pub fn get_attr(&self, id: AstNodeId, attr: Identifier) -> Option<Attr> {
        self.0.borrow(id).and_then(|attrs| attrs.attrs.get(&attr).cloned())
    }
}

/// The global [`AttrStore`] instance.
static STORES: OnceLock<AttrStore> = OnceLock::new();

/// Access the global [`AttrStore`] instance.
#[inline]
pub fn attr_store() -> &'static AttrStore {
    STORES.get_or_init(AttrStore::default)
}
