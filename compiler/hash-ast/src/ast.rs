//! Frontend-agnostic Hash AST (abstract syntax tree) type definitions.

use std::{
    fmt::Display,
    hash::Hash,
    ops::{Deref, DerefMut},
    path::PathBuf,
};

use hash_source::{
    constant::{InternedFloat, InternedInt, InternedStr},
    identifier::Identifier,
    location::Span,
};
use hash_tree_def::define_tree;
use hash_utils::counter;
use num_bigint::BigInt;
use replace_with::replace_with_or_abort;

counter! {
    name: AstNodeId,
    counter_name: AST_NODE_ID_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

/// Represents an abstract syntax tree node.
///
/// Contains an inner type, as well as begin and end positions in the input.
#[derive(Debug, Clone)]
pub struct AstNode<T> {
    /// The stored data within this node
    body: Box<T>,
    /// Associated [Span] with this node
    span: Span,
    /// Associated `id` with this [AstNode<T>]
    id: AstNodeId,
}

impl<T> PartialEq for AstNode<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T> AstNode<T> {
    /// Create a new node with a given body and location.
    pub fn new(body: T, span: Span) -> Self {
        Self { body: Box::new(body), span, id: AstNodeId::new() }
    }

    /// Get a reference to the body contained within this node.
    pub fn body(&self) -> &T {
        self.body.as_ref()
    }

    /// Convert the [AstNode<T>] into it's body.
    pub fn into_body(self) -> T {
        *self.body
    }

    /// Get a mutable reference to the body.
    pub fn body_mut(&mut self) -> &mut T {
        self.body.as_mut()
    }

    /// Get the [Span] of this [AstNode].
    pub fn span(&self) -> Span {
        self.span
    }

    /// Set the [Span] of this [AstNode].
    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }

    /// Get the [AstNodeId] of this node.
    pub fn id(&self) -> AstNodeId {
        self.id
    }

    /// Create an [AstNodeRef] from this [AstNode].
    pub fn ast_ref(&self) -> AstNodeRef<T> {
        AstNodeRef { body: self.body.as_ref(), span: self.span, id: self.id }
    }

    /// Create an [AstNodeRefMut] from this [AstNode].
    pub fn ast_ref_mut(&mut self) -> AstNodeRefMut<T> {
        AstNodeRefMut { body: self.body.as_mut(), span: self.span, id: self.id }
    }

    /// Create an [AstNodeRef] by providing a body and copying over the
    /// [Span] and [AstNodeId] that belong to this [AstNode].
    pub fn with_body<'u, U>(&self, body: &'u U) -> AstNodeRef<'u, U> {
        AstNodeRef { body, span: self.span, id: self.id }
    }
}

#[derive(Debug)]
pub struct AstNodeRef<'t, T> {
    /// A reference to the body of the [AstNode].
    body: &'t T,
    /// The [Span] of the node.
    span: Span,
    /// The [AstNodeId] of the node, representing a unique identifier within
    /// the AST, useful for performing fast comparisons of trees.
    id: AstNodeId,
}

impl<T> Clone for AstNodeRef<'_, T> {
    fn clone(&self) -> Self {
        Self { body: self.body, span: self.span, id: self.id }
    }
}

impl<T> Copy for AstNodeRef<'_, T> {}

impl<'t, T> AstNodeRef<'t, T> {
    /// Create a new [AstNodeRef<T>].
    pub fn new(body: &'t T, span: Span, id: AstNodeId) -> Self {
        AstNodeRef { body, span, id }
    }

    /// Get a reference to body of the [AstNodeRef].
    pub fn body(&self) -> &T {
        self.body
    }

    /// Utility function to copy over the [Span] and [AstNodeId] from
    /// another [AstNodeRef] with a provided body.
    pub fn with_body<'u, U>(&self, body: &'u U) -> AstNodeRef<'u, U> {
        AstNodeRef { body, span: self.span, id: self.id }
    }

    /// Get the [Span] of this [AstNodeRef].
    pub fn span(&self) -> Span {
        self.span
    }

    /// Get the [AstNodeId] of this [AstNodeRef].
    pub fn id(&self) -> AstNodeId {
        self.id
    }
}

/// [AstNode] dereferences to its inner `body` type.
impl<T> Deref for AstNodeRef<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.body()
    }
}

#[derive(Debug)]
pub struct AstNodeRefMut<'t, T> {
    /// A mutable reference to the body of the [AstNode].
    body: &'t mut T,
    /// The [Span] of the [AstNode].
    pub span: Span,
    /// The [AstNodeId] of the [AstNode], representing a unique identifier
    /// within the AST, useful for performing fast comparisons of trees.
    pub id: AstNodeId,
}

impl<'t, T> AstNodeRefMut<'t, T> {
    /// Create a new [AstNodeRefMut<T>].
    pub fn new(body: &'t mut T, span: Span, id: AstNodeId) -> Self {
        AstNodeRefMut { body, span, id }
    }

    /// Get a reference to body of the [AstNodeRefMut].
    pub fn body(&self) -> &T {
        self.body
    }

    /// Replace the body of the [AstNodeRefMut] with another body.
    pub fn replace(&mut self, f: impl FnOnce(T) -> T) {
        replace_with_or_abort(self.body, f);
    }

    /// Get a mutable reference to the body.
    pub fn body_mut(&mut self) -> &mut T {
        self.body
    }

    /// Get the [Span] of this [AstNodeRefMut].
    pub fn span(&self) -> Span {
        self.span
    }

    /// Get the [AstNodeId] of this [AstNodeRefMut].
    pub fn id(&self) -> AstNodeId {
        self.id
    }
}

impl<T> Deref for AstNodeRefMut<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.body()
    }
}

impl<T> DerefMut for AstNodeRefMut<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.body
    }
}

/// Helper trait to access a node from a structure that contains one.
pub trait OwnsAstNode<T> {
    /// Get a reference to [AstNode<T>].
    fn node(&self) -> &AstNode<T>;

    /// Get a mutable reference to [AstNode<T>].
    fn node_mut(&mut self) -> &mut AstNode<T>;

    /// Get a [AstNodeRef<T>].
    fn node_ref(&self) -> AstNodeRef<T> {
        self.node().ast_ref()
    }

    /// Get a [AstNodeRefMut<T>].
    fn node_ref_mut(&mut self) -> AstNodeRefMut<T> {
        self.node_mut().ast_ref_mut()
    }
}

/// A collection of [AstNode]s with an optional shared
/// span. This is often used to represent collections
/// of [AstNode]s when they are wrapped within some kind
/// of delimiter.
#[derive(Debug, PartialEq, Clone)]
pub struct AstNodes<T> {
    /// The nodes that the [AstNodes] holds.
    pub nodes: Vec<AstNode<T>>,
    /// The span of the AST nodes if one is available.
    pub span: Option<Span>,
}

#[macro_export]
macro_rules! ast_nodes {
    ($($item:expr),*) => {
        $crate::ast::AstNodes::new(vec![$($item,)*], None)
    };
    ($($item:expr,)*) => {
        $crate::ast::AstNodes::new(vec![$($item,)*], None)
    };
}

impl<T> AstNodes<T> {
    pub fn empty() -> Self {
        Self { nodes: vec![], span: None }
    }

    pub fn new(nodes: Vec<AstNode<T>>, span: Option<Span>) -> Self {
        Self { nodes, span }
    }

    /// Function to adjust the span location of [AstNodes] if it is initially
    /// incorrectly offset because there is a 'pre-conditional' token that must
    /// be parsed before parsing the nodes. This token could be something like a
    /// '<' or '(' which starts a tuple, or type bound
    pub fn set_span(&mut self, span: Span) {
        self.span = Some(span);
    }

    pub fn span(&self) -> Option<Span> {
        self.span.or_else(|| Some(self.nodes.first()?.span().join(self.nodes.last()?.span())))
    }

    pub fn ast_ref_iter(&self) -> impl Iterator<Item = AstNodeRef<T>> {
        self.nodes.iter().map(|x| x.ast_ref())
    }
}

impl<T> Deref for AstNodes<T> {
    type Target = [AstNode<T>];
    fn deref(&self) -> &Self::Target {
        &self.nodes
    }
}
impl<T> DerefMut for AstNodes<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.nodes
    }
}

/// [AstNode] dereferences to its inner `body` type.
impl<T> Deref for AstNode<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.body()
    }
}

/// [AstNode] dereferences to its inner `body` type.
impl<T> DerefMut for AstNode<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.body_mut()
    }
}

define_tree! {
    opts! {{
        node_type_name: AstNode,
        nodes_type_name: AstNodes,
        visitor_trait_base_name: AstVisitor,
        visitor_node_ref_base_type_name: AstNodeRef,
        get_ref_from_node_function_base_name: ast_ref,
        ref_change_body_function_base_name: with_body,
    }}

    /// A single name/symbol.
    #[derive(Hash, Debug, Clone, Copy, PartialEq, Eq)]
    #[node]
    pub struct Name {
        // The name of the symbol.
        pub ident: Identifier,
    }

    impl Name {
        /// Function to check whether a [Name] has a particular associated name with
        /// it.
        pub fn is(&self, other: impl Into<Identifier>) -> bool {
            self.ident == other.into()
        }
    }

    /// A concrete/"named" type.
    #[derive(Debug, PartialEq, Clone)]
    pub struct NamedTy {
        /// The name of the type.
        pub name: AstNode<Name>,
    }

    /// Access type denotes the access of a property of some inner type.
    #[derive(Debug, PartialEq, Clone)]
    pub struct AccessTy {
        /// The subject of the access
        pub subject: AstNode<Ty>,
        /// the property that is access of the `subject` type
        pub property: AstNode<Name>,
    }

    /// Reference kind representing either a raw reference or a normal reference.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum RefKind {
        /// Raw reference type
        Raw,
        /// Normal reference type
        Normal,
    }

    /// A reference type.
    #[derive(Debug, PartialEq, Clone)]
    pub struct RefTy {
        /// Inner type of the reference type
        pub inner: AstNode<Ty>,
        /// Whether this reference is a `raw` reference or normal reference (normal
        /// by default).
        pub kind: Option<AstNode<RefKind>>,
        /// Mutability of the reference (immutable by default)
        pub mutability: Option<AstNode<Mutability>>,
    }

    /// A type argument `<T: u32>`
    #[derive(Debug, PartialEq, Clone)]
    pub struct TyArg {
        /// An optional name to the argument
        pub name: Option<AstNode<Name>>,
        /// The assigned value of the type argument
        pub ty: AstNode<Ty>,
    }

    /// The tuple type.
    #[derive(Debug, PartialEq, Clone)]
    pub struct TupleTy {
        /// inner types of the tuple type
        pub entries: AstNodes<TyArg>,
    }

    /// The list type, , e.g. `{str}`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct ListTy {
        /// Inner type of the list
        pub inner: AstNode<Ty>,
    }

    /// The set type, , e.g. `{str}`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct SetTy {
        /// Inner type of the set
        pub inner: AstNode<Ty>,
    }

    /// The map type, e.g. `{str: u32}`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct MapTy {
        /// The `key` type of the map type
        pub key: AstNode<Ty>,
        /// The `value` type of the map type
        pub value: AstNode<Ty>,
    }

    /// The function type.
    #[derive(Debug, PartialEq, Clone)]
    pub struct FnTy {
        /// Any defined parameters for the function type
        pub params: AstNodes<TyArg>,
        /// Optional return type
        pub return_ty: AstNode<Ty>,
    }

    /// A type function e.g. `<T = u32, E: Conv ~ Eq> -> Result<T, E>`
    #[derive(Debug, PartialEq, Clone)]
    pub struct TyFn {
        /// The parameters of the type function
        pub params: AstNodes<Param>,
        /// Return type of the function
        pub return_ty: AstNode<Ty>,
    }

    /// A type function call specifies a call to a type function with the specified
    /// function name in the form of a [Ty] (which can only be a [NamedTy] then
    /// followed by arguments. For example: `Conv<u32>` or `(Foo<bar>)<baz>`
    #[derive(Debug, PartialEq, Clone)]
    pub struct TyFnCall {
        /// The subject of the type function call
        pub subject: AstNode<Expr>,
        /// Arguments that are applied to the type function call
        pub args: AstNodes<TyArg>,
    }

    /// A merge type meaning that multiple types are considered to be
    /// specified in place of one, e.g. `Conv ~ Eq`
    #[derive(Debug, PartialEq, Clone)]
    pub struct MergeTy {
        /// left hand-side of the merge type
        pub lhs: AstNode<Ty>,
        /// right hand-side of the merge type
        pub rhs: AstNode<Ty>,
    }

    /// A union type meaning that multiple types are accepted, e.g. `f64 | i64`
    #[derive(Debug, PartialEq, Clone)]
    pub struct UnionTy {
        /// left hand-side of the union type
        pub lhs: AstNode<Ty>,
        /// right hand-side of the union type
        pub rhs: AstNode<Ty>,
    }

    /// Binary type operators enumeration.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum BinTyOp {
        /// The union of two types, essentially an or, e.g `f64 | u64`
        Union,
        /// The intersection between two types, essentially an `and`, `Ord ~ Eq`
        Merge,
    }

    impl BinTyOp {
        /// Compute the precedence for an operator
        pub fn infix_binding_power(&self) -> (u8, u8) {
            match self {
                BinTyOp::Merge => (2, 3),
                BinTyOp::Union => (4, 5),
            }
        }
    }

    /// A type.
    #[derive(Debug, PartialEq, Clone)]
    pub enum Ty {
        /// Access type, access the property of some inner type
        Access(AccessTy),
        /// Tuple type
        Tuple(TupleTy),
        /// list type
        List(ListTy),
        /// Set type
        Set(SetTy),
        /// Map type
        Map(MapTy),
        /// Function type
        Fn(FnTy),
        /// Named type, similar to a binding
        Named(NamedTy),
        /// Reference type, the reference type of the inner type
        Ref(RefTy),
        /// Merge type, the intersection of two types
        Merge(MergeTy),
        /// Union type, the union of two types
        Union(UnionTy),
        /// Type function type
        TyFn(TyFn),
        /// Type function call
        TyFnCall(TyFnCall),
    }

    /// A set literal, e.g. `{1, 2, 3}`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct SetLit {
        /// The elements of the set literal.
        pub elements: AstNodes<Expr>,
    }

    /// A list literal, e.g. `[1, 2, 3]`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct ListLit {
        /// The elements of the list literal.
        pub elements: AstNodes<Expr>,
    }

    /// An entry within a tuple type, which may contain an optional name
    /// annotation and or a type annotation, for example:
    ///
    /// ```text
    /// (foo : u32 = 2, ..., k = 2)
    ///  ^^^   ^^^   ^
    /// name   type  value
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    pub struct TupleLitEntry {
        /// If the entry has a bounded name
        pub name: Option<AstNode<Name>>,
        /// Optional type annotation on the tuple entry
        pub ty: Option<AstNode<Ty>>,
        /// Value of the tuple literal entry
        pub value: AstNode<Expr>,
    }

    /// A tuple literal, e.g. `(1, 'A', "foo")`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct TupleLit {
        /// The elements of the tuple literal.
        pub elements: AstNodes<TupleLitEntry>,
    }

    /// A map literal entry, e.g. `"foo": 1`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct MapLitEntry {
        /// The key of the map entry
        pub key: AstNode<Expr>,
        /// The value of the map entry
        pub value: AstNode<Expr>,
    }

    /// A map literal, e.g. `{"foo": 1, "bar": 2}`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct MapLit {
        /// The elements of the map literal (key-value pairs).
        pub elements: AstNodes<MapLitEntry>,
    }

    /// A string literal.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct StrLit(pub InternedStr);

    /// A character literal.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct CharLit(pub char);

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum IntTy {
        I8,
        I16,
        I32,
        I64,
        I128,
        ISize,
        IBig,
        U8,
        U16,
        U32,
        U64,
        U128,
        USize,
        UBig,
    }

    impl IntTy {
        /// Check if the variant is signed or not.
        #[inline]
        pub fn is_signed(&self) -> bool {
            matches!(
                self,
                IntTy::I8
                    | IntTy::I16
                    | IntTy::I32
                    | IntTy::I64
                    | IntTy::I128
                    | IntTy::ISize
                    | IntTy::IBig
            )
        }

        /// Check if the variant is unsigned.
        #[inline]
        pub fn is_unsigned(&self) -> bool {
            !self.is_signed()
        }

        /// Get the size of [IntTy] in bytes. Returns [None] for
        /// [IntTy::IBig] and [IntTy::UBig] variants
        pub const fn size(&self) -> Option<u64> {
            match self {
                IntTy::I8 | IntTy::U8 => Some(1),
                IntTy::I16 | IntTy::U16 => Some(2),
                IntTy::I32 | IntTy::U32 => Some(4),
                IntTy::I64 | IntTy::U64 => Some(8),
                IntTy::I128 | IntTy::U128 => Some(16),
                // @@Todo: actually get the target pointer size, don't default to 64bit pointers.
                IntTy::ISize | IntTy::USize => Some(8),
                IntTy::IBig | IntTy::UBig => None,
            }
        }

        /// Function to get the largest possible integer represented within this
        /// type. For sizes `ibig` and `ubig` there is no defined max and so the
        /// function returns [None].
        pub fn max(&self) -> Option<BigInt> {
            match self {
                IntTy::I8 => Some(BigInt::from(i8::MAX)),
                IntTy::I16 => Some(BigInt::from(i16::MAX)),
                IntTy::I32 => Some(BigInt::from(i32::MAX)),
                IntTy::I64 => Some(BigInt::from(i64::MAX)),
                IntTy::I128 => Some(BigInt::from(i128::MAX)),
                IntTy::ISize => Some(BigInt::from(isize::MAX)),
                IntTy::U8 => Some(BigInt::from(u8::MAX)),
                IntTy::U16 => Some(BigInt::from(u16::MAX)),
                IntTy::U32 => Some(BigInt::from(u32::MAX)),
                IntTy::U64 => Some(BigInt::from(u64::MAX)),
                IntTy::U128 => Some(BigInt::from(u128::MAX)),
                IntTy::USize => Some(BigInt::from(usize::MAX)),
                IntTy::IBig | IntTy::UBig => None,
            }
        }

        /// Function to get the most minimum integer represented within this
        /// type. For sizes `ibig` and `ubig` there is no defined minimum and so the
        /// function returns [None].
        pub fn min(&self) -> Option<BigInt> {
            match self {
                IntTy::I8 => Some(BigInt::from(i8::MIN)),
                IntTy::I16 => Some(BigInt::from(i16::MIN)),
                IntTy::I32 => Some(BigInt::from(i32::MIN)),
                IntTy::I64 => Some(BigInt::from(i64::MIN)),
                IntTy::I128 => Some(BigInt::from(i128::MIN)),
                IntTy::ISize => Some(BigInt::from(isize::MIN)),
                IntTy::U8 => Some(BigInt::from(u8::MIN)),
                IntTy::U16 => Some(BigInt::from(u16::MIN)),
                IntTy::U32 => Some(BigInt::from(u32::MIN)),
                IntTy::U64 => Some(BigInt::from(u64::MIN)),
                IntTy::U128 => Some(BigInt::from(u128::MIN)),
                IntTy::USize => Some(BigInt::from(usize::MIN)),
                IntTy::IBig | IntTy::UBig => None,
            }
        }

        /// Convert the [IntTy] into a primitive type name
        pub fn to_name(&self) -> &'static str {
            match self {
                IntTy::I8 => "i8",
                IntTy::I16 => "i16",
                IntTy::I32 => "i32",
                IntTy::I64 => "i64",
                IntTy::I128 => "i128",
                IntTy::ISize => "isize",
                IntTy::IBig => "ibig",
                IntTy::U8 => "u8",
                IntTy::U16 => "u16",
                IntTy::U32 => "u32",
                IntTy::U64 => "u64",
                IntTy::U128 => "u128",
                IntTy::USize => "usize",
                IntTy::UBig => "ubig",
            }
        }
    }

    impl Display for IntTy {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.to_name())
        }
    }

    /// The type of the float the [IntLit] is storing.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum IntLitKind {
        /// integer kind `i128`, `u32` ,`i8`...
        Suffixed(IntTy),
        /// No provided suffix type, so defaults to `i32`
        Unsuffixed,
    }

    impl Display for IntLitKind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                IntLitKind::Suffixed(ty) => write!(f, "{ty}"),
                IntLitKind::Unsuffixed => write!(f, ""),
            }
        }
    }

    /// An integer literal.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct IntLit {
        /// The raw value of the literal
        pub value: InternedInt,
        /// Whether the literal has an ascription
        pub kind: IntLitKind,
    }

    /// The type of the float the [FloatLit] is storing.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum FloatTy {
        F32,
        F64,
    }

    impl Display for FloatTy {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                FloatTy::F32 => write!(f, "f32"),
                FloatTy::F64 => write!(f, "f64"),
            }
        }
    }

    /// The kind of ascription that is applied to the [FloatLit].
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum FloatLitKind {
        /// Has a provided user suffix type
        Suffixed(FloatTy),
        /// No provided suffix type, so defaults to `f32`
        Unsuffixed,
    }

    impl Display for FloatLitKind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                FloatLitKind::Suffixed(ty) => write!(f, "{ty}"),
                FloatLitKind::Unsuffixed => write!(f, ""),
            }
        }
    }

    /// A float literal.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct FloatLit {
        /// Raw value of the literal
        pub value: InternedFloat,
        /// Whether the literal has an ascription
        pub kind: FloatLitKind,
    }

    /// A boolean literal.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct BoolLit(pub bool);

    /// A literal.
    #[derive(Debug, PartialEq, Clone)]
    pub enum Lit {
        /// String literals, e.g. `"Viktor"`
        Str(StrLit),
        /// Character literals, e.g. `'c'`
        Char(CharLit),
        /// Integer literals, e.g. `5i32`
        Int(IntLit),
        /// Float literals, e.g. `27.4`
        Float(FloatLit),
        /// Boolean literals e.g. `false`
        Bool(BoolLit),
        /// Map literals, e.g. `set! { 3, 4 }`
        Set(SetLit),
        /// Map literals, e.g. `map! { x: 3, y: 4 }`
        Map(MapLit),
        /// List literals, e.g. `[1, 2, x + 4]`
        List(ListLit),
        /// Tuple literals, e.g. `(1, a, 3)`
        Tuple(TupleLit),
    }

    impl Lit {
        /// This function is used to determine if the current literal tree only
        /// contains constants. Constants are other literals that are not subject
        /// to change, e.g. a number like `5` or a string `hello`. This function
        /// implements short circuiting behaviour and thus should check if the
        /// literal is constant in the minimal time possible.
        pub fn is_constant(&self) -> bool {
            let is_expr_lit_and_const = |expr: &AstNode<Expr>| -> bool {
                match expr.kind() {
                    ExprKind::LitExpr(LitExpr(lit)) => lit.is_constant(),
                    _ => false,
                }
            };

            // Recurse over the literals for `set`, `map` and `tuple to see if they are
            // constant.
            match self {
                Lit::List(ListLit { elements }) | Lit::Set(SetLit { elements }) => {
                    !elements.iter().any(|expr| !is_expr_lit_and_const(expr))
                }
                Lit::Tuple(TupleLit { elements }) => {
                    !elements.iter().any(|entry| !is_expr_lit_and_const(&entry.body().value))
                }
                Lit::Map(MapLit { elements }) => !elements.iter().any(|entry| {
                    !is_expr_lit_and_const(&entry.body().key)
                        || !is_expr_lit_and_const(&entry.body().value)
                }),
                _ => true,
            }
        }
    }

    /// An alternative pattern, e.g. `Red | Blue`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct OrPat {
        /// The variants of the "or" pattern
        pub variants: AstNodes<Pat>,
    }

    /// A conditional pattern, e.g. `x if x == 42`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct IfPat {
        /// The pattern part of the conditional.
        pub pat: AstNode<Pat>,
        /// The expression part of the conditional.
        pub condition: AstNode<Expr>,
    }

    /// An construct pattern, e.g. `Some((x, y)), animals::Dog(name = "viktor", age
    /// = 3)`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct ConstructorPat {
        /// The subject of the constructor pattern.
        pub subject: AstNode<Pat>,
        /// The arguments of the constructor pattern.
        pub fields: AstNodes<TuplePatEntry>,
    }

    /// A module pattern entry, e.g. `{..., name as (fst, snd), ...}`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct ModulePatEntry {
        /// The name of the field.
        pub name: AstNode<Name>,
        /// The pattern to match the field's value with.
        pub pat: AstNode<Pat>,
    }

    /// A module pattern, e.g. `{ fgets, fputs, }`
    #[derive(Debug, PartialEq, Clone)]
    pub struct ModulePat {
        /// The entries of a module pattern
        pub fields: AstNodes<ModulePatEntry>,
    }

    /// A tuple pattern entry
    #[derive(Debug, PartialEq, Clone)]
    pub struct TuplePatEntry {
        /// If the tuple pattern entry binds a name to the pattern
        pub name: Option<AstNode<Name>>,
        /// The pattern that is being applied on the tuple entry
        pub pat: AstNode<Pat>,
    }

    /// A tuple pattern, e.g. `(1, 2, x)`
    #[derive(Debug, PartialEq, Clone)]
    pub struct TuplePat {
        /// The element of the tuple, as patterns.
        pub fields: AstNodes<TuplePatEntry>,
    }

    impl TuplePat {
        /// Function used to check if the pattern is nameless or not. If the pattern
        /// has at least one member that contains a `name` field, then it is
        /// considered to be named.
        pub fn is_nameless_pat(&self) -> bool {
            !self.fields.iter().any(|pat| pat.body().name.is_some())
        }
    }

    /// A list pattern, e.g. `[x, 1, ..]`
    #[derive(Debug, PartialEq, Clone)]
    pub struct ListPat {
        /// The element of the tuple, as patterns.
        pub fields: AstNodes<Pat>,
    }

    /// A literal pattern, limited to strings, character, floats, and integers, e.g.
    /// `3`, `c`
    #[derive(Debug, PartialEq, Clone)]
    pub struct LitPat(pub AstNode<Lit>);
    /// An access pattern, denoting the access of a property from
    /// another pattern.
    #[derive(Debug, PartialEq, Clone)]
    pub struct AccessPat {
        /// The subject of the access pattern
        pub subject: AstNode<Pat>,
        /// The property of the subject to access.
        pub property: AstNode<Name>,
    }

    /// A pattern name binding.
    #[derive(Debug, PartialEq, Clone)]
    pub struct BindingPat {
        /// The identifier that the name bind is using
        pub name: AstNode<Name>,
        /// Visibility of the binding (`priv` by default)
        pub visibility: Option<AstNode<Visibility>>,
        /// Mutability of the binding (immutable by default)
        pub mutability: Option<AstNode<Mutability>>,
    }

    /// A pattern spread
    #[derive(Debug, PartialEq, Clone)]
    pub struct SpreadPat {
        /// If the spread pattern binds the selected range
        pub name: Option<AstNode<Name>>,
    }

    /// The wildcard pattern.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct WildPat;

    /// Represents what kind of [RangePat] is being
    /// boundaries are specified when creating it.
    #[derive(Debug, PartialEq, Eq, Copy, Clone)]
    pub enum RangeEnd {
        /// The end element is included in the range, i.e. closed interval range.
        Included,
        /// The end element is excluded in the range, i.e. open interval range.
        Excluded,
    }

    impl Display for RangeEnd {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                RangeEnd::Included => write!(f, ".."),
                RangeEnd::Excluded => write!(f, "..<"),
            }
        }
    }

    /// A range pattern, which has a `lo` and `hi` endpoints
    /// representing the boundaries of the range, and a
    /// `end` which specifies if the range is open or closed
    /// interval, e.g. `'a'..<'g'`
    #[derive(Debug, PartialEq, Clone)]
    pub struct RangePat {
        /// Initial bound of the range
        pub lo: AstNode<Lit>,
        /// Upper bound of the range
        pub hi: AstNode<Lit>,
        /// Whether the `end` is included or not
        pub end: RangeEnd,
    }

    /// A pattern. e.g. `Ok(Dog(props = (1, x)))`.
    #[derive(Debug, PartialEq, Clone)]
    pub enum Pat {
        /// An access pattern is one that denotes the access of a property from
        /// another pattern. This is used to denote namespace accesses like
        /// `a::b::c`
        Access(AccessPat),
        /// A simple binding pattern, assign some value to the name of the pattern
        Binding(BindingPat),
        /// A representation of a constructor in the pattern space. Constructors in
        /// patterns can either be enum or struct values. The subject of the
        /// constructor can be either an [Pat::Access] or a [Pat::Binding].
        Constructor(ConstructorPat),
        /// Module pattern is used to destructure entries from an import.
        Module(ModulePat),
        /// A tuple pattern is a collection of patterns, e.g `(1, x, 'c')`
        Tuple(TuplePat),
        /// A list pattern, which is a collection of patterns, including spread and
        /// matches a list e.g `[x, 2, y]`
        List(ListPat),
        /// A literal pattern e.g. `c`
        ///
        /// @@Note: `tuple`, `map`, and `set` literal cannot appear within this
        /// branch
        Lit(LitPat),
        /// An `or` pattern which groups multiple patterns and matches one of the
        /// provided patterns e.g. `a | b | c`
        Or(OrPat),
        /// A pattern that is guarded by an if statement, e.g. `x if x > 5`
        If(IfPat),
        /// Wildcard pattern, similar to a binding but it is not bound
        /// to any member.
        Wild(WildPat),
        /// Similar to a [Pat::Wild], but does captures a collection of patterns,
        /// which can be used to ignore a range of elements in a tuple or
        /// a list.
        Spread(SpreadPat),
        /// A range pattern which represents an open or closed range of primitives
        /// e.g. `'a'..'z'`, `3..27`... etc
        Range(RangePat),
    }

    /// Enum representing whether a declaration is public or private
    /// within module scope.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Visibility {
        /// The binding is private to outer scopes. This is assumed by default.
        Private,
        /// The binding is public to outer scopes. The modifier has no
        /// effect if used within inner module scopes like a function.
        Public,
    }

    impl Display for Visibility {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Visibility::Private => write!(f, "private"),
                Visibility::Public => write!(f, "public"),
            }
        }
    }

    /// Enum representing whether a [BindingPat] is declared as being mutable
    /// or immutable.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Mutability {
        /// Declare that the binding can be re-assigned.
        Mutable,
        /// Declare that the binding cannot be re-assigned or methods that require
        /// mutable access cannot take this binding. This is assumed by default.
        Immutable,
    }

    impl Display for Mutability {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Mutability::Mutable => write!(f, "mutable"),
                Mutability::Immutable => write!(f, "immutable"),
            }
        }
    }

    /// A type function, e.g. `<T, U: Conv<U>> => ...`.
    ///
    /// Used in struct, enum, trait, and function definitions.
    #[derive(Debug, PartialEq, Clone)]
    pub struct TyFnDef {
        /// The type arguments of the function.
        pub params: AstNodes<Param>,
        /// Optional return type of the type function
        pub return_ty: Option<AstNode<Ty>>,
        /// The body of the type function,
        pub body: AstNode<Expr>,
    }

    /// A declaration, e.g. `x := 3;`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct Declaration {
        /// The pattern to bind the right-hand side to.
        pub pat: AstNode<Pat>,

        /// Any associated type with the expression
        pub ty: Option<AstNode<Ty>>,

        /// Any value that is assigned to the binding, simply
        /// an expression.
        pub value: Option<AstNode<Expr>>,
    }

    /// A merge declaration (adding implementations to traits/structs), e.g. `x ~=
    /// impl T { ... };`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct MergeDeclaration {
        /// The expression to bind the right-hand side to.
        pub decl: AstNode<Expr>,

        /// Any value that is assigned to the binding, simply
        /// an expression.
        pub value: AstNode<Expr>,
    }

    /// Unary operators that are defined within the core of the language.
    #[derive(Debug, Clone)]
    pub enum UnOp {
        // Bitwise logical inversion
        BitNot,
        /// Logical inversion.
        Not,
        /// The operator '-' for negation
        Neg,
        /// Get the type of an expression
        TypeOf,
    }

    impl Display for UnOp {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                UnOp::BitNot => write!(f, "~"),
                UnOp::Not => write!(f, "!"),
                UnOp::Neg => write!(f, "-"),
                UnOp::TypeOf => write!(f, "typeof"),
            }
        }
    }

    /// Binary operators that are defined within the core of the language.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum BinOp {
        /// '=='
        EqEq,
        /// '!='
        NotEq,
        /// '|'
        BitOr,
        /// '||'
        Or,
        /// '&'
        BitAnd,
        /// '&&'
        And,
        /// '^'
        BitXor,
        /// '^^'
        Exp,
        /// '>'
        Gt,
        /// '>='
        GtEq,
        /// '<'
        Lt,
        /// '<='
        LtEq,
        /// '>>'
        Shr,
        /// '<<'
        Shl,
        /// '+'
        Add,
        /// '-'
        Sub,
        /// '*'
        Mul,
        /// '/'
        Div,
        /// '%'
        Mod,
        /// 'as'
        As,
        /// `~`
        Merge,
    }

    impl Display for BinOp {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                BinOp::EqEq => write!(f, "=="),
                BinOp::NotEq => write!(f, "!="),
                BinOp::BitOr => write!(f, "|"),
                BinOp::Or => write!(f, "||"),
                BinOp::BitAnd => write!(f, "&"),
                BinOp::And => write!(f, "&&"),
                BinOp::BitXor => write!(f, "^"),
                BinOp::Exp => write!(f, "^^"),
                BinOp::Gt => write!(f, ">"),
                BinOp::GtEq => write!(f, ">="),
                BinOp::Lt => write!(f, "<"),
                BinOp::LtEq => write!(f, "<="),
                BinOp::Shr => write!(f, "<<"),
                BinOp::Shl => write!(f, ">>"),
                BinOp::Add => write!(f, "+"),
                BinOp::Sub => write!(f, "-"),
                BinOp::Mul => write!(f, "*"),
                BinOp::Div => write!(f, "/"),
                BinOp::Mod => write!(f, "%"),
                BinOp::As => write!(f, "as"),
                BinOp::Merge => write!(f, "~"),
            }
        }
    }

    impl BinOp {
        /// Compute the precedence for an operator
        pub fn infix_binding_power(&self) -> (u8, u8) {
            match self {
                BinOp::Or => (2, 3),
                BinOp::And => (4, 5),
                BinOp::EqEq | BinOp::NotEq => (6, 5),
                BinOp::Gt | BinOp::GtEq | BinOp::Lt | BinOp::LtEq => (7, 8),
                BinOp::BitOr | BinOp::BitXor => (9, 10),
                BinOp::BitAnd => (11, 12),
                BinOp::Shr | BinOp::Shl => (13, 14),
                BinOp::Add | BinOp::Sub => (15, 16),
                BinOp::Mul | BinOp::Div | BinOp::Mod => (17, 18),
                BinOp::Exp => (20, 19),
                BinOp::As => (21, 22),
                BinOp::Merge => (23, 24),
            }
        }

        /// This returns if an operator is actually re-assignable. By re-assignable,
        /// this is in the sense that you can add a '=' to mean that you are
        /// performing a re-assigning operation using the left
        /// hand-side expression as a starting point and the rhs as the other
        /// argument to the operator. For example, `a += b` is re-assigning
        /// because it means `a = a + b`.
        pub fn is_re_assignable(&self) -> bool {
            matches!(
                self,
                BinOp::BitOr
                    | BinOp::Or
                    | BinOp::BitAnd
                    | BinOp::And
                    | BinOp::BitXor
                    | BinOp::Exp
                    | BinOp::Shr
                    | BinOp::Shl
                    | BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
            )
        }

        /// Checks whether this operator is a ordering comparison operator, i.e. `<`
        /// `<=`, `>`, etc.
        pub fn is_ordering_comparator(&self) -> bool {
            matches!(self, BinOp::Gt | BinOp::GtEq | BinOp::Lt | BinOp::LtEq)
        }

        /// Checks whether this operator is a `lazy` operator, as in it is possible
        /// that only the first operand is evaluated before ever evaluating the
        /// second operand. Lazy operators are the logical operators `&&` and `||`
        /// that short-circuit.
        pub fn is_lazy(&self) -> bool {
            matches!(self, BinOp::And | BinOp::Or)
        }
    }

    /// An assign expression, e.g. `x = 4;`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct AssignExpr {
        /// The left-hand side of the assignment.
        ///
        /// This should resolve to either a variable or a struct field.
        pub lhs: AstNode<Expr>,
        /// The right-hand side of the assignment.
        ///
        /// The value will be assigned to the left-hand side.
        pub rhs: AstNode<Expr>,
    }

    /// An assign expression, e.g. `x += 4;`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct AssignOpExpr {
        /// The left-hand side of the assignment.
        ///
        /// This should resolve to either a variable or a struct field.
        pub lhs: AstNode<Expr>,
        /// The right-hand side of the assignment.
        ///
        /// The value will be assigned to the left-hand side.
        pub rhs: AstNode<Expr>,

        /// Operator that is applied with the assignment on the lhs with the rhs
        /// value.
        ///
        /// Note: Some binary operators are not allowed to be in the location.
        pub operator: AstNode<BinOp>,
    }

    /// A struct definition, e.g:
    /// ```ignore
    /// Foo := struct<T>( index: i32, val: T );
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    pub struct StructDef {
        /// Type parameters that are attached to the definition.
        pub ty_params: AstNodes<Param>,
        /// The fields of the struct, in the form of [Param].
        pub fields: AstNodes<Param>,
    }

    /// A variant of an enum definition, e.g. `Some(T)`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct EnumDefEntry {
        /// The name of the enum variant.
        pub name: AstNode<Name>,
        /// The parameters of the enum variant, if any.
        pub fields: AstNodes<Param>,
    }

    /// An enum definition, e.g.
    /// ```ignore
    /// enum<T> (
    ///     Some(T),
    ///     None
    /// )
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    pub struct EnumDef {
        /// Type parameters that are attached to the definition.
        pub ty_params: AstNodes<Param>,
        /// The variants of the enum, in the form of [EnumDefEntry].
        pub entries: AstNodes<EnumDefEntry>,
    }

    /// A trait definition, e.g.
    /// ```ignore
    /// trait<T> {
    ///     add: (T, T) -> T;
    /// }
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    pub struct TraitDef {
        /// Type parameters that are attached to the definition.
        pub ty_params: AstNodes<Param>,
        /// Members of the trait definition, which are constricted to
        /// constant-block only allowed [Expr]s.
        pub members: AstNodes<Expr>,
    }

    /// A return statement.
    ///
    /// Has an optional return expression, which becomes `void` if [None] is given.
    #[derive(Debug, PartialEq, Clone)]
    pub struct ReturnStatement(pub Option<AstNode<Expr>>);

    /// Break statement (only in loop context).
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct BreakStatement;

    /// Continue statement (only in loop context).
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct ContinueStatement;

    /// A branch/"case" of a `match` block.
    #[derive(Debug, PartialEq, Clone)]
    pub struct MatchCase {
        /// The pattern of the `match` case.
        pub pat: AstNode<Pat>,
        /// The expression corresponding to the match case.
        ///
        /// Will be executed if the pattern succeeds.
        pub expr: AstNode<Expr>,
    }

    /// The origin of a match block when the AST is
    /// de-sugared into simpler constructs. More details
    /// about the de-structuring process is detailed in
    /// [Block].
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum MatchOrigin {
        /// The match statement came from an `if` statement
        If,
        /// The match statement has no de-sugared origin
        Match,
        /// The match statement came from a de-sugared `for` loop
        For,
        /// The match statement came from a de-sugared `while` loop
        While,
    }

    /// A `match` block.
    #[derive(Debug, PartialEq, Clone)]
    pub struct MatchBlock {
        /// The expression to match on.
        pub subject: AstNode<Expr>,
        /// The match cases to execute.
        pub cases: AstNodes<MatchCase>,
        /// Whether the match block represents a for, while, if or match statement
        pub origin: MatchOrigin,
    }

    /// A body block.
    #[derive(Debug, PartialEq, Clone)]
    pub struct BodyBlock {
        /// Zero or more statements.
        pub statements: AstNodes<Expr>,
        /// Zero or one expression.
        pub expr: Option<AstNode<Expr>>,
    }

    impl BodyBlock {
        /// Get the members of the body block: the list of statements as well as the
        /// optional ending expression.
        pub fn members(&self) -> impl Iterator<Item = AstNodeRef<Expr>> + '_ {
            self.statements.ast_ref_iter().chain(self.expr.as_ref().map(|x| x.ast_ref()))
        }
    }

    /// Loop block e.g. `loop { ... }`
    #[derive(Debug, PartialEq, Clone)]
    pub struct LoopBlock(pub AstNode<Block>);

    /// A for-loop block e.g. `for pat in iterator { ...body... }`
    #[derive(Debug, PartialEq, Clone)]
    pub struct ForLoopBlock {
        /// The pattern that de-structures the operator
        pub pat: AstNode<Pat>,
        /// The iterator of the for loop, goes after the `in`
        pub iterator: AstNode<Expr>,
        /// The body of the for-loop
        pub body: AstNode<Block>,
    }

    /// A `while` loop, e.g. `while x > 2 { ... }`
    #[derive(Debug, PartialEq, Clone)]
    pub struct WhileLoopBlock {
        /// The condition of the the `while` loop.
        pub condition: AstNode<Expr>,
        /// The body of the `while` loop.
        pub body: AstNode<Block>,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub struct IfClause {
        /// The condition of the `if` block.
        pub condition: AstNode<Expr>,
        /// The body of the `if-statement`
        pub body: AstNode<Block>,
    }

    /// An `if` block consisting of the condition, block and an optional else clause
    /// e.g. `if x { ... } else { y }`
    #[derive(Debug, PartialEq, Clone)]
    pub struct IfBlock {
        pub clauses: AstNodes<IfClause>,
        /// The else clause.
        pub otherwise: Option<AstNode<Block>>,
    }

    /// A `mod` block, e.g.
    ///
    /// ```ignore
    /// mod {
    ///     foo := () -> char => {
    ///     };
    /// }
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    pub struct ModBlock {
        /// Any type parameters that are applied to the `mod` block.
        pub ty_params: AstNodes<Param>,
        /// The actual contents of the block.
        pub block: AstNode<BodyBlock>,
    }

    /// An `impl` block, e.g.
    ///
    /// ```ignore
    /// impl<T> {
    ///     into := () -> T => {
    ///     };
    /// };
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    pub struct ImplBlock {
        /// Any type parameters that are applied to the `mod` block.
        pub ty_params: AstNodes<Param>,
        /// The actual contents of the block.
        pub block: AstNode<BodyBlock>,
    }

    /// A block.
    #[derive(Debug, PartialEq, Clone)]
    pub enum Block {
        /// A match block.
        Match(MatchBlock),
        /// A loop block. The inner block is the loop body.
        Loop(LoopBlock),
        /// A for-loop block. This is later transpiled into a more simpler
        /// construct using a `loop` and a `match` clause.
        ///
        /// Since for loops are used for iterators in hash, we transpile the
        /// construct into a primitive loop. An iterator can be traversed by
        /// calling the next function on the iterator. Since next returns a
        /// Option type, we need to check if there is a value or if it returns None.
        /// If a value does exist, we essentially perform an assignment to the
        /// pattern provided. If None, the branch immediately breaks the for
        /// loop.
        ///
        /// A rough outline of what the transpilation process for a for loop looks
        /// like:
        ///
        /// Take the original for-loop:
        ///
        /// ```text
        /// for <pat> in <iterator> {
        ///      <block>
        /// }
        /// ```
        ///
        /// convert it to:
        ///
        /// ```text
        /// loop {
        ///     match next(<iterator>) {
        ///         Some(<pat>) => <block>;
        ///         None        => break;
        ///     }
        /// }
        /// ```
        For(ForLoopBlock),
        /// A while-loop block. This is later transpiled into a `loop` and `match`
        /// clause.
        ///
        /// In general, a while loop transpilation process occurs by transferring
        /// the looping condition into a match block, which compares a boolean
        /// condition. If the boolean condition evaluates to false, the loop
        /// will immediately break. Otherwise the body expression is expected. A
        /// rough outline of what the transpilation process for a while loop looks
        /// like:
        ///
        /// ```text
        /// while <condition> {
        ///      <block>
        /// }
        /// ```
        ///
        /// Is converted to:
        ///
        /// ```text
        /// loop {
        ///     match <condition> {
        ///         true  => <block>;
        ///         false => break;
        ///     }
        /// }
        /// ```
        While(WhileLoopBlock),

        /// The AST representation of an if-block.
        ///
        /// ## Transpilation
        /// We transpile if-else blocks into match blocks in order to simplify
        /// the typechecking process and optimisation efforts.
        ///
        /// Firstly, since we always want to check each case, we convert the
        /// if statement into a series of and-patterns, where the right hand-side
        /// pattern is the condition to execute the branch...
        ///
        /// For example:
        /// ```text
        /// if a { a_branch } else if b { b_branch } else { c_branch }
        /// ```
        /// will be transformed into...
        /// ```text
        /// match true {
        ///     _ if a => a_branch
        ///     _ if b => b_branch
        ///     _ => c_branch
        /// }
        /// ```
        ///
        /// Additionally, if no 'else' clause is specified, we fill it with an
        /// empty block since an if-block could be assigned to any variable and
        /// therefore we need to know the outcome of all branches for
        /// typechecking.
        If(IfBlock),
        /// A body block.
        Body(BodyBlock),
        /// A module block. The inner block becomes an inner module of the current
        /// module.
        Mod(ModBlock),
        /// An implementation block
        Impl(ImplBlock),
    }

    impl Block {
        pub fn as_str(&self) -> &str {
            match self {
                Block::Match(_) => "match(..)",
                Block::Loop(_) => "loop(..)",
                Block::For(_) => "for(..)",
                Block::While(_) => "while(..)",
                Block::If(_) => "if(..)",
                Block::Mod(_) => "mod(..)",
                Block::Body(_) => "body(..)",
                Block::Impl(_) => "impl(..)",
            }
        }
    }

    /// This enum describes the origin kind of the subject that a parameter
    /// unification occurred on.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum ParamOrigin {
        /// If at the current time, it's not known the origin of the parameter list,
        /// the function will default to using this.
        Unknown,
        /// Parameters came from a tuple
        Tuple,
        /// Parameters came from a struct
        Struct,
        /// Parameters came from a function definition
        Fn,
        /// Parameters came from a function call
        FnCall,
        /// Parameters came from a type function definition
        TyFn,
        /// Parameters came from a type function call
        TyFnCall,
        /// Parameters came from an enum variant initialisation
        EnumVariant,
        /// List pattern parameters, the parameters are all the same, but it's
        /// used to represent the inner terms of the list pattern since spread
        /// patterns may become named parameters.
        ListPat,
        /// Module pattern
        ModulePat,
        /// Constructor pattern, although this is likely to be erased into a
        /// [ParamOrigin::Struct] or [ParamOrigin::EnumVariant] when inspected.
        ConstructorPat,
    }

    impl ParamOrigin {
        /// Get the name of the `field` that the [ParamOrigin] refers to.
        /// In other words, what is the name for the parameters that are
        /// associated with the [ParamOrigin].
        pub fn field_name(&self) -> &'static str {
            match self {
                ParamOrigin::Unknown => "field",
                ParamOrigin::Tuple => "field",
                ParamOrigin::Struct => "field",
                ParamOrigin::Fn | ParamOrigin::TyFn => "parameter",
                ParamOrigin::FnCall | ParamOrigin::TyFnCall => "argument",
                ParamOrigin::EnumVariant => "field",
                ParamOrigin::ListPat => "element",
                ParamOrigin::ModulePat => "field",
                ParamOrigin::ConstructorPat => "field",
            }
        }
    }

    impl Display for ParamOrigin {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                ParamOrigin::Unknown => write!(f, "unknown"),
                ParamOrigin::Tuple => write!(f, "tuple"),
                ParamOrigin::Struct => write!(f, "struct"),
                ParamOrigin::Fn | ParamOrigin::FnCall => write!(f, "function"),
                ParamOrigin::TyFn | ParamOrigin::TyFnCall => write!(f, "type function"),
                ParamOrigin::EnumVariant => write!(f, "enum variant"),
                ParamOrigin::ListPat => write!(f, "list pattern"),
                ParamOrigin::ModulePat => write!(f, "module pattern"),
                ParamOrigin::ConstructorPat => write!(f, "constructor pattern"),
            }
        }
    }

    /// A function definition parameter.
    #[derive(Debug, PartialEq, Clone)]
    pub struct Param {
        /// The name of the argument.
        pub name: Option<AstNode<Name>>,
        /// The type of the argument, if any.
        pub ty: Option<AstNode<Ty>>,
        /// Default value of the argument if provided.
        ///
        /// If the value is provided, this makes it a named argument
        /// which means that they can be specified by putting the name of the
        /// argument.
        pub default: Option<AstNode<Expr>>,
        /// The origin of the parameter, whether it is from a struct field, function
        /// def, type function def, etc.
        pub origin: ParamOrigin,
    }

    /// A function definition.
    #[derive(Debug, PartialEq, Clone)]
    pub struct FnDef {
        /// The parameters of the function definition.
        pub params: AstNodes<Param>,
        /// The return type of the function definition.
        ///
        /// Will be inferred if [None].
        pub return_ty: Option<AstNode<Ty>>,
        /// The body/contents of the function, in the form of an expression.
        pub fn_body: AstNode<Expr>,
    }

    /// Function call argument.
    #[derive(Debug, PartialEq, Clone)]
    pub struct ConstructorCallArg {
        /// Optional name for the function argument, e.g `f(x = 3);`.
        pub name: Option<AstNode<Name>>,
        /// Each argument of the function call, as an expression.
        pub value: AstNode<Expr>,
    }

    /// A constructor call expression. This can either be a function
    /// call, a struct instantiation or a enum variant instantiation.
    #[derive(Debug, PartialEq, Clone)]
    pub struct ConstructorCallExpr {
        /// An expression which evaluates to a function value.
        pub subject: AstNode<Expr>,
        /// Arguments to the function, a list of [ConstructorCallArg]s.
        pub args: AstNodes<ConstructorCallArg>,
    }

    /// An directive expression.
    #[derive(PartialEq, Debug, Clone)]
    pub struct DirectiveExpr {
        /// The name of the directive (without the "#").
        pub name: AstNode<Name>,
        /// An expression which is referenced in the directive
        pub subject: AstNode<Expr>,
    }

    /// A the kind of access an [AccessExpr] has
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum AccessKind {
        /// A namespace access, i.e. `a::b`
        Namespace,
        /// A property access, i.e. `a.b`
        Property,
    }

    impl Display for AccessKind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                AccessKind::Namespace => write!(f, "namespace"),
                AccessKind::Property => write!(f, "property"),
            }
        }
    }

    /// The kind of property that's being accessed, either being
    /// named or numeric, e.g `foo.x`, `foo.1`, etc.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum PropertyKind {
        /// A named field like
        NamedField(Identifier),

        /// The numeric value of the index that's being accessed
        NumericField(usize),
    }

    /// A property access expression.
    #[derive(Debug, PartialEq, Clone)]
    pub struct AccessExpr {
        /// An expression which evaluates to a struct or tuple value.
        pub subject: AstNode<Expr>,
        /// The property of the subject to access.
        pub property: AstNode<PropertyKind>,
        /// The kind of access, either namespacing or property
        pub kind: AccessKind,
    }

    /// A typed expression, e.g. `foo as int`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct CastExpr {
        /// The annotated type of the expression.
        pub ty: AstNode<Ty>,
        /// The expression being typed.
        pub expr: AstNode<Expr>,
    }

    /// Represents a path to a module, given as a string literal to an `import`
    /// call.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct Import {
        pub path: InternedStr,
        pub resolved_path: PathBuf,
    }

    /// A variable expression.
    #[derive(Debug, PartialEq, Clone)]
    pub struct VariableExpr {
        /// The name of the variable.
        pub name: AstNode<Name>,
    }

    /// A reference expression with a flag denoting whether it is a raw ref or not
    #[derive(Debug, PartialEq, Clone)]
    pub struct RefExpr {
        pub inner_expr: AstNode<Expr>,
        /// The kind of reference, either being a normal reference or a `raw`
        /// reference
        pub kind: RefKind,
        /// Mutability modifier on the expression.
        pub mutability: Option<AstNode<Mutability>>,
    }

    /// A dereference expression.
    #[derive(Debug, PartialEq, Clone)]
    pub struct TyExpr(pub AstNode<Ty>);

    /// A dereference expression.
    #[derive(Debug, PartialEq, Clone)]
    pub struct DerefExpr(pub AstNode<Expr>);

    /// An unsafe expression.
    #[derive(Debug, PartialEq, Clone)]
    pub struct UnsafeExpr(pub AstNode<Expr>);

    /// A literal.
    #[derive(Debug, PartialEq, Clone)]
    pub struct LitExpr(pub AstNode<Lit>);

    /// A block.
    #[derive(Debug, PartialEq, Clone)]
    pub struct BlockExpr(pub AstNode<Block>);

    /// An `import` call.
    #[derive(Debug, PartialEq, Clone)]
    pub struct ImportExpr(pub AstNode<Import>);

    /// A trait implementation.
    #[derive(Debug, PartialEq, Clone)]
    pub struct TraitImpl {
        /// The referenced name to the trait
        pub ty: AstNode<Ty>,
        /// The implementation of the trait.
        pub body: AstNodes<Expr>,
    }

    /// A binary expression `2 + 2`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct BinaryExpr {
        /// left hand-side of the binary expression
        pub lhs: AstNode<Expr>,
        /// right hand-side of the binary expression
        pub rhs: AstNode<Expr>,
        /// The unary operator of the [BinaryExpr]
        pub operator: AstNode<BinOp>,
    }

    /// A unary expression `!a`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct UnaryExpr {
        /// The expression that the unary operator is applied to
        pub expr: AstNode<Expr>,
        /// The unary operator of the [UnaryExpr]
        pub operator: AstNode<UnOp>,
    }

    /// An index expression `arr[x]`.
    #[derive(Debug, PartialEq, Clone)]
    pub struct IndexExpr {
        /// The subject that is being indexed.
        pub subject: AstNode<Expr>,
        /// The expression that is the index.
        pub index_expr: AstNode<Expr>,
    }

    /// The kind of an expression.
    #[derive(Debug, PartialEq, Clone)]
    pub enum ExprKind {
        /// A constructor call which could be a struct/enum initialisation or a
        /// function call e.g. `foo(5)`.
        ConstructorCall(ConstructorCallExpr),
        /// A directive expression
        Directive(DirectiveExpr),
        /// Declaration e.g. `x := 5;`
        Declaration(Declaration),
        /// A variable e.g. `x`
        Variable(VariableExpr),
        /// Either a property access or a namespace access
        Access(AccessExpr),
        /// Reference expression e.g. `&expr`
        Ref(RefExpr),
        /// Dereference expression e.g. `*expr`
        Deref(DerefExpr),
        /// Unsafe block expression e.g. `unsafe { *(&raw bytes) }`
        Unsafe(UnsafeExpr),
        /// Literal expression e.g. `5`
        LitExpr(LitExpr),
        /// Cast expression e.g. `x as u32`
        Cast(CastExpr),
        /// Block expression
        Block(BlockExpr),
        /// Import expression e.g. `import("lib")`
        Import(ImportExpr),
        /// Struct definition expression e.g. `struct(foo: str)`
        StructDef(StructDef),
        /// Struct definition expression e.g. `enum(Bar(u32), Baz(f32))`
        EnumDef(EnumDef),
        /// Type function definition e.g. `<T> => ...`
        TyFnDef(TyFnDef),
        /// Trait definition e.g.  `trait { ... }`
        TraitDef(TraitDef),
        /// Function definition e.g. `(foo: i32) -> i32 => { ... }`
        FnDef(FnDef),
        /// Type expression e.g. `type i32`
        Ty(TyExpr),
        /// Break statement e.g. `return 5;`
        Return(ReturnStatement),
        /// Break statement e.g. `break`
        Break(BreakStatement),
        /// Continue statement e.g. `continue`
        Continue(ContinueStatement),
        /// Expression to index a subject e.g. `arr[x]`
        Index(IndexExpr),
        /// An expression that captures a variable or a pattern being assigned
        /// to a right hand-side expression such as `x = 3`.
        Assign(AssignExpr),
        /// An expression that captures a variable or a pattern being assigned with
        /// the application of a binary operator, such as `x += 3`.
        AssignOp(AssignOpExpr),
        /// A merge declaration is one that adds an implementation for a particular
        /// trait/struct to an already declared item, such as `x ~= impl T { ... }`
        MergeDeclaration(MergeDeclaration),
        /// Trait implementation e.g. `impl Clone { ... }`
        TraitImpl(TraitImpl),
        /// Binary Expression composed of a left and right hand-side with a binary
        /// operator
        BinaryExpr(BinaryExpr),
        /// Unary Expression composed of a unary operator and an expression
        UnaryExpr(UnaryExpr),
    }

    /// An expression.
    #[derive(Debug, PartialEq, Clone)]
    pub struct Expr {
        /// The kind of the expression
        pub kind: ExprKind,
    }

    impl Expr {
        /// Create a new [Expr] with a specific [ExprKind].
        pub fn new(kind: ExprKind) -> Self {
            Self { kind }
        }

        /// Convert the [Expr] into an [ExprKind]
        pub fn into_kind(self) -> ExprKind {
            self.kind
        }

        /// Get the [ExprKind] of the expression
        pub fn kind(&self) -> &ExprKind {
            &self.kind
        }

        /// Get the [ExprKind] of the expression
        pub fn kind_mut(&mut self) -> &mut ExprKind {
            &mut self.kind
        }
    }

    /// A module.
    ///
    /// Represents a parsed `.hash` file.
    #[derive(Debug, PartialEq, Clone)]
    pub struct Module {
        /// The contents of the module, as a list of expressions terminated with a
        /// semi-colon.
        pub contents: AstNodes<Expr>,
    }
}
