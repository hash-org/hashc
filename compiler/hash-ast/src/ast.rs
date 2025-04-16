//! Frontend-agnostic Hash AST (abstract syntax tree) type definitions.

use std::{
    fmt::Display,
    hash::Hash,
    iter::repeat_n,
    ops::{Deref, DerefMut},
};

use hash_source::{
    SourceId,
    constant::AllocId,
    identifier::Identifier,
    location::{ByteRange, Span},
};
use hash_token::{Base, FloatLitKind, IntLitKind, Token, delimiter::Delimiter};
use hash_tree_def::define_tree;
use hash_utils::{
    counter,
    parking_lot::{RwLock, RwLockWriteGuard},
    thin_vec::{ThinVec, thin_vec},
};
use once_cell::sync::Lazy;
use replace_with::replace_with_or_abort;

counter! {
    /// This is the unique identifier for an AST node. This is used to
    /// map spans to nodes, and vice versa. [AstNodeId]s are unique and
    /// they are always increasing as a new nodes are created.
    name: AstNodeId,
    counter_name: AST_COUNTER,
    visibility: pub,
    method_visibility:,
    derives: (Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug),
}

impl AstNodeId {
    /// Create a null node id.
    pub fn null() -> Self {
        AstNodeId::from(0)
    }

    /// Get the [Span] of this [AstNodeId].
    pub fn span(&self) -> Span {
        SpanMap::span_of(*self)
    }

    /// Get the [SourceId] of this [AstNodeId].
    pub fn source(&self) -> SourceId {
        SpanMap::source_of(*self)
    }
}

/// Name for some reference within the AST to a source
/// hunk. This is essentially an interned [Span] that
/// can be used to reference a particular part of the
/// source.
pub type Hunk = AstNodeId;

impl Hunk {
    /// Create a new [Hunk] from a [Span].
    pub fn create(span: Span) -> Self {
        SpanMap::add_span(span)
    }
}

/// The [`SPAN_MAP`] is a global static that is used to store the span
/// of each AST node. This is used to avoid storing the [Span] on the
/// [`AstNode<T>`] itself in order for other data structures to be able
/// to query the [Span] of a node simply by using the [AstNodeId] of the
/// node.
static SPAN_MAP: Lazy<RwLock<Vec<Span>>> = Lazy::new(|| {
    // We initialise the map with a NULL node-id so we can use it as the default
    // for items that need a node, but don't have one.
    RwLock::new(vec![Span::new(ByteRange::new(0, 0), SourceId::default())])
});

/// A thread/job local map of [AstNodeId]s to [ByteRange]s. The [LocalSpanMap]
/// can be used by a thread to "reserve" [AstNodeId]s for nodes that will be
/// added to the global [`SPAN_MAP`] later.
///
/// ##Note: This is only used by the parser in order to reduce contention for [`SPAN_MAP`].
#[derive(Default)]
pub struct LocalSpanMap {
    map: Vec<(AstNodeId, ByteRange)>,
}

impl LocalSpanMap {
    /// Create a new [LocalSpanMap] with a given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self { map: Vec::with_capacity(capacity) }
    }

    /// Add a new node to the map.
    pub fn add(&mut self, range: ByteRange) -> AstNodeId {
        let id = AstNodeId::new();
        self.map.push((id, range));
        id
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

/// Utilities for working with the [`SPAN_MAP`].
pub struct SpanMap;

impl SpanMap {
    /// Get the span of a node by [AstNodeId].
    pub fn span_of(id: AstNodeId) -> Span {
        let span = SPAN_MAP.read()[id.to_usize()];
        debug_assert_ne!(span, Span::null(), "span of node {id:?} is null");
        span
    }

    /// Get the [SourceId] of a node by [AstNodeId].
    pub fn source_of(id: AstNodeId) -> SourceId {
        SpanMap::span_of(id).id
    }

    fn extend_map(writer: &mut RwLockWriteGuard<Vec<Span>>, id: AstNodeId) {
        let len = (id.to_usize() + 1).saturating_sub(writer.len());
        if len > 0 {
            writer.extend(repeat_n(Span::null(), len));
        }
    }

    /// Get a mutable reference to the [`SPAN_MAP`]. This is only
    /// internal to the `hash-ast` crate since it creates entries
    /// in the span map when creating new AST nodes.
    fn add_span(span: Span) -> AstNodeId {
        let mut writer = SPAN_MAP.write();

        // Create the new id, expand the map for capacity and
        // then write the span into the map.
        let id = AstNodeId::new();
        Self::extend_map(&mut writer, id);
        writer[id.to_usize()] = span;

        id
    }

    /// Update the span of a node by [AstNodeId].
    fn update_span(id: AstNodeId, span: Span) {
        SPAN_MAP.write()[id.to_usize()] = span;
    }

    /// Merge a [LocalSpanMap] into the [`SPAN_MAP`].
    pub fn add_local_map(source: SourceId, local: LocalSpanMap) {
        // If no nodes were added, don't do anything!
        if local.map.is_empty() {
            return;
        }

        let mut writer = SPAN_MAP.write();
        let (key, _) = local.map.last().unwrap();

        // Reserve enough space in the global map to fit the local map.
        //
        // ##Note: During high loads, we're likely reserving space for all of the
        // other nodes that are to be added.
        Self::extend_map(&mut writer, *key);

        // Now we write all of the items into the map.
        for (id, range) in local.map {
            writer[id.to_usize()] = Span::new(range, source);
        }
    }
}

/// Represents an abstract syntax tree node.
///
/// Contains an inner type, as well as begin and end positions in the input.
#[derive(Debug, Clone)]
pub struct AstNode<T> {
    /// The stored data within this node
    body: Box<T>,
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
        let id = SpanMap::add_span(span);
        Self { body: Box::new(body), id }
    }

    /// Create an [AstNode] with an existing [AstNodeId].
    pub fn with_id(body: T, id: AstNodeId) -> Self {
        Self { body: Box::new(body), id }
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
        SpanMap::span_of(self.id)
    }

    /// Get the [ByteRange] of this [AstNode].
    pub fn byte_range(&self) -> ByteRange {
        self.span().range
    }

    /// Set the [Span] of this [AstNode].
    pub fn set_span(&mut self, span: Span) {
        SpanMap::update_span(self.id, span)
    }

    /// Get the [AstNodeId] of this node.
    pub fn id(&self) -> AstNodeId {
        self.id
    }

    /// Create an [AstNodeRef] from this [AstNode].
    pub fn ast_ref(&self) -> AstNodeRef<T> {
        AstNodeRef { body: self.body.as_ref(), id: self.id }
    }

    /// Create an [AstNodeRefMut] from this [AstNode].
    pub fn ast_ref_mut(&mut self) -> AstNodeRefMut<T> {
        AstNodeRefMut { body: self.body.as_mut(), id: self.id }
    }

    /// Create an [AstNodeRef] by providing a body and copying over the
    /// [AstNodeId] that belong to this [AstNode].
    pub fn with_body<'u, U>(&self, body: &'u U) -> AstNodeRef<'u, U> {
        AstNodeRef { body, id: self.id }
    }
}

#[derive(Debug)]
pub struct AstNodeRef<'t, T> {
    /// A reference to the body of the [AstNode].
    pub body: &'t T,

    /// The [AstNodeId] of the node, representing a unique identifier within
    /// the AST, useful for performing fast comparisons of trees.
    pub id: AstNodeId,
}

impl<T> Clone for AstNodeRef<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for AstNodeRef<'_, T> {}

impl<'t, T> AstNodeRef<'t, T> {
    /// Create a new [AstNodeRef<T>].
    pub fn new(body: &'t T, id: AstNodeId) -> Self {
        AstNodeRef { body, id }
    }

    /// Get a reference to body of the [AstNodeRef].
    pub fn body(&self) -> &'t T {
        self.body
    }

    /// Utility function to copy over the [AstNodeId] from
    /// another [AstNodeRef] with a provided body.
    pub fn with_body<'u, U>(&self, body: &'u U) -> AstNodeRef<'u, U> {
        AstNodeRef { body, id: self.id }
    }

    /// Get the [Span] of this [AstNodeRef].
    pub fn span(&self) -> Span {
        SpanMap::span_of(self.id)
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

    /// The [AstNodeId] of the [AstNode], representing a unique identifier
    /// within the AST, useful for performing fast comparisons of trees.
    pub id: AstNodeId,
}

impl<'t, T> AstNodeRefMut<'t, T> {
    /// Create a new [AstNodeRefMut<T>].
    pub fn new(body: &'t mut T, id: AstNodeId) -> Self {
        AstNodeRefMut { body, id }
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
        SpanMap::span_of(self.id)
    }

    /// Get the [AstNodeId] of this [AstNodeRefMut].
    pub fn id(&self) -> AstNodeId {
        self.id
    }

    /// Get this node as an immutable reference
    pub fn immutable(&self) -> AstNodeRef<T> {
        AstNodeRef::new(self.body, self.id)
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
    pub nodes: ThinVec<AstNode<T>>,

    /// The id that is used to refer to the span of the [AstNodes].
    id: AstNodeId,
}

impl<T> AstNodes<T> {
    /// Create a new [AstNodes].
    pub fn empty(span: Span) -> Self {
        Self::new(thin_vec![], span)
    }

    /// Create an [AstNodes] with items and a [Span].
    pub fn new(nodes: ThinVec<AstNode<T>>, span: Span) -> Self {
        let id = SpanMap::add_span(span);
        Self { nodes, id }
    }

    /// Create a new [AstNodes] with an existing [AstNodeId].
    pub fn with_id(nodes: ThinVec<AstNode<T>>, id: AstNodeId) -> Self {
        Self { nodes, id }
    }

    /// Function to adjust the span location of [AstNodes] if it is initially
    /// incorrectly offset because there is a 'pre-conditional' token that must
    /// be parsed before parsing the nodes. This token could be something like a
    /// '<' or '(' which starts a tuple, or type bound
    pub fn set_span(&mut self, span: Span) {
        SpanMap::update_span(self.id, span);
    }

    /// Get the [AstNodeId] of this [AstNodes].
    pub fn id(&self) -> AstNodeId {
        self.id
    }

    /// Get the [Span] of this [AstNodes].
    pub fn span(&self) -> Span {
        SpanMap::span_of(self.id)
    }

    /// Insert an item into the [AstNodes] at a particular index.
    pub fn insert(&mut self, item: AstNode<T>, index: usize) {
        self.nodes.insert(index, item);
    }

    /// Merge two [AstNodes] together, this will append the nodes of the
    /// other [AstNodes] to this one, and then return the new [AstNodes].
    ///
    /// **Note** this will automatically update the [Span] of this node
    /// by extending it with the span of the other node.
    pub fn merge(&mut self, other: Self) {
        self.set_span(self.span().join(other.span()));
        self.nodes.extend(other.nodes);
    }

    /// Iterate over each child whilst wrapping it in a [AstNodeRef].
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
        root_module: hash_ast::ast,
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

    impl std::fmt::Display for Name {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.ident)
        }
    }

    /// Macro invocation argument.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct MacroInvocationArg {
        /// Optional name for the function argument, e.g `f(x = 3);`.
        pub name: OptionalChild!(Name),

        /// Each argument of the function call, as an expression.
        pub value: Child!(Expr),
    }

    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct MacroInvocationArgs {
        pub args: Children!(MacroInvocationArg),
    }


    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct MacroInvocation {
        /// The name of the macro. @@Todo: make this into an access-name.
        pub name: Child!(Name),

        /// Any arguments to the macro itself.
        pub args: OptionalChild!(MacroInvocationArgs),
    }

    /// This is a collection of macro invocations that can occur on a single
    /// item which are collected into a single node.
    ///
    /// ##Note: the `AstNodeId` of the `MacroInvocations` will be the same as
    /// the id of the children `invocations` node. The [`MacroInvocations`]
    /// struct is only to effectively collect logic for handling clumps of such
    /// invocations under one node.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct MacroInvocations {
        pub invocations: Children!(MacroInvocation),
    }

    impl MacroInvocations {
        /// Get the number of invocations that are contained within this node.
        pub fn len(&self) -> usize {
            self.invocations.len()
        }

        /// Check whether this node contains any invocations.
        pub fn is_empty(&self) -> bool {
            self.invocations.is_empty()
        }
    }

    /// A macro invocation on an expression.
    #[derive(PartialEq, Debug, Clone)]
    #[node]
    pub struct ExprMacroInvocation {
        /// The directives that apply on the subject expression.
        pub macros: Child!(MacroInvocations),

        /// The subjection expression of the invocation.
        pub subject: Child!(Expr),
    }

    /// A macro invocation on a type.
    #[derive(PartialEq, Debug, Clone)]
    #[node]
    pub struct TyMacroInvocation {
        /// The directives that apply on the subject type.
        pub macros: Child!(MacroInvocations),

        /// The subject type of the invocation.
        pub subject: Child!(Ty),
    }

    /// A macro invocation on an expression.
    #[derive(PartialEq, Debug, Clone)]
    #[node]
    pub struct PatMacroInvocation {
        /// The directives that apply on the subject pattern.
        pub macros: Child!(MacroInvocations),

        /// The subject pattern of the invocation.
        pub subject: Child!(Pat),
    }


    /// A token macro invocation, e.g.
    /// ```
    /// @brainfuck   { ,+[-.,+] }
    ///  ^^^^^^^^^   ^^^^^^^^^^^^
    ///  Invocation  Token stream
    /// ```
    #[derive(Clone, Debug, PartialEq)]
    #[node]
    pub struct TokenMacroInvocation {
        /// The macro invocation name, and possibly arguments.
        pub mac: Child!(TokenMacro),

        /// The token stream that is being applied to the macro.
        pub stream: Child!(TokenStream),
    }

    /// The name of the token macro, and any optional arguments that
    /// are applied to the macro.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TokenMacro {
        /// The name of the macro. @@Todo: make this into an access-name.
        pub name: Child!(Name),

        /// Any arguments to the macro itself.
        pub args: OptionalChild!(MacroInvocationArgs),

        /// If the macro name and arguments are wrapped in `[...]`
        pub delimited: bool
    }

    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TokenStream {
        pub tokens: Vec<Token>,

        /// The delimiter used for the stream.
        pub delimiter: Delimiter,
    }

    /// The kind of macros that can be invoked and written in the source.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum MacroKind {
        /// A token macro, which accepts a token tree and returns a parse-able token
        /// tree which is later converted into AST. Token macros begin with a `@`.
        Token,

        /// An AST-level macro which is directly applied onto an AST node. AST-level
        /// macros begin with a `#`.
        Ast
    }

    /// A concrete/"named" type.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct NamedTy {
        /// The name of the type.
        pub name: Child!(Name),
    }

    /// Access type denotes the access of a property of some inner type.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct AccessTy {
        /// The subject of the access
        pub subject: Child!(Ty),
        /// the property that is access of the `subject` type
        pub property: Child!(Name),
    }

    /// Reference kind representing either a raw reference or a normal reference.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    #[node]
    pub enum RefKind {
        /// Raw reference type
        Raw,
        /// Normal reference type
        Normal,
    }

    /// A reference type.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct RefTy {
        /// Inner type of the reference type
        pub inner: Child!(Ty),
        /// Whether this reference is a `raw` reference or normal reference (normal
        /// by default).
        pub kind: OptionalChild!(RefKind),
        /// Mutability of the reference (immutable by default)
        pub mutability: OptionalChild!(Mutability),
    }

    /// A type argument `<T: u32>`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TyArg {
        /// An optional name to the argument
        pub name: OptionalChild!(Name),

        /// The assigned value of the type argument
        pub ty: Child!(Ty),

        /// Any macros are invoked on the parameter.
        pub macros: OptionalChild!(MacroInvocations),
    }

    /// The tuple type.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TupleTy {
        /// inner types of the tuple type
        pub entries: Child!(Params),
    }

    /// Array type, , e.g. `[T]`, `[T; N]`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ArrayTy {
        /// Inner type of the array
        pub inner: Child!(Ty),

        /// An optional expression that denotes the length of the array
        /// as a constant.
        pub len: OptionalChild!(Expr),
    }

    /// The function type.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct FnTy {
        /// Any defined parameters for the function type
        pub params: Child!(Params),

        /// Optional return type
        pub return_ty: Child!(Ty),
    }

    /// A type function e.g. `<T = u32, E: Conv ~ Eq> -> Result<T, E>`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ImplicitFnTy {
        /// The parameters of the type function
        pub params: Child!(TyParams),
        /// Return type of the function
        pub return_ty: Child!(Ty),
    }

    /// An implicit function call specifies a call to a implicit function with the specified
    /// function name in the form of a [Ty] (which can only be a [NamedTy] then
    /// followed by arguments. For example: `Conv<u32>` or `(Foo<bar>)<baz>`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ImplicitFnCall {
        /// The subject of the type function call
        pub subject: Child!(Expr),
        /// Arguments that are applied to the type function call
        pub args: Children!(TyArg),
    }

    /// An equality type specifies that there is an equality between two types, and hence
    /// labelling it as the type of equality between the two operands.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct EqualityTy {
        /// left hand-side of the equality type.
        pub lhs: Child!(Ty),

        /// right hand-side of the equality type.
        pub rhs: Child!(Ty),
    }

    /// A union type meaning that multiple types are accepted, e.g. `f64 | i64`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct UnionTy {
        /// left hand-side of the union type
        pub lhs: Child!(Ty),
        /// right hand-side of the union type
        pub rhs: Child!(Ty),
    }

    /// Binary type operators enumeration.
    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum BinTyOp {
        /// The union of two types, essentially an or, e.g `f64 | u64`
        Union,
        /// The intersection between two types, essentially an `and`, `Ord ~ Eq`
        Equality,
    }

    impl BinTyOp {
        /// Compute the precedence for an operator
        pub fn infix_binding_power(&self) -> (u8, u8) {
            match self {
                BinTyOp::Equality => (2, 3),
                BinTyOp::Union => (4, 5),
            }
        }
    }

    /// An expression within a type in the form of `{ <expr> }`
    /// This is used to allow for expressions within types, e.g. `Result<{ 1 + 2 }, E>`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ExprTy {
        /// The expression within the type
        pub expr: Child!(Expr),
    }

    /// A type.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub enum Ty {
        /// Access type, access the property of some inner type
        Access(AccessTy),

        /// Tuple type
        Tuple(TupleTy),

        /// Array type
        Array(ArrayTy),

        /// Macro invocation on a type.
        Macro(TyMacroInvocation),

        /// A token macro invocation in an type position.
        TokenMacro(TokenMacroInvocation),

        /// Function type
        Fn(FnTy),

        /// Named type, similar to a binding
        Named(NamedTy),

        /// Reference type, the reference type of the inner type
        Ref(RefTy),

        /// Equality between two types.
        Equality(EqualityTy),

        /// Union type, the union of two types
        Union(UnionTy),

        /// Implicit function type
        ImplicitFn(ImplicitFnTy),

        /// Implicit function call
        ImplicitCall(ImplicitFnCall),

        /// An expression within a type in the form of `{ <expr> }`
        Expr(ExprTy)
    }

    /// An array expression, e.g. `[1, 2, 3]`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ArrayExpr {
        /// The elements of the array literal.
        pub elements: Children!(Expr),
    }

    /// A tuple expression, e.g. `(1, 'A', "foo")`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TupleExpr {
        /// The elements of the tuple literal.
        pub elements: Children!(ExprArg),
    }

    /// A string literal.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    #[node]
    pub struct StrLit {
        pub data: AllocId
    }

    /// A character literal.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    #[node]
    pub struct CharLit {
        pub data: char
    }

    /// A byte literal.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    #[node]
    pub struct ByteLit {
        pub data: u8
    }

    /// An integer literal.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    #[node]
    pub struct IntLit {
        /// The raw hunk of text that represents the literal.
        ///
        /// **Note** This span does not include the suffix of the literal, e.g. `i32`.
        pub hunk: Hunk,

        /// The base that specified the integer literal, e.g. `0x` for hexadecimal.
        pub base: Base,

        /// Whether the literal has an ascription
        pub kind: IntLitKind,
    }

    impl IntLit {
        /// Check whether that value is negative.
        ///
        /// **Note**: For raw values, we just check if the value starts with a `-`.
        pub fn is_negative(&self) -> bool {
            self.hunk.span().map_contents(|s| s.starts_with('-'))
        }
    }

    /// A float literal.
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    #[node]
    pub struct FloatLit {
        /// Raw value hunk of the float literal.
        ///
        /// **Note** This span does not include the suffix of the literal, e.g. `f32`.
        pub hunk: Hunk,

        /// Whether the literal has an ascription
        pub kind: FloatLitKind,
    }

    /// A boolean literal.
    #[derive(Debug, PartialEq, Eq, Clone)]
    #[node]
    pub struct BoolLit {
        pub data: bool
    }

    /// A literal.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub enum Lit {
        /// String literals, e.g. `"Viktor"`
        Str(StrLit),
        /// Character literals, e.g. `'c'`
        Char(CharLit),
        /// Integer literals, e.g. `5i32`
        Int(IntLit),
        /// A byte literal, e.g. `b'c'`
        Byte(ByteLit),
        /// Float literals, e.g. `27.4`
        Float(FloatLit),
        /// Boolean literals e.g. `false`
        Bool(BoolLit),
    }

    /// An alternative pattern, e.g. `Red | Blue`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct OrPat {
        /// The variants of the "or" pattern
        pub variants: Children!(Pat),
    }

    /// A conditional pattern, e.g. `x if x == 42`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct IfPat {
        /// The pattern part of the conditional.
        pub pat: Child!(Pat),
        /// The expression part of the conditional.
        pub condition: Child!(Expr),
    }

    /// An construct pattern, e.g. `Some((x, y)), animals::Dog(name = "viktor", age
    /// = 3)`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ConstructorPat {
        /// The subject of the constructor pattern.
        pub subject: Child!(Pat),

        /// The arguments of the constructor pattern.
        pub fields: Children!(PatArg),

        /// If there is a spread argument in the constructor pattern.
        pub spread: OptionalChild!(SpreadPat),
    }

    /// A module pattern entry, e.g. `{..., name as (fst, snd), ...}`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ModulePatEntry {
        /// The name of the field.
        pub name: Child!(Name),
        /// The pattern to match the field's value with.
        pub pat: Child!(Pat),
    }

    /// A module pattern, e.g. `{ fgets, fputs, }`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ModulePat {
        /// The entries of a module pattern
        pub fields: Children!(ModulePatEntry),
    }

    /// A pattern argument with an optional name, pattern value
    /// and optional macro invocations.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct PatArg {
        /// If the tuple pattern entry binds a name to the pattern
        pub name: OptionalChild!(Name),

        /// The pattern that is being applied on the tuple entry
        pub pat: Child!(Pat),

        /// Any applied macro invocations on this argument.
        pub macros: OptionalChild!(MacroInvocations),
    }

    /// A tuple pattern, e.g. `(1, 2, x)`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TuplePat {
        /// The element of the tuple, as patterns.
        pub fields: Children!(PatArg),

        /// If there is a spread argument in the tuple pattern.
        pub spread: OptionalChild!(SpreadPat),
    }

    impl TuplePat {
        /// Function used to check if the pattern is nameless or not. If the pattern
        /// has at least one member that contains a `name` field, then it is
        /// considered to be named.
        pub fn is_nameless_pat(&self) -> bool {
            !self.fields.iter().any(|pat| pat.body().name.is_some())
        }
    }

    /// A array pattern, e.g. `[x, 1, ..]`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ArrayPat {
        pub fields: Children!(Pat),

        /// If there is a spread argument in the tuple pattern.
        pub spread: OptionalChild!(SpreadPat),
    }

    /// A literal pattern, limited to strings, character, floats, and integers, e.g.
    /// `3`, `c`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct LitPat {
        pub data: Child!(Lit)
    }

    /// An access pattern, denoting the access of a property from
    /// another pattern.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct AccessPat {
        /// The subject of the access pattern
        pub subject: Child!(Pat),
        /// The property of the subject to access.
        pub property: Child!(Name),
    }

    /// A pattern name binding.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct BindingPat {
        /// The identifier that the name bind is using
        pub name: Child!(Name),
        /// Visibility of the binding (`priv` by default)
        pub visibility: OptionalChild!(Visibility),
        /// Mutability of the binding (immutable by default)
        pub mutability: OptionalChild!(Mutability),
    }

    /// A pattern spread
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct SpreadPat {
        /// If the spread pattern binds the selected range
        pub name: OptionalChild!(Name),

        /// The position of the spread pattern within parent
        /// pattern.
        pub position: usize,
    }

    /// The wildcard pattern.
    #[derive(Debug, PartialEq, Eq, Clone)]
    #[node]
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
    #[node]
    pub struct RangePat {
        /// Initial bound of the range
        pub lo: OptionalChild!(Lit),

        /// Upper bound of the range
        pub hi: OptionalChild!(Lit),

        /// Whether the `end` is included or not
        pub end: RangeEnd,
    }

    /// A pattern. e.g. `Ok(Dog(props = (1, x)))`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub enum Pat {
        /// An access pattern is one that denotes the access of a property from
        /// another pattern. This is used to denote namespace accesses like
        /// `a::b::c`
        Access(AccessPat),

        /// A simple binding pattern, assign some value to the name of the pattern
        Binding(BindingPat),

        /// A representation of a constructor in the pattern space. Constructors in
        /// patterns can either be enum or struct values. The subject of the
        /// constructor can be either an [`Pat::Access`] or a [`Pat::Binding`].
        Constructor(ConstructorPat),

        /// A macro invocation on a pattern.
        Macro(PatMacroInvocation),

        /// A token macro invocation in an pattern position.
        TokenMacro(TokenMacroInvocation),

        /// Module pattern is used to destructure entries from an import.
        Module(ModulePat),

        /// A tuple pattern is a collection of patterns, e.g `(1, x, 'c')`
        Tuple(TuplePat),

        /// An array pattern, which is a collection of patterns, including spread and
        /// matches an array e.g `[x, 2, y]`
        Array(ArrayPat),

        /// A literal pattern e.g. `c`
        ///
        /// ##Note: `tuple` literal cannot appear within this branch.
        Lit(LitPat),

        /// An `or` pattern which groups multiple patterns and matches one of the
        /// provided patterns e.g. `a | b | c`
        Or(OrPat),

        /// A pattern that is guarded by an if statement, e.g. `x if x > 5`
        If(IfPat),

        /// Wildcard pattern, similar to a binding but it is not bound
        /// to any member.
        Wild(WildPat),

        /// A range pattern which represents an open or closed range of primitives
        /// e.g. `'a'..'z'`, `3..27`... etc
        Range(RangePat),
    }

    /// Enum representing whether a declaration is public or private
    /// within module scope.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    #[node]
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
    #[node]
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
    #[node]
    pub struct ImplicitFnDef {
        /// The type arguments of the function.
        pub params: Child!(TyParams),

        /// Optional return type of the type function
        pub return_ty: OptionalChild!(Ty),

        /// The body of the type function,
        pub fn_body: Child!(Expr),
    }

    /// A declaration, e.g. `x := 3;`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct Declaration {
        /// The pattern to bind the right-hand side to.
        pub pat: Child!(Pat),

        /// Any associated type with the expression
        pub ty: OptionalChild!(Ty),

        /// Any value that is assigned to the binding, simply
        /// an expression.
        pub value: Child!(Expr),
    }

    /// Unary operators that are defined within the core of the language.
    #[derive(Debug, Clone, Copy)]
    #[node]
    pub enum UnOp {
        // Bitwise logical inversion
        BitNot,

        /// Logical inversion.
        Not,

        /// The operator '-' for negation
        Neg,
    }

    impl Display for UnOp {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                UnOp::BitNot => write!(f, "~"),
                UnOp::Not => write!(f, "!"),
                UnOp::Neg => write!(f, "-"),
            }
        }
    }

    /// Binary operators that are defined within the core of the language.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[node]
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
        /// '**'
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

        /// Check whether an operator is a comparator operator, i.e. `==`, `!=`, etc.
        pub fn is_comparator(&self) -> bool {
            matches!(
                self,
                BinOp::EqEq | BinOp::NotEq | BinOp::Gt | BinOp::GtEq | BinOp::Lt | BinOp::LtEq
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
    #[node]
    pub struct AssignExpr {
        /// The left-hand side of the assignment.
        ///
        /// This should resolve to either a variable or a struct field.
        pub lhs: Child!(Expr),
        /// The right-hand side of the assignment.
        ///
        /// The value will be assigned to the left-hand side.
        pub rhs: Child!(Expr),
    }

    /// An assign expression, e.g. `x += 4;`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct AssignOpExpr {
        /// The left-hand side of the assignment.
        ///
        /// This should resolve to either a variable or a struct field.
        pub lhs: Child!(Expr),
        /// The right-hand side of the assignment.
        ///
        /// The value will be assigned to the left-hand side.
        pub rhs: Child!(Expr),

        /// Operator that is applied with the assignment on the lhs with the rhs
        /// value.
        ///
        /// Note: Some binary operators are not allowed to be in the location.
        pub operator: Child!(BinOp),
    }

    /// A struct definition, e.g:
    /// ```ignore
    /// Foo := struct<T>( index: i32, val: T );
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct StructDef {
        /// Type parameters that are attached to the definition.
        pub ty_params: OptionalChild!(TyParams),

        /// The fields of the struct, in the form of [Param].
        pub fields: Child!(Params),
    }

    /// A variant of an enum definition, e.g. `Some(T)`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct EnumDefEntry {
        /// The name of the enum variant.
        pub name: Child!(Name),

        /// The parameters of the enum variant, if any.
        pub fields: OptionalChild!(Params),

        /// The type of the enum variant, if any.
        pub ty: OptionalChild!(Ty),

        /// Any macro invocations that occur on the enum variant.
        pub macros: OptionalChild!(MacroInvocations),
    }

    /// An enum definition, e.g.
    /// ```ignore
    /// enum<T> (
    ///     Some(T),
    ///     None
    /// )
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct EnumDef {
        /// Type parameters that are attached to the definition.
        pub ty_params: OptionalChild!(TyParams),

        /// The variants of the enum, in the form of [EnumDefEntry].
        pub entries: Children!(EnumDefEntry),
    }

    /// A return statement.
    ///
    /// Has an optional return expression, which becomes `void` if [None] is given.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ReturnStatement {
        pub expr: OptionalChild!(Expr)
    }

    /// Break statement (only in loop context).
    #[derive(Debug, PartialEq, Eq, Clone)]
    #[node]
    pub struct BreakStatement;

    /// Continue statement (only in loop context).
    #[derive(Debug, PartialEq, Eq, Clone)]
    #[node]
    pub struct ContinueStatement;

    /// A branch/"case" of a `match` block.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct MatchCase {
        /// The pattern of the `match` case.
        pub pat: Child!(Pat),
        /// The expression corresponding to the match case.
        ///
        /// Will be executed if the pattern succeeds.
        pub expr: Child!(Expr),

        /// Any macro invocations that occur on this match case.
        pub macros: OptionalChild!(MacroInvocations),
    }

    impl MatchCase {
        /// Check if the pattern of the case is an `if-pattern`
        pub fn has_if_pat(&self) -> bool {
            matches!(self.pat.body(), Pat::If(_))
        }
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
    #[node]
    pub struct MatchBlock {
        /// The expression to match on.
        pub subject: Child!(Expr),
        /// The match cases to execute.
        pub cases: Children!(MatchCase),
        /// Whether the match block represents a for, while, if or match statement
        pub origin: MatchOrigin,
    }

    /// A body block.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct BodyBlock {
        /// Zero or more statements.
        pub statements: Children!(Expr),
        /// Zero or one expression.
        pub expr: OptionalChild!(Expr),
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
    #[node]
    pub struct LoopBlock {
        pub contents: Child!(Block)
    }

    /// A for-loop block e.g. `for pat in iterator { ...body... }`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ForLoopBlock {
        /// The pattern that de-structures the operator
        pub pat: Child!(Pat),
        /// The iterator of the for loop, goes after the `in`
        pub iterator: Child!(Expr),
        /// The body of the for-loop
        pub for_body: Child!(Block),
    }

    /// A `while` loop, e.g. `while x > 2 { ... }`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct WhileLoopBlock {
        /// The condition of the the `while` loop.
        pub condition: Child!(Expr),
        /// The body of the `while` loop.
        pub while_body: Child!(Block),
    }

    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct IfClause {
        /// The condition of the `if` block.
        pub condition: Child!(Expr),
        /// The body of the `if-statement`
        pub if_body: Child!(Block),
    }

    /// An `if` block consisting of the condition, block and an optional else clause
    /// e.g. `if x { ... } else { y }`
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct IfBlock {
        pub clauses: Children!(IfClause),
        /// The else clause.
        pub otherwise: OptionalChild!(Block),
    }

    /// A `mod` definition block, e.g.
    ///
    /// ```ignore
    /// mod {
    ///     foo := () -> char => {
    ///     };
    /// }
    /// ```
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ModDef {
        /// Any type parameters that are applied to the `mod` block.
        pub ty_params: OptionalChild!(TyParams),

        /// The actual contents of the block.
        pub entries: Children!(Expr),
    }

    /// A block.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
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
    }

    impl Block {
        pub fn as_str(&self) -> &str {
            match self {
                Block::Match(_) => "match(..)",
                Block::Loop(_) => "loop(..)",
                Block::For(_) => "for(..)",
                Block::While(_) => "while(..)",
                Block::If(_) => "if(..)",
                Block::Body(_) => "body(..)",
            }
        }
    }

    /// A parameter list, e.g. `(a: i32, b := 'c')`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct Params {
        /// The parameters.
        pub params: Children!(Param),

        /// The origin of the type parameters.
        pub origin: ParamOrigin,
    }

    /// This enum describes the origin kind of the subject that a parameter
    /// unification occurred on.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum ParamOrigin {
        /// Parameters came from a tuple expression or a tuple type.
        Tuple,

        /// Parameters came from a struct
        Struct,

        /// Parameters came from a function definition or a function type.
        Fn,

        /// Parameters came from a function call
        FnCall,

        /// Parameters came from an enum variant initialisation
        EnumVariant,
    }

    impl ParamOrigin {
        pub fn is_item_def(&self) -> bool {
            matches!(self, ParamOrigin::Fn | ParamOrigin::EnumVariant)
        }

        /// Get the name of the `field` that the [ParamOrigin] refers to.
        /// In other words, what is the name for the parameters that are
        /// associated with the [ParamOrigin].
        pub fn field_name(&self) -> &'static str {
            match self {
                ParamOrigin::Fn => "parameter",
                ParamOrigin::FnCall => "argument",
                ParamOrigin::Tuple |
                ParamOrigin::Struct |
                ParamOrigin::EnumVariant => "field",
            }
        }
    }

    impl Display for ParamOrigin {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                ParamOrigin::Tuple => write!(f, "tuple"),
                ParamOrigin::Struct => write!(f, "struct"),
                ParamOrigin::Fn | ParamOrigin::FnCall => write!(f, "function"),
                ParamOrigin::EnumVariant => write!(f, "enum variant"),
            }
        }
    }

    /// A function parameter, struct or enum field.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct Param {
        /// The name of the argument.
        pub name: OptionalChild!(Name),

        /// The type of the argument, if any.
        pub ty: OptionalChild!(Ty),

        /// Default value of the argument if provided.
        ///
        /// If the value is provided, this makes it a named argument
        /// which means that they can be specified by putting the name of the
        /// argument.
        pub default: OptionalChild!(Expr),

        /// Any macros are invoked on the parameter.
        pub macros: OptionalChild!(MacroInvocations),
    }

    /// A type parameter list, e.g. `<T, U: Conv<U>>`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TyParams {
        /// The type parameters.
        pub params: Children!(TyParam),

        /// The origin of the type parameters.
        pub origin: TyParamOrigin,
    }

    /// A function parameter, struct or enum field.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TyParam {
        /// The name of the argument.
        pub name: OptionalChild!(Name),

        /// The type of the argument, if any.
        pub ty: OptionalChild!(Ty),

        /// Default value of the argument if provided.
        ///
        /// If the value is provided, this makes it a named argument
        /// which means that they can be specified by putting the name of the
        /// argument.
        pub default: OptionalChild!(Ty),

        /// Any macros are invoked on the parameter.
        pub macros: OptionalChild!(MacroInvocations),
    }

    /// Represents what the origin of a definition is. This is useful
    /// for when emitting warnings that might occur in the same way
    /// as the ret of these constructs.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum TyParamOrigin {
        /// This is a type function definition,
        ImplicitFn,

        /// The definition is a `struct`.
        Struct,

        /// The definition is a `enum`.
        Enum,

        /// The definition is a `mod` block.
        Mod,
    }

    impl TyParamOrigin {
        /// Get the name of origin of the type parameter.
        pub fn name(&self) -> &'static str {
            match self {
                TyParamOrigin::ImplicitFn => "implicit function",
                TyParamOrigin::Struct => "struct",
                TyParamOrigin::Enum => "enum",
                TyParamOrigin::Mod => "mod",
            }
        }
    }

    /// A function definition.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct FnDef {
        /// The parameters of the function definition.
        pub params: Child!(Params),

        /// The return type of the function definition.
        ///
        /// Will be inferred if [None].
        pub return_ty: OptionalChild!(Ty),

        /// The body/contents of the function, in the form of an expression.
        pub fn_body: Child!(Expr),
    }

    /// Generic argument with a optional name, expression and optional
    /// macro invocations on the argument itself.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ExprArg {
        /// Optional name for the function argument, e.g `f(x = 3);`.
        pub name: OptionalChild!(Name),

        /// Each argument of the function call, as an expression.
        pub value: Child!(Expr),

        /// Any macros are invoked on the parameter.
        pub macros: OptionalChild!(MacroInvocations),
    }

    /// A constructor call expression. This can either be a function
    /// call, a struct instantiation or a enum variant instantiation.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct CallExpr {
        /// An expression which evaluates to a function value.
        pub subject: Child!(Expr),

        /// Arguments to the function, a list of [ExprArg]s.
        pub args: Children!(ExprArg),
    }

    /// A the kind of access an [AccessExpr] has
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    #[node]
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
    #[node]
    pub enum PropertyKind {
        /// A named field like
        NamedField(Identifier),

        /// The numeric value of the index that's being accessed
        NumericField(u32),
    }

    /// A property access expression.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct AccessExpr {
        /// An expression which evaluates to a struct or tuple value.
        pub subject: Child!(Expr),
        /// The property of the subject to access.
        pub property: Child!(PropertyKind),
        /// The kind of access, either namespacing or property
        pub kind: AccessKind,
    }

    /// A typed expression, e.g. `foo as int`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct CastExpr {
        /// The annotated type of the expression.
        pub ty: Child!(Ty),
        /// The expression being typed.
        pub expr: Child!(Expr),
    }

    /// Represents a path to a module, given as a string literal to an `import`
    /// call.
    #[derive(Debug, PartialEq, Eq, Clone)]
    #[node]
    pub struct Import {
        pub path: AllocId,
        pub source: SourceId,
    }

    /// A variable expression.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct VariableExpr {
        /// The name of the variable.
        pub name: Child!(Name),
    }

    /// A reference expression with a flag denoting whether it is a raw ref or not
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct RefExpr {
        pub inner_expr: Child!(Expr),
        /// The kind of reference, either being a normal reference or a `raw`
        /// reference
        pub kind: RefKind,
        /// Mutability modifier on the expression.
        pub mutability: OptionalChild!(Mutability),
    }

    /// A dereference expression.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct TyExpr {
        pub ty: Child!(Ty)
    }

    /// A dereference expression.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct DerefExpr {
        pub data: Child!(Expr)
    }

    /// An unsafe expression.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct UnsafeExpr {
        pub data: Child!(Expr)
    }

    /// A literal.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct LitExpr {
        pub data: Child!(Lit)
    }

    /// A block.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct BlockExpr {
        pub data: Child!(Block)
    }

    /// An `import` call.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct ImportExpr {
        pub data: Child!(Import)
    }

    /// A binary expression `2 + 2`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct BinaryExpr {
        /// left hand-side of the binary expression
        pub lhs: Child!(Expr),
        /// right hand-side of the binary expression
        pub rhs: Child!(Expr),
        /// The unary operator of the [BinaryExpr]
        pub operator: Child!(BinOp),
    }

    /// A unary expression `!a`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct UnaryExpr {
        /// The expression that the unary operator is applied to
        pub expr: Child!(Expr),
        /// The unary operator of the [UnaryExpr]
        pub operator: Child!(UnOp),
    }

    /// An index expression `arr[x]`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct IndexExpr {
        /// The subject that is being indexed.
        pub subject: Child!(Expr),
        /// The expression that is the index.
        pub index_expr: Child!(Expr),
    }

    /// A repeat expression `[x; 5]`.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct RepeatExpr {
        /// The subject that is being repeated.
        pub subject: Child!(Expr),

        /// The constant specifying the number of repeats of the subject.
        pub repeat: Child!(Expr),
    }

    /// An expression.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub enum Expr {
        /// A constructor call which could be a struct/enum initialisation or a
        /// function call e.g. `foo(5)`.
        Call(CallExpr),

        /// A call to an implicit function, i.e. `cast<_, u32>(5)`.
        ImplicitCall(ImplicitFnCall),

        /// A macro invocation on an expression.
        Macro(ExprMacroInvocation),

        /// A token macro invocation in an expression position.
        TokenMacro(TokenMacroInvocation),

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
        Lit(LitExpr),

        /// Array expressions, e.g. `[1, 2, x + 4]`
        Array(ArrayExpr),

        /// Tuple expressions, e.g. `(1, a, 3)`
        Tuple(TupleExpr),

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

        /// Implicit function definition e.g. `<T> => ...`
        ImplicitFnDef(ImplicitFnDef),

        /// A `mod` definition e.g. `mod { ... }`
        ModDef(ModDef),

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

        /// An expression that specifies that an operand is to be
        /// repeated a certain number of times, e.g. `[1; 5]`.
        Repeat(RepeatExpr),

        /// An expression that captures a variable or a pattern being assigned
        /// to a right hand-side expression such as `x = 3`.
        Assign(AssignExpr),

        /// An expression that captures a variable or a pattern being assigned with
        /// the application of a binary operator, such as `x += 3`.
        AssignOp(AssignOpExpr),

        /// Binary Expression composed of a left and right hand-side with a binary
        /// operator
        BinaryExpr(BinaryExpr),

        /// Unary Expression composed of a unary operator and an expression
        UnaryExpr(UnaryExpr),
    }

    /// A module.
    ///
    /// Represents a parsed `.hash` file.
    #[derive(Debug, PartialEq, Clone)]
    #[node]
    pub struct Module {
        /// The contents of the module, as a list of expressions terminated with a
        /// semi-colon.
        pub contents: Children!(Expr),

        /// Any kind of top level invocations of macros and applications of attributes, i.e.
        ///
        /// ```ignore
        /// #![feature(some_cool_feat)]
        /// ```
        pub macros: Child!(MacroInvocations),
    }
}

#[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
mod size_asserts {
    use hash_utils::assert::static_assert_size;

    use super::*;

    static_assert_size!(Expr, 56);
    static_assert_size!(Pat, 56);
    static_assert_size!(Ty, 56);
}
