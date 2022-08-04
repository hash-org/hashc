//! Frontend-agnostic Hash AST (abstract syntax tree) type definitions.

use hash_source::{identifier::Identifier, location::Span, string::Str};
use hash_utils::counter;
use replace_with::replace_with_or_abort;
use std::{
    fmt::Display,
    hash::Hash,
    ops::{Deref, DerefMut},
    path::PathBuf,
};

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
    body: Box<T>,
    span: Span,
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
    /// A reference to the body of the node.
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
    /// Get a reference to the reference contained within this node.
    pub fn body(&self) -> &T {
        self.body
    }

    pub fn with_body<'u, U>(&self, body: &'u U) -> AstNodeRef<'u, U> {
        AstNodeRef { body, span: self.span, id: self.id }
    }

    /// Get the [Span] of this node in the input.
    pub fn span(&self) -> Span {
        self.span
    }

    /// Get the ID of this node.
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
    body: &'t mut T,
    pub span: Span,
    pub id: AstNodeId,
}

impl<'t, T> AstNodeRefMut<'t, T> {
    pub fn new(body: &'t mut T, span: Span, id: AstNodeId) -> Self {
        AstNodeRefMut { body, span, id }
    }

    /// Get a reference to the reference contained within this node.
    pub fn body(&self) -> &T {
        self.body
    }

    pub fn with_body<'u, U>(&self, body: &'u mut U) -> AstNodeRefMut<'u, U> {
        AstNodeRefMut { body, span: self.span, id: self.id }
    }

    /// Function to replace the body of the node with a newly generated body
    pub fn replace(&mut self, f: impl FnOnce(T) -> T) {
        replace_with_or_abort(self.body, f);
    }

    /// Get a mutable reference to the reference contained within this node.
    pub fn body_mut(&mut self) -> &mut T {
        self.body
    }

    /// Get the [Span] of this node in the input.
    pub fn span(&self) -> Span {
        self.span
    }

    /// Get the ID of this node.
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
    fn node(&self) -> &AstNode<T>;
    fn node_mut(&mut self) -> &mut AstNode<T>;

    fn node_ref(&self) -> AstNodeRef<T> {
        self.node().ast_ref()
    }

    fn node_ref_mut(&mut self) -> AstNodeRefMut<T> {
        self.node_mut().ast_ref_mut()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct AstNodes<T> {
    pub nodes: Vec<AstNode<T>>,

    /// The span of the AST nodes if one is available,
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

/// A single name/symbol.
#[derive(Hash, Debug, Clone, Copy)]
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
    pub entries: AstNodes<TyArg>,
}

/// The list type, , e.g. `{str}`.
#[derive(Debug, PartialEq, Clone)]
pub struct ListTy {
    pub inner: AstNode<Ty>,
}

/// The set type, , e.g. `{str}`.
#[derive(Debug, PartialEq, Clone)]
pub struct SetTy {
    pub inner: AstNode<Ty>,
}

/// The map type, e.g. `{str: u32}`.
#[derive(Debug, PartialEq, Clone)]
pub struct MapTy {
    pub key: AstNode<Ty>,
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
    pub subject: AstNode<Expr>,
    pub args: AstNodes<TyArg>,
}

/// A merge type meaning that multiple types are considered to be
/// specified in place of one, e.g. `Conv ~ Eq`
#[derive(Debug, PartialEq, Clone)]
pub struct MergeTy {
    pub lhs: AstNode<Ty>,
    pub rhs: AstNode<Ty>,
}

/// A union type meaning that multiple types are accepted, e.g. `f64 | i64`
#[derive(Debug, PartialEq, Clone)]
pub struct UnionTy {
    pub lhs: AstNode<Ty>,
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
    pub name: Option<AstNode<Name>>,
    pub ty: Option<AstNode<Ty>>,
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
    pub key: AstNode<Expr>,
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
pub struct StrLit(pub Str);

/// A character literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CharLit(pub char);

/// An integer literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IntLit(pub u64);

/// A float literal.
#[derive(Debug, PartialEq, Clone)]
pub struct FloatLit(pub f64);

/// A boolean literal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BoolLit(pub bool);

/// A literal.
#[derive(Debug, PartialEq, Clone)]
pub enum Lit {
    Str(StrLit),
    Char(CharLit),
    Int(IntLit),
    Float(FloatLit),
    Bool(BoolLit),
    Set(SetLit),
    Map(MapLit),
    List(ListLit),
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
    /// The arguments of the enum variant as patterns.
    pub fields: AstNodes<TuplePatEntry>,
}

/// A module pattern entry, e.g. `{..., name: (fst, snd), ...}`.
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
    pub name: Option<AstNode<Name>>,
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

/// A string literal pattern.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StrLitPat(pub Str);

/// A character literal pattern.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CharLitPat(pub char);

/// An integer literal pattern.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IntLitPat(pub u64);

/// A float literal pattern.
#[derive(Debug, PartialEq, Clone)]
pub struct FloatLitPat(pub f64);

/// A boolean literal pattern.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BoolLitPat(pub bool);

/// A literal pattern, e.g. `1`, `3.4`, `"foo"`, `false`.
#[derive(Debug, PartialEq, Clone)]
pub enum LitPat {
    Str(StrLitPat),
    Char(CharLitPat),
    Int(IntLitPat),
    Float(FloatLitPat),
    Bool(BoolLitPat),
}

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
    pub name: Option<AstNode<Name>>,
}

/// The catch-all, i.e "ignore" pattern.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IgnorePat;

/// A pattern. e.g. `Ok(Dog {props = (1, x)})`.
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
    List(ListPat),
    Lit(LitPat),
    Or(OrPat),
    If(IfPat),
    Ignore(IgnorePat),
    Spread(SpreadPat),
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
/// impl { ... };`.
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
#[derive(Debug, Clone, PartialEq, Eq)]
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

/// A struct definition, e.g. `struct Foo = { bar: int; };`.
#[derive(Debug, PartialEq, Clone)]
pub struct StructDef {
    /// The fields of the struct, in the form of [Param].
    pub entries: AstNodes<Param>,
}

/// A variant of an enum definition, e.g. `Some(T)`.
#[derive(Debug, PartialEq, Clone)]
pub struct EnumDefEntry {
    /// The name of the enum variant.
    pub name: AstNode<Name>,
    /// The arguments of the enum variant, if any.
    pub args: AstNodes<Ty>,
}

/// An enum definition, e.g. `enum Option = <T> => { Some(T); None; };`.
#[derive(Debug, PartialEq, Clone)]
pub struct EnumDef {
    /// The variants of the enum, in the form of [EnumDefEntry].
    pub entries: AstNodes<EnumDefEntry>,
}

/// A trait definition, e.g. `add := <T> => trait { add: (T, T) -> T; }`.
#[derive(Debug, PartialEq, Clone)]
pub struct TraitDef {
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

/// The origin of a match block
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum MatchOrigin {
    If,
    Match,
    For,
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

#[derive(Debug, PartialEq, Clone)]
pub struct LoopBlock(pub AstNode<Block>);

#[derive(Debug, PartialEq, Clone)]
pub struct ForLoopBlock {
    pub pat: AstNode<Pat>,
    pub iterator: AstNode<Expr>,
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

#[derive(Debug, PartialEq, Clone)]
pub struct ModBlock(pub AstNode<BodyBlock>);

#[derive(Debug, PartialEq, Clone)]
pub struct ImplBlock(pub AstNode<BodyBlock>);

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
    /// A module block. The inner block becomes an inner module of the current
    /// module.
    Mod(ModBlock),
    /// A body block.
    Body(BodyBlock),
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
    Tuple,
    Struct,
    Fn,
    TyFn,
    EnumVariant,
    /// List pattern parameters, the parameters are all the same, but it's
    /// used to represent the inner terms of the list pattern since spread
    /// patterns may become named parameters.
    ListPat,
    /// Module pattern
    ModulePat,
}

impl Display for ParamOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParamOrigin::Unknown => write!(f, "unknown"),
            ParamOrigin::Tuple => write!(f, "tuple"),
            ParamOrigin::Struct => write!(f, "struct"),
            ParamOrigin::Fn => write!(f, "function"),
            ParamOrigin::TyFn => write!(f, "type function"),
            ParamOrigin::EnumVariant => write!(f, "enum variant"),
            ParamOrigin::ListPat => write!(f, "list pattern"),
            ParamOrigin::ModulePat => write!(f, "module pattern"),
        }
    }
}

/// A function definition parameter.
#[derive(Debug, PartialEq, Clone)]
pub struct Param {
    /// The name of the argument.
    pub name: AstNode<Name>,
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

/// Function call arguments.
#[derive(Debug, PartialEq, Clone)]
pub struct ConstructorCallArgs {
    pub entries: AstNodes<ConstructorCallArg>,
}

/// A constructor call expression. This can either be a function
/// call, a struct instantiation or a enum variant instantiation.
#[derive(Debug, PartialEq, Clone)]
pub struct ConstructorCallExpr {
    /// An expression which evaluates to a function value.
    pub subject: AstNode<Expr>,
    /// Arguments to the function, in the form of [ConstructorCallArgs].
    pub args: AstNode<ConstructorCallArgs>,
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

/// A property access expression.
#[derive(Debug, PartialEq, Clone)]
pub struct AccessExpr {
    /// An expression which evaluates to a struct or tuple value.
    pub subject: AstNode<Expr>,
    /// The property of the subject to access.
    pub property: AstNode<Name>,
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
    pub path: Str,
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
    pub implementation: AstNodes<Expr>,
}

/// A binary expression `2 + 2`.
#[derive(Debug, PartialEq, Clone)]
pub struct BinaryExpr {
    pub lhs: AstNode<Expr>,
    pub rhs: AstNode<Expr>,
    pub operator: AstNode<BinOp>,
}

/// A unary expression `!a`.
#[derive(Debug, PartialEq, Clone)]
pub struct UnaryExpr {
    pub expr: AstNode<Expr>,
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
    ConstructorCall(ConstructorCallExpr),
    Directive(DirectiveExpr),
    Declaration(Declaration),
    Variable(VariableExpr),
    /// Either a property access or a namespace access
    Access(AccessExpr),
    Ref(RefExpr),
    Deref(DerefExpr),
    Unsafe(UnsafeExpr),
    LitExpr(LitExpr),
    Cast(CastExpr),
    Block(BlockExpr),
    Import(ImportExpr),
    StructDef(StructDef),
    EnumDef(EnumDef),
    TyFnDef(TyFnDef),
    TraitDef(TraitDef),
    FnDef(FnDef),
    Ty(TyExpr),
    Return(ReturnStatement),
    Break(BreakStatement),
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
    /// trait/struct to an already declared item, such as `x ~= impl { ... }`
    MergeDeclaration(MergeDeclaration),
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
