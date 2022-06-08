//! Frontend-agnostic Hash AST (abstract syntax tree) type definitions.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use crate::ident::Identifier;
use crate::literal::StringLiteral;
use hash_alloc::brick::Brick;
use hash_alloc::collections::row::Row;
use hash_alloc::{row, Wall};
use hash_source::location::Span;
use hash_utils::counter;
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;
use std::{fmt::Display, hash::Hash};

counter! {
    name: AstNodeId,
    counter_name: AST_NODE_ID_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

/// Represents an abstract syntax tree node.
///
/// Contains an inner type, as well as begin and end positions in the input.
#[derive(Debug)]
pub struct AstNode<'c, T> {
    body: Brick<'c, T>,
    span: Span,
    id: AstNodeId,
}

impl<T> PartialEq for AstNode<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<'c, T> AstNode<'c, T> {
    /// Create a new node with a given body and location.
    pub fn new(body: T, span: Span, wall: &Wall<'c>) -> Self {
        Self {
            body: Brick::new(body, wall),
            span,
            id: AstNodeId::new(),
        }
    }

    /// Get a reference to the value contained within this node.
    pub fn body(&self) -> &T {
        self.body.as_ref()
    }

    pub fn body_mut(&mut self) -> &mut T {
        self.body.as_mut()
    }

    /// Take the value contained within this node.
    pub fn into_body(self) -> Brick<'c, T> {
        self.body
    }

    pub fn ast_ref(&self) -> AstNodeRef<T> {
        AstNodeRef {
            body: self.body.as_ref(),
            span: self.span,
            id: self.id,
        }
    }

    pub fn with_body<'u, U>(&self, body: &'u U) -> AstNodeRef<'u, U> {
        AstNodeRef {
            body,
            span: self.span,
            id: self.id,
        }
    }

    /// Get the location of this node in the input.
    pub fn span(&self) -> Span {
        self.span
    }

    /// Get the ID of this node.
    pub fn id(&self) -> AstNodeId {
        self.id
    }
}

#[derive(Debug)]
pub struct AstNodeRef<'t, T> {
    body: &'t T,
    span: Span,
    id: AstNodeId,
}

impl<T> Clone for AstNodeRef<'_, T> {
    fn clone(&self) -> Self {
        Self {
            body: self.body,
            span: self.span,
            id: self.id,
        }
    }
}

impl<T> Copy for AstNodeRef<'_, T> {}

impl<'t, T> AstNodeRef<'t, T> {
    /// Get a reference to the reference contained within this node.
    pub fn body(&self) -> &T {
        self.body
    }

    pub fn with_body<'u, U>(&self, body: &'u U) -> AstNodeRef<'u, U> {
        AstNodeRef {
            body,
            span: self.span,
            id: self.id,
        }
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

#[derive(Debug, PartialEq)]
pub struct AstNodes<'c, T> {
    pub nodes: Row<'c, AstNode<'c, T>>,

    /// The span of the AST nodes if one is available,
    pub span: Option<Span>,
}

#[macro_export]
macro_rules! ast_nodes {
    () => {
        $crate::ast::AstNodes::new(hash_alloc::collections::row::Row::new(), None)
    };
    ($wall:expr) => {
        $crate::ast::AstNodes::new(hash_alloc::collections::row::Row::new(), None)
    };
    ($wall:expr; $($item:expr),*) => {
        $crate::ast::AstNodes::new(hash_alloc::collections::row::Row::from_iter([$($item,)*], $wall), None)
    };
    ($wall:expr; $($item:expr,)*) => {
        $crate::ast::AstNodes::new(hash_alloc::collections::row::Row::from_iter([$($item,)*], $wall), None)
    };
    ($wall:expr; $item:expr; $count:expr) => {
        $crate::ast::AstNodes::new(hash_alloc::collections::row::Row::from_iter(std::iter::repeat($item).take($count), $wall), None)
    };
}

impl<'c, T> AstNodes<'c, T> {
    pub fn empty() -> Self {
        Self {
            nodes: row![],
            span: None,
        }
    }

    pub fn new(nodes: Row<'c, AstNode<'c, T>>, span: Option<Span>) -> Self {
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
        self.span
            .or_else(|| Some(self.nodes.first()?.span().join(self.nodes.last()?.span())))
    }
}

impl<'c, T> Deref for AstNodes<'c, T> {
    type Target = [AstNode<'c, T>];
    fn deref(&self) -> &Self::Target {
        &*self.nodes
    }
}
impl<'c, T> DerefMut for AstNodes<'c, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.nodes
    }
}

/// [AstNode] dereferences to its inner `body` type.
impl<T> Deref for AstNode<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.body()
    }
}

/// [AstNode] dereferences to its inner `body` type.
impl<T> DerefMut for AstNode<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.body_mut()
    }
}

/// A single name/symbol.
#[derive(Hash, PartialEq, Eq, Debug)]
pub struct Name {
    // The name of the symbol.
    pub ident: Identifier,
}

/// A namespaced name, i.e. access name.
#[derive(Debug, PartialEq)]
pub struct AccessName<'c> {
    /// The list of names that make up the access name.
    pub path: AstNodes<'c, Identifier>,
}

impl AccessName<'_> {
    pub fn path(&self) -> Vec<Identifier> {
        self.path
            .iter()
            .map(|part| *part.body())
            .collect::<Vec<_>>()
    }

    pub fn path_with_locations(&self) -> Vec<(Identifier, Span)> {
        self.path
            .iter()
            .map(|part| (*part.body(), part.span()))
            .collect::<Vec<_>>()
    }
}

/// A concrete/"named" type.
#[derive(Debug, PartialEq)]
pub struct NamedType<'c> {
    /// The name of the type.
    pub name: AstNode<'c, AccessName<'c>>,
}

/// Reference kind representing either a raw reference or a normal reference.
#[derive(Debug, PartialEq, Eq)]
pub enum RefKind {
    /// Raw reference type
    Raw,
    /// Normal reference type
    Normal,
}

/// A reference type.
#[derive(Debug, PartialEq)]
pub struct RefType<'c> {
    /// Inner type of the reference type
    pub inner: AstNode<'c, Type<'c>>,
    /// Whether this reference is a `raw` reference or normal reference (normal by default).
    pub kind: Option<AstNode<'c, RefKind>>,
    /// Mutability of the reference (immutable by default)
    pub mutability: Option<AstNode<'c, Mutability>>,
}

/// The existential type (`?`).
#[derive(Debug, PartialEq, Eq)]
pub struct ExistentialType;

/// The type infer operator.
#[derive(Debug, PartialEq, Eq)]
pub struct InferType;

/// An entry within a tuple type.
#[derive(Debug, PartialEq)]
pub struct NamedFieldTypeEntry<'c> {
    pub name: Option<AstNode<'c, Name>>,
    pub ty: AstNode<'c, Type<'c>>,
}

/// The tuple type.
#[derive(Debug, PartialEq)]
pub struct TupleType<'c> {
    pub entries: AstNodes<'c, NamedFieldTypeEntry<'c>>,
}

/// The list type, , e.g. `{str}`.
#[derive(Debug, PartialEq)]
pub struct ListType<'c> {
    pub inner: AstNode<'c, Type<'c>>,
}

/// The set type, , e.g. `{str}`.
#[derive(Debug, PartialEq)]
pub struct SetType<'c> {
    pub inner: AstNode<'c, Type<'c>>,
}

/// The grouped type (essentially a type within parenthesees), e.g. `(str)`. It
/// differs from a tuple that it does not contain a trailing comma which signifies that
/// this is a single element tuple.
#[derive(Debug, PartialEq)]
pub struct GroupedType<'c>(pub AstNode<'c, Type<'c>>);

/// The map type, e.g. `{str: u32}`.
#[derive(Debug, PartialEq)]
pub struct MapType<'c> {
    pub key: AstNode<'c, Type<'c>>,
    pub value: AstNode<'c, Type<'c>>,
}

/// The function type.
#[derive(Debug, PartialEq)]
pub struct FnType<'c> {
    pub args: AstNodes<'c, NamedFieldTypeEntry<'c>>,
    pub return_ty: AstNode<'c, Type<'c>>,
}

/// A [TypeFunctionParam] is a parameter that appears within a [TypeFunction]. This specifies
/// that the type function takes a particular parameter with a specific name, a bound and a default
/// value.
#[derive(Debug, PartialEq)]
pub struct TypeFunctionParam<'c> {
    pub name: AstNode<'c, Name>,
    pub bound: Option<AstNode<'c, Type<'c>>>,
    pub default: Option<AstNode<'c, Type<'c>>>,
}

/// A type function e.g. `<T = u32, E: Conv ~ Eq> -> Result<T, E>`
#[derive(Debug, PartialEq)]
pub struct TypeFunction<'c> {
    pub args: AstNodes<'c, TypeFunctionParam<'c>>,
    pub return_ty: AstNode<'c, Type<'c>>,
}

/// A type function call specifies a call to a type function with the specified
/// function name in the form of a [Type] (which can only be a [NamedType] or a [GroupedType])
/// and then followed by arguments. For example: `Conv<u32>` or `(Foo<bar>)<baz>`
#[derive(Debug, PartialEq)]
pub struct TypeFunctionCall<'c> {
    pub subject: AstNode<'c, Type<'c>>,
    pub args: AstNodes<'c, NamedFieldTypeEntry<'c>>,
}

/// A merged type meaning that multiple types are considered to be
/// specified in place of one, e.g. `Conv ~ Eq ~ Print`
#[derive(Debug, PartialEq)]
pub struct MergedType<'c>(pub AstNodes<'c, Type<'c>>);

/// A type.
#[derive(Debug, PartialEq)]
pub enum Type<'c> {
    Tuple(TupleType<'c>),
    List(ListType<'c>),
    Set(SetType<'c>),
    Map(MapType<'c>),
    Fn(FnType<'c>),
    Named(NamedType<'c>),
    Ref(RefType<'c>),
    Merged(MergedType<'c>),
    TypeFunction(TypeFunction<'c>),
    TypeFunctionCall(TypeFunctionCall<'c>),
}

/// A set literal, e.g. `{1, 2, 3}`.
#[derive(Debug, PartialEq)]
pub struct SetLiteral<'c> {
    /// The elements of the set literal.
    pub elements: AstNodes<'c, Expression<'c>>,
}

/// A list literal, e.g. `[1, 2, 3]`.
#[derive(Debug, PartialEq)]
pub struct ListLiteral<'c> {
    /// The elements of the list literal.
    pub elements: AstNodes<'c, Expression<'c>>,
}

/// An entry within a tuple type, which may contain an optional name
/// annotation and or a type annotation, for example:
///
/// ```text
/// (foo : u32 = 2, ..., k = 2)
///  ^^^   ^^^   ^
/// name   type  value
/// ```
#[derive(Debug, PartialEq)]
pub struct TupleLiteralEntry<'c> {
    pub name: Option<AstNode<'c, Name>>,
    pub ty: Option<AstNode<'c, Type<'c>>>,
    pub value: AstNode<'c, Expression<'c>>,
}

/// A tuple literal, e.g. `(1, 'A', "foo")`.
#[derive(Debug, PartialEq)]
pub struct TupleLiteral<'c> {
    /// The elements of the tuple literal.
    pub elements: AstNodes<'c, TupleLiteralEntry<'c>>,
}

/// A map literal entry, e.g. `"foo": 1`.
#[derive(Debug, PartialEq)]
pub struct MapLiteralEntry<'c> {
    pub key: AstNode<'c, Expression<'c>>,
    pub value: AstNode<'c, Expression<'c>>,
}

/// A map literal, e.g. `{"foo": 1, "bar": 2}`.
#[derive(Debug, PartialEq)]
pub struct MapLiteral<'c> {
    /// The elements of the map literal (key-value pairs).
    pub elements: AstNodes<'c, MapLiteralEntry<'c>>,
}

/// A string literal.
#[derive(Debug, PartialEq, Eq)]
pub struct StrLiteral(pub StringLiteral);

/// A character literal.
#[derive(Debug, PartialEq, Eq)]
pub struct CharLiteral(pub char);

/// An integer literal.
#[derive(Debug, PartialEq, Eq)]
pub struct IntLiteral(pub u64);

/// A float literal.
#[derive(Debug, PartialEq)]
pub struct FloatLiteral(pub f64);

/// A boolean literal.
#[derive(Debug, PartialEq, Eq)]
pub struct BoolLiteral(pub bool);

/// A literal.
#[derive(Debug, PartialEq)]
pub enum Literal<'c> {
    Str(StrLiteral),
    Char(CharLiteral),
    Int(IntLiteral),
    Float(FloatLiteral),
    Bool(BoolLiteral),
    Set(SetLiteral<'c>),
    Map(MapLiteral<'c>),
    List(ListLiteral<'c>),
    Tuple(TupleLiteral<'c>),
}

/// An alternative pattern, e.g. `Red | Blue`.
#[derive(Debug, PartialEq)]
pub struct OrPattern<'c> {
    /// The variants of the "or" pattern
    pub variants: AstNodes<'c, Pattern<'c>>,
}

/// A conditional pattern, e.g. `x if x == 42`.
#[derive(Debug, PartialEq)]
pub struct IfPattern<'c> {
    /// The pattern part of the conditional.
    pub pattern: AstNode<'c, Pattern<'c>>,
    /// The expression part of the conditional.
    pub condition: AstNode<'c, Expression<'c>>,
}

/// An construct pattern, e.g. `Some((x, y)), Dog(name = "viktor", age = 3)`.
#[derive(Debug, PartialEq)]
pub struct ConstructorPattern<'c> {
    /// The name of the enum variant.
    pub name: AstNode<'c, AccessName<'c>>,
    /// The arguments of the enum variant as patterns.
    pub fields: AstNodes<'c, TuplePatternEntry<'c>>,
}

/// A pattern destructuring, e.g. `name: (fst, snd)`.
///
/// Used in struct and namespace patterns.
#[derive(Debug, PartialEq)]
pub struct DestructuringPattern<'c> {
    /// The name of the field.
    pub name: AstNode<'c, Name>,
    /// The pattern to match the field's value with.
    pub pattern: AstNode<'c, Pattern<'c>>,
}

/// A namespace pattern, e.g. `{ fgets, fputs, }`
#[derive(Debug, PartialEq)]
pub struct NamespacePattern<'c> {
    /// The entries of the namespace, as [DestructuringPattern] entries.
    pub fields: AstNodes<'c, DestructuringPattern<'c>>,
}

/// A tuple pattern entry
#[derive(Debug, PartialEq)]
pub struct TuplePatternEntry<'c> {
    pub name: Option<AstNode<'c, Name>>,
    pub pattern: AstNode<'c, Pattern<'c>>,
}

/// A tuple pattern, e.g. `(1, 2, x)`
#[derive(Debug, PartialEq)]
pub struct TuplePattern<'c> {
    /// The element of the tuple, as patterns.
    pub fields: AstNodes<'c, TuplePatternEntry<'c>>,
}

/// A list pattern, e.g. `[x, 1, ..]`
#[derive(Debug, PartialEq)]
pub struct ListPattern<'c> {
    /// The element of the tuple, as patterns.
    pub fields: AstNodes<'c, Pattern<'c>>,
}

/// A string literal pattern.
#[derive(Debug, PartialEq, Eq)]
pub struct StrLiteralPattern(pub StringLiteral);

/// A character literal pattern.
#[derive(Debug, PartialEq, Eq)]
pub struct CharLiteralPattern(pub char);

/// An integer literal pattern.
#[derive(Debug, PartialEq, Eq)]
pub struct IntLiteralPattern(pub u64);

/// A float literal pattern.
#[derive(Debug, PartialEq)]
pub struct FloatLiteralPattern(pub f64);

/// A boolean literal pattern.
#[derive(Debug, PartialEq, Eq)]
pub struct BoolLiteralPattern(pub bool);

/// A literal pattern, e.g. `1`, `3.4`, `"foo"`, `false`.
#[derive(Debug, PartialEq)]
pub enum LiteralPattern {
    Str(StrLiteralPattern),
    Char(CharLiteralPattern),
    Int(IntLiteralPattern),
    Float(FloatLiteralPattern),
    Bool(BoolLiteralPattern),
}

/// A pattern name binding.
#[derive(Debug, PartialEq)]
pub struct BindingPattern<'c> {
    /// The identifier that the name bind is using
    pub name: AstNode<'c, Name>,
    /// Visibility of the binding (`priv` by default)
    pub visibility: Option<AstNode<'c, Visibility>>,
    /// Mutability of the binding (immutable by default)
    pub mutability: Option<AstNode<'c, Mutability>>,
}

/// A pattern spread
#[derive(Debug, PartialEq)]
pub struct SpreadPattern<'c> {
    pub name: Option<AstNode<'c, Name>>,
}

/// The catch-all, i.e "ignore" pattern.
#[derive(Debug, PartialEq, Eq)]
pub struct IgnorePattern;

/// A pattern. e.g. `Ok(Dog {props = (1, x)})`.
#[derive(Debug, PartialEq)]
pub enum Pattern<'c> {
    Constructor(ConstructorPattern<'c>),
    Namespace(NamespacePattern<'c>),
    Tuple(TuplePattern<'c>),
    List(ListPattern<'c>),
    Literal(LiteralPattern),
    Or(OrPattern<'c>),
    If(IfPattern<'c>),
    Binding(BindingPattern<'c>),
    Ignore(IgnorePattern),
    Spread(SpreadPattern<'c>),
}

/// Enum representing whether a declaration is public or private
/// within module scope.
#[derive(Debug, PartialEq, Eq)]
pub enum Visibility {
    /// The binding is private to outer scopes. This is assumed by default.
    Private,
    /// The binding is public to outer scopes. The modifier has no
    /// effect if used within inner module scopes like a function.
    Public,
}

/// Enum representing whether a [BindingPattern] is declared as being mutable
/// or immutable.
#[derive(Debug, PartialEq, Eq)]
pub enum Mutability {
    /// Declare that the binding can be re-assigned.
    Mutable,
    /// Declare that the binding cannot be re-assigned or methods that require
    /// mutable access cannot take this binding. This is assumed by default.
    Immutable,
}

/// A type function, e.g. `<T, U: Conv<U>> => ...`.
///
/// Used in struct, enum, trait, and function definitions.
#[derive(Debug, PartialEq)]
pub struct TypeFunctionDef<'c> {
    /// The type arguments of the function.
    pub args: AstNodes<'c, TypeFunctionDefArg<'c>>,
    /// Optional return type of the type function
    pub return_ty: Option<AstNode<'c, Type<'c>>>,
    /// The body of the type function,
    pub expr: AstNode<'c, Expression<'c>>,
}

/// An argument within a type function
#[derive(Debug, PartialEq)]
pub struct TypeFunctionDefArg<'c> {
    /// The name of the argument
    pub name: AstNode<'c, Name>,

    /// The argument bounds.
    pub ty: Option<AstNode<'c, Type<'c>>>,
}

/// A declaration, e.g. `x := 3;`.
#[derive(Debug, PartialEq)]
pub struct Declaration<'c> {
    /// The pattern to bind the right-hand side to.
    pub pattern: AstNode<'c, Pattern<'c>>,

    /// Any associated type with the expression
    pub ty: Option<AstNode<'c, Type<'c>>>,

    /// Any value that is assigned to the binding, simply
    /// an expression.
    pub value: Option<AstNode<'c, Expression<'c>>>,
}

/// A merge declaration (adding implementations to traits/structs), e.g. `x ~= impl { ... };`.
#[derive(Debug, PartialEq)]
pub struct MergeDeclaration<'c> {
    /// The expression to bind the right-hand side to.
    pub decl: AstNode<'c, Expression<'c>>,

    /// Any value that is assigned to the binding, simply
    /// an expression.
    pub value: AstNode<'c, Expression<'c>>,
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
        }
    }

    /// This returns if an operator is actually re-assignable. By re-assignable, this is in the sense
    /// that you can add a '=' to mean that you are performing a re-assigning operation using the left
    /// hand-side expression as a starting point and the rhs as the other argument to the operator.
    /// For example, `a += b` is re-assigning because it means `a = a + b`.
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
#[derive(Debug, PartialEq)]
pub struct AssignExpression<'c> {
    /// The left-hand side of the assignment.
    ///
    /// This should resolve to either a variable or a struct field.
    pub lhs: AstNode<'c, Expression<'c>>,
    /// The right-hand side of the assignment.
    ///
    /// The value will be assigned to the left-hand side.
    pub rhs: AstNode<'c, Expression<'c>>,
}

/// An assign expression, e.g. `x += 4;`.
#[derive(Debug, PartialEq)]
pub struct AssignOpExpression<'c> {
    /// The left-hand side of the assignment.
    ///
    /// This should resolve to either a variable or a struct field.
    pub lhs: AstNode<'c, Expression<'c>>,
    /// The right-hand side of the assignment.
    ///
    /// The value will be assigned to the left-hand side.
    pub rhs: AstNode<'c, Expression<'c>>,

    /// Operator that is applied with the assignment on the lhs with the rhs value.
    ///
    /// Note: Some binary operators are not allowed to be in the location.
    pub operator: AstNode<'c, BinOp>,
}

/// A field of a struct definition, e.g. "name: str".
#[derive(Debug, PartialEq)]
pub struct StructDefEntry<'c> {
    /// The name of the struct field.
    pub name: AstNode<'c, Name>,
    /// The type of the struct field.
    ///
    /// Will be inferred if [None].
    pub ty: Option<AstNode<'c, Type<'c>>>,
    /// The default value of the struct field, if any.
    pub default: Option<AstNode<'c, Expression<'c>>>,
}

/// A struct definition, e.g. `struct Foo = { bar: int; };`.
#[derive(Debug, PartialEq)]
pub struct StructDef<'c> {
    /// The fields of the struct, in the form of [StructDefEntry].
    pub entries: AstNodes<'c, StructDefEntry<'c>>,
}

/// A variant of an enum definition, e.g. `Some(T)`.
#[derive(Debug, PartialEq)]
pub struct EnumDefEntry<'c> {
    /// The name of the enum variant.
    pub name: AstNode<'c, Name>,
    /// The arguments of the enum variant, if any.
    pub args: AstNodes<'c, Type<'c>>,
}

/// An enum definition, e.g. `enum Option = <T> => { Some(T); None; };`.
#[derive(Debug, PartialEq)]
pub struct EnumDef<'c> {
    /// The variants of the enum, in the form of [EnumDefEntry].
    pub entries: AstNodes<'c, EnumDefEntry<'c>>,
}

/// A trait definition, e.g. `add := <T> => trait { add: (T, T) -> T; }`.
#[derive(Debug, PartialEq)]
pub struct TraitDef<'c> {
    pub members: AstNodes<'c, Expression<'c>>,
}

/// A return statement.
///
/// Has an optional return expression, which becomes `void` if [None] is given.
#[derive(Debug, PartialEq)]
pub struct ReturnStatement<'c>(pub Option<AstNode<'c, Expression<'c>>>);

/// Break statement (only in loop context).
#[derive(Debug, PartialEq, Eq)]
pub struct BreakStatement;

/// Continue statement (only in loop context).
#[derive(Debug, PartialEq, Eq)]
pub struct ContinueStatement;

/// A branch/"case" of a `match` block.
#[derive(Debug, PartialEq)]
pub struct MatchCase<'c> {
    /// The pattern of the `match` case.
    pub pattern: AstNode<'c, Pattern<'c>>,
    /// The expression corresponding to the match case.
    ///
    /// Will be executed if the pattern succeeds.
    pub expr: AstNode<'c, Expression<'c>>,
}

/// The origin of a match block
#[derive(Debug, PartialEq, Eq)]
pub enum MatchOrigin {
    If,
    Match,
    For,
    While,
}

/// A `match` block.
#[derive(Debug, PartialEq)]
pub struct MatchBlock<'c> {
    /// The expression to match on.
    pub subject: AstNode<'c, Expression<'c>>,
    /// The match cases to execute.
    pub cases: AstNodes<'c, MatchCase<'c>>,
    /// Whether the match block represents a for, while, if or match statement
    pub origin: MatchOrigin,
}

/// A body block.
#[derive(Debug, PartialEq)]
pub struct BodyBlock<'c> {
    /// Zero or more statements.
    pub statements: AstNodes<'c, Expression<'c>>,
    /// Zero or one expression.
    pub expr: Option<AstNode<'c, Expression<'c>>>,
}

#[derive(Debug, PartialEq)]
pub struct LoopBlock<'c>(pub AstNode<'c, Block<'c>>);

#[derive(Debug, PartialEq)]
pub struct ForLoopBlock<'c> {
    pub pattern: AstNode<'c, Pattern<'c>>,
    pub iterator: AstNode<'c, Expression<'c>>,
    pub body: AstNode<'c, Block<'c>>,
}

/// A `while` loop, e.g. `while x > 2 { ... }`
#[derive(Debug, PartialEq)]
pub struct WhileLoopBlock<'c> {
    /// The condition of the the `while` loop.
    pub condition: AstNode<'c, Expression<'c>>,
    /// The body of the `while` loop.
    pub body: AstNode<'c, Block<'c>>,
}

#[derive(Debug, PartialEq)]
pub struct IfClause<'c> {
    /// The condition of the `if` block.
    pub condition: AstNode<'c, Expression<'c>>,
    /// The body of the `if-statement`
    pub body: AstNode<'c, Block<'c>>,
}

/// An `if` block consisting of the condition, block and an optional else clause e.g. `if x { ... } else { y }`
#[derive(Debug, PartialEq)]
pub struct IfBlock<'c> {
    pub clauses: AstNodes<'c, IfClause<'c>>,
    /// The else clause.
    pub otherwise: Option<AstNode<'c, Block<'c>>>,
}

#[derive(Debug, PartialEq)]
pub struct ModBlock<'c>(pub AstNode<'c, Block<'c>>);

#[derive(Debug, PartialEq)]
pub struct ImplBlock<'c>(pub AstNode<'c, Block<'c>>);

/// A block.
#[derive(Debug, PartialEq)]
pub enum Block<'c> {
    /// A match block.
    Match(MatchBlock<'c>),
    /// A loop block. The inner block is the loop body.
    Loop(LoopBlock<'c>),
    /// A for-loop block. This is later transpiled into a more simpler
    /// construct using a `loop` and a `match` clause.
    ///
    /// Since for loops are used for iterators in hash, we transpile the construct into a primitive loop.
    /// An iterator can be traversed by calling the next function on the iterator.
    /// Since next returns a Option type, we need to check if there is a value or if it returns None.
    /// If a value does exist, we essentially perform an assignment to the pattern provided.
    /// If None, the branch immediately breaks the for loop.
    ///
    /// A rough outline of what the transpilation process for a for loop looks like:
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
    For(ForLoopBlock<'c>),
    /// A while-loop block. This is later transpiled into a `loop` and `match` clause.
    ///
    /// In general, a while loop transpilation process occurs by transferring the looping
    /// condition into a match block, which compares a boolean condition. If the boolean condition
    /// evaluates to false, the loop will immediately break. Otherwise the body expression is expected.
    /// A rough outline of what the transpilation process for a while loop looks like:
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
    While(WhileLoopBlock<'c>),

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
    /// >>> if a {a_branch} else if b {b_branch} else {c_branch}
    /// will be transpiled into...
    /// >>> match true {
    ///      _ if a => a_branch
    ///      _ if b => b_branch
    ///      _ => c_branch
    ///     }
    ///
    /// Additionally, if no 'else' clause is specified, we fill it with an
    /// empty block since an if-block could be assigned to any variable and therefore
    /// we need to know the outcome of all branches for typechecking.
    If(IfBlock<'c>),
    /// A module block. The inner block becomes an inner module of the current module.
    ///
    Mod(ModBlock<'c>),
    /// A body block.
    Body(BodyBlock<'c>),
    /// An implementation block
    Impl(ImplBlock<'c>),
}

/// A function definition argument.
#[derive(Debug, PartialEq)]
pub struct FunctionDefArg<'c> {
    /// The name of the argument.
    pub name: AstNode<'c, Name>,
    /// The type of the argument, if any.
    pub ty: Option<AstNode<'c, Type<'c>>>,
    /// Default value of the argument if provided.
    ///
    /// If the value is provided, this makes it a named argument
    /// which means that they can be specified by putting the name of the
    /// argument.
    pub default: Option<AstNode<'c, Expression<'c>>>,
}

/// A function definition.
#[derive(Debug, PartialEq)]
pub struct FunctionDef<'c> {
    /// The arguments of the function definition.
    pub args: AstNodes<'c, FunctionDefArg<'c>>,
    /// The return type of the function definition.
    ///
    /// Will be inferred if [None].
    pub return_ty: Option<AstNode<'c, Type<'c>>>,
    /// The body/contents of the function, in the form of an expression.
    pub fn_body: AstNode<'c, Expression<'c>>,
}

/// Function call argument.
#[derive(Debug, PartialEq)]
pub struct FunctionCallArg<'c> {
    /// Optional name for the function argument, e.g `f(x = 3);`.
    pub name: Option<AstNode<'c, Name>>,
    /// Each argument of the function call, as an expression.
    pub value: AstNode<'c, Expression<'c>>,
}

/// Function call arguments.
#[derive(Debug, PartialEq)]
pub struct FunctionCallArgs<'c> {
    pub entries: AstNodes<'c, FunctionCallArg<'c>>,
}

/// A function call expression.
#[derive(Debug, PartialEq)]
pub struct FunctionCallExpr<'c> {
    /// An expression which evaluates to a function value.
    pub subject: AstNode<'c, Expression<'c>>,
    /// Arguments to the function, in the form of [FunctionCallArgs].
    pub args: AstNode<'c, FunctionCallArgs<'c>>,
}

/// An directive expression.
#[derive(PartialEq, Debug)]
pub struct DirectiveExpr<'c> {
    /// The name of the directive (without the "#").
    pub name: AstNode<'c, Name>,
    /// An expression which is referenced in the directive
    pub subject: AstNode<'c, Expression<'c>>,
}

/// A property access expression.
#[derive(Debug, PartialEq)]
pub struct PropertyAccessExpr<'c> {
    /// An expression which evaluates to a struct or tuple value.
    pub subject: AstNode<'c, Expression<'c>>,
    /// The property of the subject to access.
    pub property: AstNode<'c, Name>,
}

/// A typed expression, e.g. `foo as int`.
#[derive(Debug, PartialEq)]
pub struct CastExpr<'c> {
    /// The annotated type of the expression.
    pub ty: AstNode<'c, Type<'c>>,
    /// The expression being typed.
    pub expr: AstNode<'c, Expression<'c>>,
}

/// Represents a path to a module, given as a string literal to an `import` call.
#[derive(Debug, PartialEq, Eq)]
pub struct Import {
    pub path: StringLiteral,
    pub resolved_path: PathBuf,
}

/// A variable expression.
#[derive(Debug, PartialEq)]
pub struct VariableExpr<'c> {
    /// The name of the variable.
    pub name: AstNode<'c, AccessName<'c>>,
    /// Any type arguments of the variable. Only valid for traits.
    pub type_args: AstNodes<'c, NamedFieldTypeEntry<'c>>,
}

/// A reference expression with a flag denoting whether it is a raw ref or not
#[derive(Debug, PartialEq)]
pub struct RefExpr<'c> {
    pub inner_expr: AstNode<'c, Expression<'c>>,
    /// The kind of reference, either being a normal reference or a `raw` reference
    pub kind: RefKind,
    /// Mutability modifier on the expression.
    pub mutability: Option<AstNode<'c, Mutability>>,
}

/// A dereference expression.
#[derive(Debug, PartialEq)]
pub struct TypeExpr<'c>(pub AstNode<'c, Type<'c>>);

/// A dereference expression.
#[derive(Debug, PartialEq)]
pub struct DerefExpr<'c>(pub AstNode<'c, Expression<'c>>);

/// An unsafe expression.
#[derive(Debug, PartialEq)]
pub struct UnsafeExpr<'c>(pub AstNode<'c, Expression<'c>>);

/// A literal.
#[derive(Debug, PartialEq)]
pub struct LiteralExpr<'c>(pub AstNode<'c, Literal<'c>>);

/// A block.
#[derive(Debug, PartialEq)]
pub struct BlockExpr<'c>(pub AstNode<'c, Block<'c>>);

/// An `import` call.
#[derive(Debug, PartialEq)]
pub struct ImportExpr<'c>(pub AstNode<'c, Import>);

/// A trait implementation.
#[derive(Debug, PartialEq)]
pub struct TraitImpl<'c> {
    /// The referenced name to the trait
    pub ty: AstNode<'c, Type<'c>>,
    /// The implementation of the trait.
    pub implementation: AstNodes<'c, Expression<'c>>,
}

/// A binary expression `2 + 2`.
#[derive(Debug, PartialEq)]
pub struct BinaryExpression<'c> {
    pub lhs: AstNode<'c, Expression<'c>>,
    pub rhs: AstNode<'c, Expression<'c>>,
    pub operator: AstNode<'c, BinOp>,
}

/// A unary expression `!a`.
#[derive(Debug, PartialEq)]
pub struct UnaryExpression<'c> {
    pub expr: AstNode<'c, Expression<'c>>,
    pub operator: AstNode<'c, UnOp>,
}

/// An index expression `arr[x]`.
#[derive(Debug, PartialEq)]
pub struct IndexExpr<'c> {
    /// The subject that is being indexed.
    pub subject: AstNode<'c, Expression<'c>>,
    /// The expression that is the index.
    pub index_expr: AstNode<'c, Expression<'c>>,
}

/// The kind of an expression.
#[derive(Debug, PartialEq)]
pub enum ExpressionKind<'c> {
    FunctionCall(FunctionCallExpr<'c>),
    Directive(DirectiveExpr<'c>),
    Declaration(Declaration<'c>),
    Variable(VariableExpr<'c>),
    PropertyAccess(PropertyAccessExpr<'c>),
    Ref(RefExpr<'c>),
    Deref(DerefExpr<'c>),
    Unsafe(UnsafeExpr<'c>),
    LiteralExpr(LiteralExpr<'c>),
    As(CastExpr<'c>),
    Block(BlockExpr<'c>),
    Import(ImportExpr<'c>),
    StructDef(StructDef<'c>),
    EnumDef(EnumDef<'c>),
    TypeFunctionDef(TypeFunctionDef<'c>),
    TraitDef(TraitDef<'c>),
    FunctionDef(FunctionDef<'c>),
    Type(TypeExpr<'c>),
    Return(ReturnStatement<'c>),
    Break(BreakStatement),
    Continue(ContinueStatement),
    /// Expression to index a subject e.g. `arr[x]`
    Index(IndexExpr<'c>),
    /// An expression that captures a variable or a pattern being assigned
    /// to a right hand-side expression such as `x = 3`.
    Assign(AssignExpression<'c>),
    /// An expression that captures a variable or a pattern being assigned with
    /// the application of a binary operator, such as `x += 3`.
    AssignOp(AssignOpExpression<'c>),
    MergeDeclaration(MergeDeclaration<'c>),
    TraitImpl(TraitImpl<'c>),
    /// Binary Expression composed of a left and right hand-side with a binary operator
    BinaryExpr(BinaryExpression<'c>),
    /// Unary Expression composed of a unary operator and an expression
    UnaryExpr(UnaryExpression<'c>),
}

/// An expression.
#[derive(Debug, PartialEq)]
pub struct Expression<'c> {
    /// The kind of the expression
    kind: ExpressionKind<'c>,
}

impl<'c> Expression<'c> {
    /// Create a new [Expression] with a specific [ExpressionKind].
    pub fn new(kind: ExpressionKind<'c>) -> Self {
        Self { kind }
    }

    /// Convert the [Expression] into an [ExpressionKind]
    pub fn into_kind(self) -> ExpressionKind<'c> {
        self.kind
    }

    /// Get the [ExpressionKind] of the expression
    pub fn kind(&self) -> &ExpressionKind<'c> {
        &self.kind
    }
}

/// A module.
///
/// Represents a parsed `.hash` file.
#[derive(Debug, PartialEq)]
pub struct Module<'c> {
    /// The contents of the module, as a list of expressions terminated with a semi-colon.
    pub contents: AstNodes<'c, Expression<'c>>,
}
