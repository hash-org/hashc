//! Frontend-agnostic Hash abstract syntax tree type definitions.
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::ident::{Identifier, PathIdentifier};
use crate::location::Location;
use crate::module::ModuleIdx;
use hash_alloc::Wall;
use hash_alloc::brick::Brick;
use hash_alloc::collections::row::Row;
use hash_utils::counter;
use std::hash::Hash;
use std::ops::Deref;
use crate::literal::StringLiteral;

counter! {
    name: AstNodeId,
    counter_name: AST_NODE_ID_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

counter! {
    name: TypeId,
    counter_name: TYPE_ID_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

/// Represents an abstract syntax tree node.
///
/// Contains an inner type, as well as begin and end positions in the input.
#[derive(Debug)]
pub struct AstNode<'c, T> {
    body: Brick<'c, T>,
    location: Location,
    id: AstNodeId,
}

impl<T> PartialEq for AstNode<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<'c, T> AstNode<'c, T> {
    /// Create a new node with a given body and location.
    pub fn new(body: T, location: Location, wall: &Wall<'c>) -> Self {
        Self {
            body: Brick::new(body, wall),
            location,
            id: AstNodeId::new(),
        }
    }

    /// Get a reference to the value contained within this node.
    pub fn body(&self) -> &T {
        self.body.as_ref()
    }

    /// Take the value contained within this node.
    pub fn into_body(self) -> Brick<'c, T> {
        self.body
    }

    /// Get the location of this node in the input.
    pub fn location(&self) -> Location {
        self.location
    }

    /// Get the ID of this node.
    pub fn id(&self) -> AstNodeId {
        self.id
    }
}

pub type AstNodes<'c, T> = Row<'c, AstNode<'c, T>>;

/// [AstNode] dereferences to its inner `body` type.
impl<T> Deref for AstNode<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.body()
    }
}

/// An intrinsic identifier.
#[derive(Hash, PartialEq, Debug)]
pub struct IntrinsicKey {
    /// The name of the intrinsic (without the "#").
    pub name: Identifier,
}

/// A single name/symbol.
#[derive(Hash, PartialEq, Debug)]
pub struct Name {
    // The name of the symbol.
    pub ident: Identifier,
}

/// A namespaced name, i.e. access name.
#[derive(Debug, PartialEq)]
pub struct AccessName {
    /// The list of names that make up the access name.
    pub path: PathIdentifier,
}

/// A concrete/"named" type.
#[derive(Debug, PartialEq)]
pub struct NamedType<'c> {
    /// The name of the type.
    pub name: AstNode<'c, AccessName>,
    /// The type arguments of the type, if any.
    pub type_args: AstNodes<'c, Type<'c>>,
}

/// A type variable.
#[derive(Debug, PartialEq)]
pub struct TypeVar<'c> {
    /// The name of the type variable.
    pub name: AstNode<'c, Name>,
}

/// A type.
#[derive(Debug, PartialEq)]
pub enum Type<'c> {
    /// A concrete/"named" type.
    Named(NamedType<'c>),
    /// A reference type.
    Ref(AstNode<'c, Type<'c>>),
    /// A raw reference type
    RawRef(AstNode<'c, Type<'c>>),
    /// A type variable.
    TypeVar(TypeVar<'c>),
    /// The existential type (`?`).
    Existential,
    /// The type infer operator.
    Infer,
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

/// A tuple literal, e.g. `(1, 'A', "foo")`.
#[derive(Debug, PartialEq)]
pub struct TupleLiteral<'c> {
    /// The elements of the tuple literal.
    pub elements: AstNodes<'c, Expression<'c>>,
}

/// A map literal, e.g. `{"foo": 1, "bar": 2}`.
#[derive(Debug, PartialEq)]
pub struct MapLiteral<'c> {
    /// The elements of the map literal (key-value pairs).
    pub elements: Vec<(AstNode<'c, Expression<'c>>, AstNode<'c, Expression<'c>>)>,
}

/// A struct literal entry (struct field in struct literal), e.g. `name = "Nani"`.
#[derive(Debug, PartialEq)]
pub struct StructLiteralEntry<'c> {
    /// The name of the struct field.
    pub name: AstNode<'c, Name>,
    /// The value given to the struct field.
    pub value: AstNode<'c, Expression<'c>>,
}

/// A struct literal, e.g. `Dog { name = "Adam", age = 12 }`
#[derive(Debug, PartialEq)]
pub struct StructLiteral<'c> {
    /// The name of the struct literal.
    pub name: AstNode<'c, AccessName>,
    /// Type arguments to the struct literal, if any.
    pub type_args: AstNodes<'c, Type<'c>>,
    /// The fields (entries) of the struct literal.
    pub entries: AstNodes<'c, StructLiteralEntry<'c>>,
}

/// A function definition argument.
#[derive(Debug, PartialEq)]
pub struct FunctionDefArg<'c> {
    /// The name of the argument.
    pub name: AstNode<'c, Name>,
    /// The type of the argument, if any.
    ///
    /// Will be inferred if [None].
    pub ty: Option<AstNode<'c, Type<'c>>>,
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

/// A literal.
#[derive(Debug, PartialEq)]
pub enum Literal<'c> {
    /// A string literal.
    Str(StringLiteral),
    /// A character literal.
    Char(char),
    /// An integer literal.
    Int(u64),
    /// A float literal.
    Float(f64),
    /// A set literal.
    Set(SetLiteral<'c>),
    /// A map literal.
    Map(MapLiteral<'c>),
    /// A list literal.
    List(ListLiteral<'c>),
    /// A tuple literal.
    Tuple(TupleLiteral<'c>),
    /// A struct literal.
    Struct(StructLiteral<'c>),
    /// A function definition.
    Function(FunctionDef<'c>),
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

/// An enum pattern, e.g. `Some((x, y))`.
#[derive(Debug, PartialEq)]
pub struct EnumPattern<'c> {
    /// The name of the enum variant.
    pub name: AstNode<'c, AccessName>,
    /// The arguments of the enum variant as patterns.
    pub args: AstNodes<'c, Pattern<'c>>,
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

/// A struct pattern, e.g. `Dog { name = "Frank"; age; }`
#[derive(Debug, PartialEq)]
pub struct StructPattern<'c> {
    /// The name of the struct.
    pub name: AstNode<'c, AccessName>,
    /// The entries of the struct, as [DestructuringPattern] entries.
    pub entries: AstNodes<'c, DestructuringPattern<'c>>,
}

/// A namespace pattern, e.g. `{ fgets; fputs; }`
#[derive(Debug, PartialEq)]
pub struct NamespacePattern<'c> {
    /// The entries of the namespace, as [DestructuringPattern] entries.
    pub patterns: AstNodes<'c, DestructuringPattern<'c>>,
}

/// A tuple pattern, e.g. `(1, 2, x)`
#[derive(Debug, PartialEq)]
pub struct TuplePattern<'c> {
    /// The element of the tuple, as patterns.
    pub elements: AstNodes<'c, Pattern<'c>>,
}

/// A literal pattern, e.g. `1`, `3.4`, `"foo"`.
#[derive(Debug, PartialEq)]
pub enum LiteralPattern {
    /// A string literal pattern.
    Str(StringLiteral),
    /// A character literal pattern.
    Char(char),
    /// An integer literal pattern.
    Int(u64),
    /// A float literal pattern.
    Float(f64),
}

/// A pattern. e.g. `Ok(Dog {props = (1, x)})`.
#[derive(Debug, PartialEq)]
pub enum Pattern<'c> {
    /// An enum pattern.
    Enum(EnumPattern<'c>),
    /// A struct pattern.
    Struct(StructPattern<'c>),
    /// A namespace pattern.
    Namespace(NamespacePattern<'c>),
    /// A tuple pattern.
    Tuple(TuplePattern<'c>),
    /// A literal pattern.
    Literal(LiteralPattern),
    /// An alternative/"or" pattern.
    Or(OrPattern<'c>),
    /// A conditional/"if" pattern.
    If(IfPattern<'c>),
    /// A pattern name binding.
    Binding(AstNode<'c, Name>),
    /// The catch-all, i.e "ignore" pattern.
    Ignore,
}

/// A trait bound, e.g. "where eq<T>"
#[derive(Debug, PartialEq)]
pub struct TraitBound<'c> {
    /// The name of the trait.
    pub name: AstNode<'c, AccessName>,
    /// The type arguments of the trait.
    pub type_args: AstNodes<'c, Type<'c>>,
}

/// A bound, e.g. "<T, U> where conv<U, T>".
///
/// Used in struct, enum, trait definitions.
#[derive(Debug, PartialEq)]
pub struct Bound<'c> {
    /// The type arguments of the bound.
    pub type_args: AstNodes<'c, Type<'c>>,
    /// The traits that constrain the bound, if any.
    pub trait_bounds: AstNodes<'c, TraitBound<'c>>,
}

/// A let statement, e.g. `let x = 3;`.
#[derive(Debug, PartialEq)]
pub struct LetStatement<'c> {
    /// The pattern to bind the right-hand side to.
    pub pattern: AstNode<'c, Pattern<'c>>,

    /// Any associated type with the expression
    pub ty: Option<AstNode<'c, Type<'c>>>,

    /// The bound of the let, if any.
    ///
    /// Used for trait implementations.
    pub bound: Option<AstNode<'c, Bound<'c>>>,

    /// Any value that is assigned to the statement, simply
    /// an expression. Since it is optional, it will be set
    /// to none if there is no expression.
    pub value: Option<AstNode<'c, Expression<'c>>>,
}

/// An assign statement, e.g. `x = 4;`.
#[derive(Debug, PartialEq)]
pub struct AssignStatement<'c> {
    /// The left-hand side of the assignment.
    ///
    /// This should resolve to either a variable or a struct field.
    pub lhs: AstNode<'c, Expression<'c>>,
    /// The right-hand side of the assignment.
    ///
    /// The value will be assigned to the left-hand side.
    pub rhs: AstNode<'c, Expression<'c>>,
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
    /// The name of the struct.
    pub name: AstNode<'c, Name>,
    /// The bound of the struct.
    pub bound: Option<AstNode<'c, Bound<'c>>>,
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
    /// The name of the enum.
    pub name: AstNode<'c, Name>,
    /// The bounds of the enum.
    pub bound: Option<AstNode<'c, Bound<'c>>>,
    /// The variants of the enum, in the form of [EnumDefEntry].
    pub entries: AstNodes<'c, EnumDefEntry<'c>>,
}

/// A trait definition, e.g. `trait add = <T> => (T, T) => T;`.
#[derive(Debug, PartialEq)]
pub struct TraitDef<'c> {
    /// The name of the trait.
    pub name: AstNode<'c, Name>,
    /// The bound of the trait.
    pub bound: AstNode<'c, Bound<'c>>,
    /// The inner type of the trait. Expected to be a `Function` type.
    pub trait_type: AstNode<'c, Type<'c>>,
}

/// A statement.
#[derive(Debug, PartialEq)]
pub enum Statement<'c> {
    /// An expression statement, e.g. `my_func();`
    Expr(AstNode<'c, Expression<'c>>),
    /// An return statement.
    ///
    /// Has an optional return expression, which becomes `void` if [None] is given.
    Return(Option<AstNode<'c, Expression<'c>>>),
    /// A block statement.
    Block(AstNode<'c, Block<'c>>),
    /// Break statement (only in loop context).
    Break,
    /// Continue statement (only in loop context).
    Continue,
    /// A let statement.
    Let(LetStatement<'c>),
    /// An assign statement.
    Assign(AssignStatement<'c>),
    /// A struct definition.
    StructDef(StructDef<'c>),
    /// An enum definition.
    EnumDef(EnumDef<'c>),
    /// A trait definition.
    TraitDef(TraitDef<'c>),
}

/// A branch/"case" of a `match` block.
#[derive(Debug, PartialEq)]
pub struct MatchCase<'c> {
    /// The pattern of the `match` case.
    pub pattern: AstNode<'c, Pattern<'c>>,
    /// The expression corresponding to the match case.
    ///
    /// Will be executed if the pattern succeeeds.
    pub expr: AstNode<'c, Expression<'c>>,
}

/// A `match` block.
#[derive(Debug, PartialEq)]
pub struct MatchBlock<'c> {
    /// The expression to match on.
    pub subject: AstNode<'c, Expression<'c>>,
    /// The match cases to execute.
    pub cases: AstNodes<'c, MatchCase<'c>>,
}

/// A body block.
#[derive(Debug, PartialEq)]
pub struct BodyBlock<'c> {
    /// Zero or more statements.
    pub statements: AstNodes<'c, Statement<'c>>,
    /// Zero or one expression.
    pub expr: Option<AstNode<'c, Expression<'c>>>,
}

/// A block.
#[derive(Debug, PartialEq)]
pub enum Block<'c> {
    /// A match block.
    Match(MatchBlock<'c>),
    /// A loop block.
    ///
    /// The inner block is the loop body.
    Loop(AstNode<'c, Block<'c>>),
    /// A body block.
    Body(BodyBlock<'c>),
}

/// Function call arguments.
#[derive(Debug, PartialEq)]
pub struct FunctionCallArgs<'c> {
    /// Each argument of the function call, as an expression.
    pub entries: AstNodes<'c, Expression<'c>>,
}

/// A function call expression.
#[derive(Debug, PartialEq)]
pub struct FunctionCallExpr<'c> {
    /// An expression which evaluates to a function value.
    pub subject: AstNode<'c, Expression<'c>>,
    /// Arguments to the function, in the form of [FunctionCallArgs].
    pub args: AstNode<'c, FunctionCallArgs<'c>>,
}

/// A property access exprssion.
#[derive(Debug, PartialEq)]
pub struct PropertyAccessExpr<'c> {
    /// An expression which evaluates to a struct or tuple value.
    pub subject: AstNode<'c, Expression<'c>>,
    /// The property of the subject to access.
    pub property: AstNode<'c, Name>,
}

/// A typed expression, e.g. `foo as int`.
#[derive(Debug, PartialEq)]
pub struct TypedExpr<'c> {
    /// The annotated type of the expression.
    pub ty: AstNode<'c, Type<'c>>,
    /// The expression being typed.
    pub expr: AstNode<'c, Expression<'c>>,
}

/// Represents a path to a module, given as a string literal to an `import` call.
#[derive(Debug, PartialEq)]
pub struct Import {
    pub path: StringLiteral,
    pub index: ModuleIdx,
}

/// A variable expression.
#[derive(Debug, PartialEq)]
pub struct VariableExpr<'c> {
    /// The name of the variable.
    pub name: AstNode<'c, AccessName>,
    /// Any type arguments of the variable. Only valid for traits.
    pub type_args: AstNodes<'c, Type<'c>>,
}

/// A variable expression.
#[derive(Debug, PartialEq)]
pub struct IndexExpr<'c> {
    /// The name of the variable.
    pub subject: AstNode<'c, Expression<'c>>,
    /// Any type arguments of the variable. Only valid for traits.
    pub index: AstNodes<'c, Expression<'c>>,
}

/// The kind of an expression.
#[derive(Debug, PartialEq)]
pub enum ExpressionKind<'c> {
    /// A function call.
    FunctionCall(FunctionCallExpr<'c>),
    /// An intrinsic symbol.
    Intrinsic(IntrinsicKey),
    /// A variable.
    Variable(VariableExpr<'c>),
    /// A property access.
    PropertyAccess(PropertyAccessExpr<'c>),
    /// A reference expression.
    Ref(AstNode<'c, Expression<'c>>),
    /// A dereference expression.
    Deref(AstNode<'c, Expression<'c>>),
    /// A literal.
    LiteralExpr(AstNode<'c, Literal<'c>>),
    /// A typed expression.
    Typed(TypedExpr<'c>),
    /// A block.
    Block(AstNode<'c, Block<'c>>),
    /// An `import` call.
    Import(AstNode<'c, Import>),
}

/// An expression.
#[derive(Debug, PartialEq)]
pub struct Expression<'c> {
    kind: ExpressionKind<'c>,
    type_id: Option<TypeId>,
}

impl<'c> Expression<'c> {
    pub fn new(kind: ExpressionKind<'c>) -> Self {
        Self {
            kind,
            type_id: None,
        }
    }

    pub fn kind(&self) -> &ExpressionKind<'c> {
        &self.kind
    }

    /// Set the type ID of the node.
    pub fn set_type_id(&mut self, type_id: TypeId) {
        self.type_id = Some(type_id);
    }

    /// Clear the type ID of the node.
    pub fn clear_type_id(&mut self) {
        self.type_id = None;
    }

    /// Get the type ID of this node.
    pub fn type_id(&self) -> Option<TypeId> {
        self.type_id
    }
}

/// A module.
///
/// Represents a parsed `.hash` file.
#[derive(Debug, PartialEq)]
pub struct Module<'c> {
    /// The contents of the module, as a list of statements.
    pub contents: AstNodes<'c, Statement<'c>>,
}
