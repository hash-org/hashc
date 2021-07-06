//! Frontend-agnostic Hash abstract syntax tree type definitions.
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::ident::{Identifier, PathIdentifier};
use crate::location::Location;
use crate::parse::ModuleIdx;
use hash_utils::counter;
use num::BigInt;
use std::borrow::Cow;
use std::hash::Hash;
use std::ops::Deref;

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
#[derive(Debug, Clone)]
pub struct AstNode<T> {
    body: Box<T>,
    location: Location,
    id: AstNodeId,
}

impl<T> PartialEq for AstNode<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T> AstNode<T> {
    /// Create a new node with a given body and location.
    pub fn new(body: T, location: Location) -> Self {
        Self {
            body: Box::new(body),
            location,
            id: AstNodeId::new(),
        }
    }

    /// Get a reference to the value contained within this node.
    pub fn body(&self) -> &T {
        self.body.as_ref()
    }

    /// Take the value contained within this node.
    pub fn into_body(self) -> T {
        *self.body
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

pub type AstNodes<T> = Vec<AstNode<T>>;

pub type AstString = Cow<'static, str>;

/// [AstNode] dereferences to its inner `body` type.
impl<T> Deref for AstNode<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.body()
    }
}

/// An intrinsic identifier.
#[derive(Hash, PartialEq, Clone, Debug)]
pub struct IntrinsicKey {
    /// The name of the intrinsic (without the "#").
    pub name: Identifier,
}

/// A single name/symbol.
#[derive(Hash, PartialEq, Clone, Debug)]
pub struct Name {
    // The name of the symbol.
    pub ident: Identifier,
}

/// A namespaced name, i.e. access name.
#[derive(Debug, PartialEq, Clone)]
pub struct AccessName {
    /// The list of names that make up the access name.
    pub path: PathIdentifier,
}

/// A concrete/"named" type.
#[derive(Debug, PartialEq, Clone)]
pub struct NamedType {
    /// The name of the type.
    pub name: AstNode<AccessName>,
    /// The type arguments of the type, if any.
    pub type_args: AstNodes<Type>,
}

/// A type variable.
#[derive(Debug, PartialEq, Clone)]
pub struct TypeVar {
    /// The name of the type variable.
    pub name: AstNode<Name>,
}

/// A type.
#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    /// A concrete/"named" type.
    Named(NamedType),
    /// A reference type.
    Ref(AstNode<Type>),
    /// A raw reference type
    RawRef(AstNode<Type>),
    /// A type variable.
    TypeVar(TypeVar),
    /// The existential type (`?`).
    Existential,
    /// The type infer operator.
    Infer,
}

/// A set literal, e.g. `{1, 2, 3}`.
#[derive(Debug, PartialEq, Clone)]
pub struct SetLiteral {
    /// The elements of the set literal.
    pub elements: AstNodes<Expression>,
}

/// A list literal, e.g. `[1, 2, 3]`.
#[derive(Debug, PartialEq, Clone)]
pub struct ListLiteral {
    /// The elements of the list literal.
    pub elements: AstNodes<Expression>,
}

/// A tuple literal, e.g. `(1, 'A', "foo")`.
#[derive(Debug, PartialEq, Clone)]
pub struct TupleLiteral {
    /// The elements of the tuple literal.
    pub elements: AstNodes<Expression>,
}

/// A map literal, e.g. `{"foo": 1, "bar": 2}`.
#[derive(Debug, PartialEq, Clone)]
pub struct MapLiteral {
    /// The elements of the map literal (key-value pairs).
    pub elements: Vec<(AstNode<Expression>, AstNode<Expression>)>,
}

/// A struct literal entry (struct field in struct literal), e.g. `name = "Nani"`.
#[derive(Debug, PartialEq, Clone)]
pub struct StructLiteralEntry {
    /// The name of the struct field.
    pub name: AstNode<Name>,
    /// The value given to the struct field.
    pub value: AstNode<Expression>,
}

/// A struct literal, e.g. `Dog { name = "Adam", age = 12 }`
#[derive(Debug, PartialEq, Clone)]
pub struct StructLiteral {
    /// The name of the struct literal.
    pub name: AstNode<AccessName>,
    /// Type arguments to the struct literal, if any.
    pub type_args: AstNodes<Type>,
    /// The fields (entries) of the struct literal.
    pub entries: AstNodes<StructLiteralEntry>,
}

/// A function definition argument.
#[derive(Debug, PartialEq, Clone)]
pub struct FunctionDefArg {
    /// The name of the argument.
    pub name: AstNode<Name>,
    /// The type of the argument, if any.
    ///
    /// Will be inferred if [None].
    pub ty: Option<AstNode<Type>>,
}

/// A function definition.
#[derive(Debug, PartialEq, Clone)]
pub struct FunctionDef {
    /// The arguments of the function definition.
    pub args: AstNodes<FunctionDefArg>,
    /// The return type of the function definition.
    ///
    /// Will be inferred if [None].
    pub return_ty: Option<AstNode<Type>>,
    /// The body/contents of the function, in the form of an expression.
    pub fn_body: AstNode<Expression>,
}

/// A literal.
#[derive(Debug, PartialEq, Clone)]
pub enum Literal {
    /// A string literal.
    Str(AstString),
    /// A character literal.
    Char(char),
    /// An integer literal.
    // @@TODO: does this really need to be a bigint? it is internally a vector :O
    Int(BigInt),
    /// A float literal.
    Float(f64),
    /// A set literal.
    Set(SetLiteral),
    /// A map literal.
    Map(MapLiteral),
    /// A list literal.
    List(ListLiteral),
    /// A tuple literal.
    Tuple(TupleLiteral),
    /// A struct literal.
    Struct(StructLiteral),
    /// A function definition.
    Function(FunctionDef),
}

/// An alternative pattern, e.g. `Red | Blue`.
#[derive(Debug, PartialEq, Clone)]
pub struct OrPattern {
    /// The variants of the "or" pattern
    pub variants: AstNodes<Pattern>,
}

/// A conditional pattern, e.g. `x if x == 42`.
#[derive(Debug, PartialEq, Clone)]
pub struct IfPattern {
    /// The pattern part of the conditional.
    pub pattern: AstNode<Pattern>,
    /// The expression part of the conditional.
    pub condition: AstNode<Expression>,
}

/// An enum pattern, e.g. `Some((x, y))`.
#[derive(Debug, PartialEq, Clone)]
pub struct EnumPattern {
    /// The name of the enum variant.
    pub name: AstNode<AccessName>,
    /// The arguments of the enum variant as patterns.
    pub args: AstNodes<Pattern>,
}

/// A pattern destructuring, e.g. `name: (fst, snd)`.
///
/// Used in struct and namespace patterns.
#[derive(Debug, PartialEq, Clone)]
pub struct DestructuringPattern {
    /// The name of the field.
    pub name: AstNode<Name>,
    /// The pattern to match the field's value with.
    pub pattern: AstNode<Pattern>,
}

/// A struct pattern, e.g. `Dog { name = "Frank"; age; }`
#[derive(Debug, PartialEq, Clone)]
pub struct StructPattern {
    /// The name of the struct.
    pub name: AstNode<AccessName>,
    /// The entries of the struct, as [DestructuringPattern] entries.
    pub entries: AstNodes<DestructuringPattern>,
}

/// A namespace pattern, e.g. `{ fgets; fputs; }`
#[derive(Debug, PartialEq, Clone)]
pub struct NamespacePattern {
    /// The entries of the namespace, as [DestructuringPattern] entries.
    pub patterns: AstNodes<DestructuringPattern>,
}

/// A tuple pattern, e.g. `(1, 2, x)`
#[derive(Debug, PartialEq, Clone)]
pub struct TuplePattern {
    /// The element of the tuple, as patterns.
    pub elements: AstNodes<Pattern>,
}

/// A literal pattern, e.g. `1`, `3.4`, `"foo"`.
#[derive(Debug, PartialEq, Clone)]
pub enum LiteralPattern {
    /// A string literal pattern.
    Str(AstString),
    /// A character literal pattern.
    Char(char),
    /// An integer literal pattern.
    Int(BigInt),
    /// A float literal pattern.
    Float(f64),
}

/// A pattern. e.g. `Ok(Dog {props = (1, x)})`.
#[derive(Debug, PartialEq, Clone)]
pub enum Pattern {
    /// An enum pattern.
    Enum(EnumPattern),
    /// A struct pattern.
    Struct(StructPattern),
    /// A namespace pattern.
    Namespace(NamespacePattern),
    /// A tuple pattern.
    Tuple(TuplePattern),
    /// A literal pattern.
    Literal(LiteralPattern),
    /// An alternative/"or" pattern.
    Or(OrPattern),
    /// A conditional/"if" pattern.
    If(IfPattern),
    /// A pattern name binding.
    Binding(AstNode<Name>),
    /// The catch-all, i.e "ignore" pattern.
    Ignore,
}

/// A trait bound, e.g. "where eq<T>"
#[derive(Debug, PartialEq, Clone)]
pub struct TraitBound {
    /// The name of the trait.
    pub name: AstNode<AccessName>,
    /// The type arguments of the trait.
    pub type_args: AstNodes<Type>,
}

/// A bound, e.g. "<T, U> where conv<U, T>".
///
/// Used in struct, enum, trait definitions.
#[derive(Debug, PartialEq, Clone)]
pub struct Bound {
    /// The type arguments of the bound.
    pub type_args: AstNodes<Type>,
    /// The traits that constrain the bound, if any.
    pub trait_bounds: AstNodes<TraitBound>,
}

/// A let statement, e.g. `let x = 3;`.
#[derive(Debug, PartialEq, Clone)]
pub struct LetStatement {
    /// The pattern to bind the right-hand side to.
    pub pattern: AstNode<Pattern>,

    /// Any associated type with the expression
    pub ty: Option<AstNode<Type>>,

    /// The bound of the let, if any.
    ///
    /// Used for trait implementations.
    pub bound: Option<AstNode<Bound>>,

    /// Any value that is assigned to the statement, simply
    /// an expression. Since it is optional, it will be set
    /// to none if there is no expression.
    pub value: Option<AstNode<Expression>>,
}

/// An assign statement, e.g. `x = 4;`.
#[derive(Debug, PartialEq, Clone)]
pub struct AssignStatement {
    /// The left-hand side of the assignment.
    ///
    /// This should resolve to either a variable or a struct field.
    pub lhs: AstNode<Expression>,
    /// The right-hand side of the assignment.
    ///
    /// The value will be assigned to the left-hand side.
    pub rhs: AstNode<Expression>,
}

/// A field of a struct definition, e.g. "name: str".
#[derive(Debug, PartialEq, Clone)]
pub struct StructDefEntry {
    /// The name of the struct field.
    pub name: AstNode<Name>,
    /// The type of the struct field.
    ///
    /// Will be inferred if [None].
    pub ty: Option<AstNode<Type>>,
    /// The default value of the struct field, if any.
    pub default: Option<AstNode<Expression>>,
}

/// A struct definition, e.g. `struct Foo = { bar: int; };`.
#[derive(Debug, PartialEq, Clone)]
pub struct StructDef {
    /// The name of the struct.
    pub name: AstNode<Name>,
    /// The bound of the struct.
    pub bound: Option<AstNode<Bound>>,
    /// The fields of the struct, in the form of [StructDefEntry].
    pub entries: AstNodes<StructDefEntry>,
}

/// A variant of an enum definition, e.g. `Some(T)`.
#[derive(Debug, PartialEq, Clone)]
pub struct EnumDefEntry {
    /// The name of the enum variant.
    pub name: AstNode<Name>,
    /// The arguments of the enum variant, if any.
    pub args: AstNodes<Type>,
}

/// An enum definition, e.g. `enum Option = <T> => { Some(T); None; };`.
#[derive(Debug, PartialEq, Clone)]
pub struct EnumDef {
    /// The name of the enum.
    pub name: AstNode<Name>,
    /// The bounds of the enum.
    pub bound: Option<AstNode<Bound>>,
    /// The variants of the enum, in the form of [EnumDefEntry].
    pub entries: AstNodes<EnumDefEntry>,
}

/// A trait definition, e.g. `trait add = <T> => (T, T) => T;`.
#[derive(Debug, PartialEq, Clone)]
pub struct TraitDef {
    /// The name of the trait.
    pub name: AstNode<Name>,
    /// The bound of the trait.
    pub bound: AstNode<Bound>,
    /// The inner type of the trait. Expected to be a `Function` type.
    pub trait_type: AstNode<Type>,
}

/// A statement.
#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    /// An expression statement, e.g. `my_func();`
    Expr(AstNode<Expression>),
    /// An return statement.
    ///
    /// Has an optional return expression, which becomes `void` if [None] is given.
    Return(Option<AstNode<Expression>>),
    /// A block statement.
    Block(AstNode<Block>),
    /// Break statement (only in loop context).
    Break,
    /// Continue statement (only in loop context).
    Continue,
    /// A let statement.
    Let(LetStatement),
    /// An assign statement.
    Assign(AssignStatement),
    /// A struct definition.
    StructDef(StructDef),
    /// An enum definition.
    EnumDef(EnumDef),
    /// A trait definition.
    TraitDef(TraitDef),
}

/// A branch/"case" of a `match` block.
#[derive(Debug, PartialEq, Clone)]
pub struct MatchCase {
    /// The pattern of the `match` case.
    pub pattern: AstNode<Pattern>,
    /// The expression corresponding to the match case.
    ///
    /// Will be executed if the pattern succeeeds.
    pub expr: AstNode<Expression>,
}

/// A `match` block.
#[derive(Debug, PartialEq, Clone)]
pub struct MatchBlock {
    /// The expression to match on.
    pub subject: AstNode<Expression>,
    /// The match cases to execute.
    pub cases: AstNodes<MatchCase>,
}

/// A body block.
#[derive(Debug, PartialEq, Clone)]
pub struct BodyBlock {
    /// Zero or more statements.
    pub statements: AstNodes<Statement>,
    /// Zero or one expression.
    pub expr: Option<AstNode<Expression>>,
}

/// A block.
#[derive(Debug, PartialEq, Clone)]
pub enum Block {
    /// A match block.
    Match(MatchBlock),
    /// A loop block.
    ///
    /// The inner block is the loop body.
    Loop(AstNode<Block>),
    /// A body block.
    Body(BodyBlock),
}

/// Function call arguments.
#[derive(Debug, PartialEq, Clone)]
pub struct FunctionCallArgs {
    /// Each argument of the function call, as an expression.
    pub entries: AstNodes<Expression>,
}

/// A function call expression.
#[derive(Debug, PartialEq, Clone)]
pub struct FunctionCallExpr {
    /// An expression which evaluates to a function value.
    pub subject: AstNode<Expression>,
    /// Arguments to the function, in the form of [FunctionCallArgs].
    pub args: AstNode<FunctionCallArgs>,
}

/// A property access exprssion.
#[derive(Debug, PartialEq, Clone)]
pub struct PropertyAccessExpr {
    /// An expression which evaluates to a struct or tuple value.
    pub subject: AstNode<Expression>,
    /// The property of the subject to access.
    pub property: AstNode<Name>,
}

/// A typed expression, e.g. `foo as int`.
#[derive(Debug, PartialEq, Clone)]
pub struct TypedExpr {
    /// The annotated type of the expression.
    pub ty: AstNode<Type>,
    /// The expression being typed.
    pub expr: AstNode<Expression>,
}

/// Represents a path to a module, given as a string literal to an `import` call.
#[derive(Debug, PartialEq, Clone)]
pub struct Import {
    pub path: AstString,
    pub index: ModuleIdx,
}

/// A variable expression.
#[derive(Debug, PartialEq, Clone)]
pub struct VariableExpr {
    /// The name of the variable.
    pub name: AstNode<AccessName>,
    /// Any type arguments of the variable. Only valid for traits.
    pub type_args: AstNodes<Type>,
}

/// A variable expression.
#[derive(Debug, PartialEq, Clone)]
pub struct IndexExpr {
    /// The name of the variable.
    pub subject: AstNode<Expression>,
    /// Any type arguments of the variable. Only valid for traits.
    pub index: AstNodes<Expression>,
}

/// The kind of an expression.
#[derive(Debug, PartialEq, Clone)]
pub enum ExpressionKind {
    /// A function call.
    FunctionCall(FunctionCallExpr),
    /// An intrinsic symbol.
    Intrinsic(IntrinsicKey),
    /// A variable.
    Variable(VariableExpr),
    /// A property access.
    PropertyAccess(PropertyAccessExpr),
    /// A reference expression.
    Ref(AstNode<Expression>),
    /// A dereference expression.
    Deref(AstNode<Expression>),
    /// A literal.
    LiteralExpr(AstNode<Literal>),
    /// A typed expression.
    Typed(TypedExpr),
    /// A block.
    Block(AstNode<Block>),
    /// An `import` call.
    Import(AstNode<Import>),
}

/// An expression.
#[derive(Debug, PartialEq, Clone)]
pub struct Expression {
    kind: ExpressionKind,
    type_id: Option<TypeId>,
}

impl Expression {
    pub fn new(kind: ExpressionKind) -> Self {
        Self {
            kind,
            type_id: None,
        }
    }

    pub fn kind(&self) -> &ExpressionKind {
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
#[derive(Debug, PartialEq, Clone)]
pub struct Module {
    /// The contents of the module, as a list of statements.
    pub contents: AstNodes<Statement>,
}
