#![allow(dead_code)]

use std::hash::{Hash, Hasher};
use std::ops::Deref;

use num::BigInt;

use crate::modules::ModuleIdx;

/// Represents an abstract syntax tree node.
///
/// Contains an inner type, as well as begin and end positions in the input.
#[derive(Eq, PartialEq, Debug, Clone)]
pub struct AstNode<T> {
    /// The actual value contained within this node.
    pub body: Box<T>,
    /// Position of the node in the input.
    pub pos: (usize, usize),
    /// Module that this node is part of. Index into `Modules`.
    pub module: ModuleIdx,
}

impl<T: Hash> Hash for AstNode<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.body.hash(state);
    }
}

impl<T> Deref for AstNode<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.body
    }
}

/// Node for an intrinsic identifier.
#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug)]
pub struct IntrinsicKey {
    /// The name of the intrinsic (without the "#").
    pub name: &'static str,
}

/// Node for a single name/symbol.
#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug)]
pub struct Name {
    // The name of the symbol.
    pub string: &'static str,
}

/// Node for a namespaced name, i.e.. access name.
#[derive(Debug, Clone)]
pub struct AccessName {
    /// The list of names that make up the access name.
    pub names: Vec<AstNode<Name>>,
}

/// Node for a concrete/"named" type.
#[derive(Debug, Clone)]
pub struct NamedType {
    /// The name of the type.
    pub name: AstNode<AccessName>,
    /// The type arguments of the type, if any.
    pub type_args: Vec<AstNode<Type>>,
}

/// Node for a type variable.
#[derive(Debug, Clone)]
pub struct TypeVar {
    /// The name of the type variable.
    pub name: AstNode<Name>,
}

/// Node for a type.
#[derive(Debug, Clone)]
pub enum Type {
    /// A concrete/"named" type.
    Named(NamedType),
    /// A type variable.
    TypeVar(TypeVar),
    /// The existential type (`?`).
    Existential,
    /// The type infer operator.
    Infer,
}

/// Node for a set literal, e.g. `{1, 2, 3}`.
#[derive(Debug, Clone)]
pub struct SetLiteral {
    /// The elements of the set literal.
    pub elements: Vec<AstNode<Expression>>,
}

/// Node for a list literal, e.g. `[1, 2, 3]`.
#[derive(Debug, Clone)]
pub struct ListLiteral {
    /// The elements of the list literal.
    pub elements: Vec<AstNode<Expression>>,
}

/// Node for a tuple literal, e.g. `(1, 'A', "foo")`.
#[derive(Debug, Clone)]
pub struct TupleLiteral {
    /// The elements of the tuple literal.
    pub elements: Vec<AstNode<Expression>>,
}

/// Node for a map literal, e.g. `{"foo": 1, "bar": 2}`.
#[derive(Debug, Clone)]
pub struct MapLiteral {
    /// The elements of the map literal (key-value pairs).
    pub elements: Vec<AstNode<(Expression, Expression)>>,
}

/// Node for a struct literal entry (struct field in struct literal), e.g. `name = "Nani"`.
#[derive(Debug, Clone)]
pub struct StructLiteralEntry {
    /// The name of the struct field.
    pub name: AstNode<Name>,
    /// The value given to the struct field.
    pub value: AstNode<Expression>,
}

/// Node for a struct literal, e.g. `Dog { name = "Adam", age = 12 }`
#[derive(Debug, Clone)]
pub struct StructLiteral {
    /// The name of the struct literal.
    pub name: AstNode<AccessName>,
    /// Type arguments to the struct literal, if any.
    pub type_args: Vec<AstNode<Type>>,
    /// The fields (entries) of the struct literal.
    pub entries: Vec<AstNode<StructLiteralEntry>>,
}

/// Node for a function definition argument.
#[derive(Debug, Clone)]
pub struct FunctionDefArg {
    /// The name of the argument.
    pub name: AstNode<Name>,
    /// The type of the argument, if any.
    ///
    /// Will be inferred if `None`.
    pub ty: Option<AstNode<Type>>,
}

/// Node for a function definition.
#[derive(Debug, Clone)]
pub struct FunctionDef {
    /// The arguments of the function definition.
    pub args: Vec<AstNode<FunctionDefArg>>,
    /// The return type of the function definition.
    ///
    /// Will be inferred if `None`.
    pub return_ty: Option<AstNode<Type>>,
    pub fn_body: AstNode<Expression>,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Str(String),
    Char(char),
    Int(BigInt),
    Float(f64),
    Set(SetLiteral),
    Map(MapLiteral),
    List(ListLiteral),
    Tuple(TupleLiteral),
    Struct(StructLiteral),
    Function(FunctionDef),
}

#[derive(Debug, Clone)]
pub struct OrPattern {
    pub a: AstNode<Pattern>,
    pub b: AstNode<Pattern>,
}

#[derive(Debug, Clone)]
pub struct IfPattern {
    pub pattern: AstNode<Pattern>,
    pub condition: AstNode<Expression>,
}

#[derive(Debug, Clone)]
pub struct EnumPattern {
    pub name: AstNode<AccessName>,
    pub variants: Vec<AstNode<Pattern>>,
}

#[derive(Debug, Clone)]
pub struct DestructuringPattern {
    pub name: AstNode<Name>,
    pub patterns: AstNode<Pattern>,
}

#[derive(Debug, Clone)]
pub struct StructPattern {
    pub name: AstNode<AccessName>,
    pub entries: Vec<AstNode<DestructuringPattern>>,
}

#[derive(Debug, Clone)]
pub struct NamespacePattern {
    pub patterns: Vec<AstNode<DestructuringPattern>>,
}

#[derive(Debug, Clone)]
pub struct TuplePattern {
    pub elements: Vec<AstNode<Pattern>>,
}

#[derive(Debug, Clone)]
pub enum LiteralPattern {
    Str(String),
    Char(char),
    Int(BigInt),
    Float(f64),
    Tuple(TuplePattern),
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Enum(EnumPattern),
    Struct(StructPattern),
    Namespace(NamespacePattern),
    Tuple(TuplePattern),
    Literal(LiteralPattern),
    Or(OrPattern),
    If(IfPattern),
    Binding(AstNode<Name>),
    Ignore,
}

#[derive(Debug, Clone)]
pub struct TraitBound {
    pub name: AstNode<AccessName>,
    pub type_args: Vec<AstNode<Type>>,
}

#[derive(Debug, Clone)]
pub struct Bound {
    pub type_args: Vec<AstNode<Type>>,
    pub trait_bounds: Vec<AstNode<TraitBound>>,
}

#[derive(Debug, Clone)]
pub struct LetStatement {
    pub pattern: AstNode<Pattern>,
    pub bound: Option<AstNode<Bound>>,
}

#[derive(Debug, Clone)]
pub struct AssignStatement {
    pub lhs: AstNode<Expression>,
    pub rhs: AstNode<Expression>,
}

#[derive(Debug, Clone)]
pub struct StructDefEntry {
    pub name: AstNode<Name>,
    pub ty: Option<AstNode<Type>>,
    pub default: Option<AstNode<Expression>>,
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub name: AstNode<Name>,
    pub bound: AstNode<Bound>,
    pub entries: Vec<AstNode<StructDefEntry>>,
}

#[derive(Debug, Clone)]
pub struct EnumDefEntry {
    pub name: AstNode<Name>,
    pub args: Vec<AstNode<Type>>,
}

#[derive(Debug, Clone)]
pub struct EnumDef {
    pub name: AstNode<Name>,
    pub bound: AstNode<Bound>,
    pub entries: Vec<AstNode<EnumDefEntry>>,
}

#[derive(Debug, Clone)]
pub struct TraitDef {
    pub name: AstNode<Name>,
    pub bound: AstNode<Bound>,
    pub trait_type: AstNode<Type>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Expr(AstNode<Expression>),
    Return(Option<AstNode<Expression>>),
    Block(AstNode<Block>),
    Break,
    Continue,
    Let(LetStatement),
    Assign(AssignStatement),
    StructDef(StructDef),
    EnumDef(EnumDef),
    TraitDef(TraitDef),
}

#[derive(Debug, Clone)]
pub struct MatchCase {
    pub pattern: AstNode<Pattern>,
    pub expr: AstNode<Expression>,
}

#[derive(Debug, Clone)]
pub struct MatchBlock {
    pub subject: AstNode<Expression>,
    pub cases: Vec<AstNode<MatchCase>>,
}

#[derive(Debug, Clone)]
pub struct BodyBlock {
    pub statements: Vec<AstNode<Statement>>,
    pub expr: Option<AstNode<Expression>>,
}

#[derive(Debug, Clone)]
pub enum Block {
    Match(MatchBlock),
    Loop(AstNode<Block>),
    Body(BodyBlock),
}

#[derive(Debug, Clone)]
pub struct FunctionCallArgs {
    pub entries: Vec<AstNode<Expression>>,
}

#[derive(Debug, Clone)]
pub struct FunctionCallExpr {
    pub subject: AstNode<Expression>,
    pub args: AstNode<FunctionCallArgs>,
}

#[derive(Debug, Clone)]
pub struct LogicalOpExpr {
    pub lhs: AstNode<Expression>,
    pub rhs: AstNode<Expression>,
}

#[derive(Debug, Clone)]
pub struct PropertyAccessExpr {
    pub subject: AstNode<Expression>,
    pub property: AstNode<Name>,
}

#[derive(Debug, Clone)]
pub struct TypedExpr {
    pub ty: AstNode<Type>,
    pub expr: AstNode<Expression>,
}

type ImportPath = String;

#[derive(Debug, Clone)]
pub struct VariableExpr {
    pub name: AstNode<AccessName>,
    pub type_args: Vec<AstNode<Type>>,
}

#[derive(Debug, Clone)]
pub enum Expression {
    FunctionCall(FunctionCallExpr),
    Intrinsic(IntrinsicKey),
    LogicalOp(LogicalOpExpr),
    Variable(VariableExpr),
    PropertyAccess(PropertyAccessExpr),
    LiteralExpr(Literal),
    Typed(TypedExpr),
    Block(AstNode<Block>),
    Import(AstNode<ImportPath>),
}

#[derive(Debug, Clone)]
pub struct Module {
    pub contents: Vec<AstNode<Statement>>,
}
