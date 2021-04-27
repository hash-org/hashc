#![allow(dead_code)]

use std::hash::{Hash, Hasher};
use std::ops::Deref;

use num::BigInt;

use crate::modules::ModuleIdx;

#[derive(Eq, PartialEq, Debug, Clone)]
pub struct AstNode<T> {
    pub body: Box<T>,
    pub pos: (u32, u32),
    pub module: ModuleIdx,
}

impl<T> Hash for AstNode<T>
where
    T: Hash,
{
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

#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug)]
pub struct IntrinsicKey {
    pub name: &'static str,
}

#[derive(Hash, Eq, PartialEq, Copy, Clone, Debug)]
pub struct Name {
    pub symbol: &'static str,
}

#[derive(Debug, Clone)]
pub struct AccessName {
    pub names: Vec<AstNode<Name>>,
}

#[derive(Debug, Clone)]
pub struct NamedType {
    pub name: AstNode<AccessName>,
    pub type_args: Vec<AstNode<Type>>,
}

#[derive(Debug, Clone)]
pub struct TypeVar {
    pub name: AstNode<Name>,
}

#[derive(Debug, Clone)]
pub enum Type {
    Named(NamedType),
    TypeVar(TypeVar),
    Existential,
    Infer,
}

#[derive(Debug, Clone)]
pub struct SetLiteral {
    pub elements: Vec<AstNode<Expression>>,
}

#[derive(Debug, Clone)]
pub struct ListLiteral {
    pub elements: Vec<AstNode<Expression>>,
}

#[derive(Debug, Clone)]
pub struct TupleLiteral {
    pub elements: Vec<AstNode<Expression>>,
}

#[derive(Debug, Clone)]
pub struct MapLiteral {
    pub elements: Vec<AstNode<(Expression, Expression)>>,
}

#[derive(Debug, Clone)]
pub struct StructLiteralEntry {
    name: AstNode<Name>,
    value: AstNode<Expression>,
}

#[derive(Debug, Clone)]
pub struct StructLiteral {
    name: AstNode<AccessName>,
    type_args: Vec<AstNode<Type>>,
    entries: Vec<AstNode<StructLiteralEntry>>,
}

#[derive(Debug, Clone)]
pub struct FunctionDefArg {
    name: AstNode<Name>,
    ty: Option<AstNode<Type>>,
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub args: Vec<AstNode<FunctionDefArg>>,
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
