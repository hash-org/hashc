//! Frontend-agnostic Hash abstract syntax tree type definitions.
//
// All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use crate::location::Location;
use crate::parse::ModuleIdx;
use bumpalo::Bump;
use bumpalo_herd::Herd;
use bumpalo_herd::Member;
use num::BigInt;
use std::hash::Hash;
use std::mem;
use std::ops::Deref;

/// Represents an abstract syntax tree node.
///
/// Contains an inner type, as well as begin and end positions in the input.
#[derive(Debug)]
pub struct AstNode<'ast, T> {
    /// The actual value contained within this node.
    pub body: &'ast mut T,
    /// Position of the node in the input.
    pub pos: Location,
}

pub trait AstAllocatorProvider<'ast, 'alloc>
where
    'ast: 'alloc,
{
    type Alloc: AstAllocator<'ast, 'alloc>;

    fn get_alloc<'alloc_prov>(&'alloc_prov self) -> Self::Alloc
    where
        'alloc_prov: 'ast;
}

impl<'ast, 'alloc> AstAllocatorProvider<'ast, 'alloc> for Herd
where
    'ast: 'alloc,
{
    type Alloc = Member<'ast>;

    fn get_alloc<'alloc_prov>(&'alloc_prov self) -> Self::Alloc
    where
        'alloc_prov: 'ast,
    {
        self.get()
    }
}

pub trait AstAllocator<'ast, 'alloc>
where
    'ast: 'alloc,
{
    fn alloc<T>(&'alloc self, value: T) -> &'ast mut T;

    fn alloc_lazy<T>(&'alloc self, value: impl FnOnce() -> T) -> &'ast mut T;

    fn alloc_str(&'alloc self, src: &str) -> &'ast mut str;

    fn alloc_slice<T>(&'alloc self, contents: impl Iterator<Item = T>) -> &'ast mut [T];

    fn try_alloc_slice<T, E>(
        &'alloc self,
        contents: impl Iterator<Item = Result<T, E>>,
    ) -> Result<&'ast mut [T], E>;

    fn alloc_ast_node<T>(&'alloc self, body: T, pos: Location) -> AstNode<'ast, T> {
        AstNode {
            pos,
            body: self.alloc(body),
        }
    }

    fn alloc_ast_node_lazy<T>(
        &'alloc self,
        with_body: impl FnOnce() -> T,
        pos: Location,
    ) -> AstNode<'ast, T> {
        AstNode {
            pos,
            body: self.alloc_lazy(with_body),
        }
    }

    fn alloc_ast_nodes<T>(
        &'alloc self,
        contents: impl Iterator<Item = AstNode<'ast, T>>,
    ) -> AstNodes<'ast, T> {
        self.alloc_slice(contents)
    }
}

impl<'ast> AstAllocator<'ast, 'ast> for Bump {
    fn alloc<T>(&'ast self, value: T) -> &'ast mut T {
        self.alloc(value)
    }

    fn alloc_lazy<T>(&'ast self, with_value: impl FnOnce() -> T) -> &'ast mut T {
        self.alloc_with(with_value)
    }

    fn alloc_str(&'ast self, src: &str) -> &'ast mut str {
        self.alloc_str(src)
    }

    fn alloc_slice<T>(&'ast self, contents: impl Iterator<Item = T>) -> &'ast mut [T] {
        let (min, _) = contents.size_hint();
        let mut vec = bumpalo::collections::Vec::with_capacity_in(min, self);
        vec.extend(contents);
        vec.into_bump_slice_mut()
    }

    fn try_alloc_slice<T, E>(
        &'ast self,
        contents: impl Iterator<Item = Result<T, E>>,
    ) -> Result<&'ast mut [T], E> {
        let (min, _) = contents.size_hint();
        let mut vec = bumpalo::collections::Vec::with_capacity_in(min, self);
        for i in contents {
            vec.push(i?);
        }
        Ok(vec.into_bump_slice_mut())
    }
}

impl<'ast, 'alloc> AstAllocator<'ast, 'alloc> for Member<'ast>
where
    'ast: 'alloc,
{
    fn alloc<T>(&'alloc self, value: T) -> &'ast mut T {
        self.alloc(value)
    }

    fn alloc_lazy<T>(&'alloc self, with_value: impl FnOnce() -> T) -> &'ast mut T {
        self.alloc_with(with_value)
    }

    fn alloc_str(&'alloc self, src: &str) -> &'ast mut str {
        self.alloc_str(src)
    }

    fn alloc_slice<T>(&'alloc self, contents: impl Iterator<Item = T>) -> &'ast mut [T] {
        let (min, _) = contents.size_hint();

        // This is okay to do because the herd will ensure that the reference lives as long as
        // 'ast, after the Member has been dropped.
        let bump = unsafe { mem::transmute::<&'alloc Bump, &'ast Bump>(self.as_bump()) };

        let mut vec = bumpalo::collections::Vec::with_capacity_in(min, bump);
        vec.extend(contents);
        vec.into_bump_slice_mut()
    }

    fn try_alloc_slice<T, E>(
        &'alloc self,
        contents: impl Iterator<Item = Result<T, E>>,
    ) -> Result<&'ast mut [T], E> {
        let (min, _) = contents.size_hint();

        // This is okay to do because the herd will ensure that the reference lives as long as
        // 'ast, after the Member has been dropped.
        let bump = unsafe { mem::transmute::<&'alloc Bump, &'ast Bump>(self.as_bump()) };

        let mut vec = bumpalo::collections::Vec::with_capacity_in(min, bump);
        for i in contents {
            vec.push(i?);
        }
        Ok(vec.into_bump_slice_mut())
    }
}

pub type AstNodes<'ast, T> = &'ast mut [AstNode<'ast, T>];

impl<T: PartialEq> PartialEq for AstNode<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.pos == other.pos && self.body == other.body
    }
}

impl<'alloc, 'ast, T: Clone> AstNode<'ast, T>
where
    'ast: 'alloc,
{
    fn clone_with(&self, allocator: &'alloc impl AstAllocator<'ast, 'alloc>) -> Self {
        Self {
            pos: self.pos,
            body: allocator.alloc(self.body.clone()),
        }
    }
}

/// [AstNode] dereferences to its inner `body` type.
impl<T> Deref for AstNode<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.body
    }
}

/// An intrinsic identifier.
#[derive(Hash, PartialEq, Debug)]
pub struct IntrinsicKey<'ast> {
    /// The name of the intrinsic (without the "#").
    pub name: &'ast str,
}

/// A single name/symbol.
#[derive(Hash, PartialEq, Debug)]
pub struct Name<'ast> {
    // The name of the symbol.
    pub string: &'ast str,
}

/// A namespaced name, i.e. access name.
#[derive(Debug, PartialEq)]
pub struct AccessName<'ast> {
    /// The list of names that make up the access name.
    pub names: AstNodes<'ast, Name<'ast>>,
}

/// A concrete/"named" type.
#[derive(Debug, PartialEq)]
pub struct NamedType<'ast> {
    /// The name of the type.
    pub name: AstNode<'ast, AccessName<'ast>>,
    /// The type arguments of the type, if any.
    pub type_args: AstNodes<'ast, Type<'ast>>,
}

/// A type variable.
#[derive(Debug, PartialEq)]
pub struct TypeVar<'ast> {
    /// The name of the type variable.
    pub name: AstNode<'ast, Name<'ast>>,
}

/// A type.
#[derive(Debug, PartialEq)]
pub enum Type<'ast> {
    /// A concrete/"named" type.
    Named(NamedType<'ast>),
    /// A reference type.
    Ref(AstNode<'ast, Type<'ast>>),
    /// A type variable.
    TypeVar(TypeVar<'ast>),
    /// The existential type (`?`).
    Existential,
    /// The type infer operator.
    Infer,
}

/// A set literal, e.g. `{1, 2, 3}`.
#[derive(Debug, PartialEq)]
pub struct SetLiteral<'ast> {
    /// The elements of the set literal.
    pub elements: AstNodes<'ast, Expression<'ast>>,
}

/// A list literal, e.g. `[1, 2, 3]`.
#[derive(Debug, PartialEq)]
pub struct ListLiteral<'ast> {
    /// The elements of the list literal.
    pub elements: AstNodes<'ast, Expression<'ast>>,
}

/// A tuple literal, e.g. `(1, 'A', "foo")`.
#[derive(Debug, PartialEq)]
pub struct TupleLiteral<'ast> {
    /// The elements of the tuple literal.
    pub elements: AstNodes<'ast, Expression<'ast>>,
}

/// A map literal, e.g. `{"foo": 1, "bar": 2}`.
#[derive(Debug, PartialEq)]
pub struct MapLiteral<'ast> {
    /// The elements of the map literal (key-value pairs).
    pub elements: &'ast mut [(
        AstNode<'ast, Expression<'ast>>,
        AstNode<'ast, Expression<'ast>>,
    )],
}

/// A struct literal entry (struct field in struct literal), e.g. `name = "Nani"`.
#[derive(Debug, PartialEq)]
pub struct StructLiteralEntry<'ast> {
    /// The name of the struct field.
    pub name: AstNode<'ast, Name<'ast>>,
    /// The value given to the struct field.
    pub value: AstNode<'ast, Expression<'ast>>,
}

/// A struct literal, e.g. `Dog { name = "Adam", age = 12 }`
#[derive(Debug, PartialEq)]
pub struct StructLiteral<'ast> {
    /// The name of the struct literal.
    pub name: AstNode<'ast, AccessName<'ast>>,
    /// Type arguments to the struct literal, if any.
    pub type_args: AstNodes<'ast, Type<'ast>>,
    /// The fields (entries) of the struct literal.
    pub entries: AstNodes<'ast, StructLiteralEntry<'ast>>,
}

/// A function definition argument.
#[derive(Debug, PartialEq)]
pub struct FunctionDefArg<'ast> {
    /// The name of the argument.
    pub name: AstNode<'ast, Name<'ast>>,
    /// The type of the argument, if any.
    ///
    /// Will be inferred if [None].
    pub ty: Option<AstNode<'ast, Type<'ast>>>,
}

/// A function definition.
#[derive(Debug, PartialEq)]
pub struct FunctionDef<'ast> {
    /// The arguments of the function definition.
    pub args: AstNodes<'ast, FunctionDefArg<'ast>>,
    /// The return type of the function definition.
    ///
    /// Will be inferred if [None].
    pub return_ty: Option<AstNode<'ast, Type<'ast>>>,
    /// The body/contents of the function, in the form of an expression.
    pub fn_body: AstNode<'ast, Expression<'ast>>,
}

/// A literal.
#[derive(Debug, PartialEq)]
pub enum Literal<'ast> {
    /// A string literal.
    Str(&'ast str),
    /// A character literal.
    Char(char),
    /// An integer literal.
    // TODO: does this really need to be a bigint? it is internally a vector :O
    Int(BigInt),
    /// A float literal.
    Float(f64),
    /// A set literal.
    Set(SetLiteral<'ast>),
    /// A map literal.
    Map(MapLiteral<'ast>),
    /// A list literal.
    List(ListLiteral<'ast>),
    /// A tuple literal.
    Tuple(TupleLiteral<'ast>),
    /// A struct literal.
    Struct(StructLiteral<'ast>),
    /// A function definition.
    Function(FunctionDef<'ast>),
}

/// An alternative pattern, e.g. `Red | Blue`.
#[derive(Debug, PartialEq)]
pub struct OrPattern<'ast> {
    /// The first pattern in the "or".
    pub a: AstNode<'ast, Pattern<'ast>>,
    /// The second pattern in the "or".
    pub b: AstNode<'ast, Pattern<'ast>>,
}

/// A conditional pattern, e.g. `x if x == 42`.
#[derive(Debug, PartialEq)]
pub struct IfPattern<'ast> {
    /// The pattern part of the conditional.
    pub pattern: AstNode<'ast, Pattern<'ast>>,
    /// The expression part of the conditional.
    pub condition: AstNode<'ast, Expression<'ast>>,
}

/// An enum pattern, e.g. `Some((x, y))`.
#[derive(Debug, PartialEq)]
pub struct EnumPattern<'ast> {
    /// The name of the enum variant.
    pub name: AstNode<'ast, AccessName<'ast>>,
    /// The arguments of the enum variant as patterns.
    pub args: AstNodes<'ast, Pattern<'ast>>,
}

/// A pattern destructuring, e.g. `name: (fst, snd)`.
///
/// Used in struct and namespace patterns.
#[derive(Debug, PartialEq)]
pub struct DestructuringPattern<'ast> {
    /// The name of the field.
    pub name: AstNode<'ast, Name<'ast>>,
    /// The pattern to match the field's value with.
    pub pattern: AstNode<'ast, Pattern<'ast>>,
}

/// A struct pattern, e.g. `Dog { name = "Frank"; age; }`
#[derive(Debug, PartialEq)]
pub struct StructPattern<'ast> {
    /// The name of the struct.
    pub name: AstNode<'ast, AccessName<'ast>>,
    /// The entries of the struct, as [DestructuringPattern] entries.
    pub entries: AstNodes<'ast, DestructuringPattern<'ast>>,
}

/// A namespace pattern, e.g. `{ fgets; fputs; }`
#[derive(Debug, PartialEq)]
pub struct NamespacePattern<'ast> {
    /// The entries of the namespace, as [DestructuringPattern] entries.
    pub patterns: AstNodes<'ast, DestructuringPattern<'ast>>,
}

/// A tuple pattern, e.g. `(1, 2, x)`
#[derive(Debug, PartialEq)]
pub struct TuplePattern<'ast> {
    /// The element of the tuple, as patterns.
    pub elements: AstNodes<'ast, Pattern<'ast>>,
}

/// A literal pattern, e.g. `1`, `3.4`, `"foo"`.
#[derive(Debug, PartialEq)]
pub enum LiteralPattern<'ast> {
    /// A string literal pattern.
    Str(&'ast str),
    /// A character literal pattern.
    Char(char),
    /// An integer literal pattern.
    Int(BigInt),
    /// A float literal pattern.
    Float(f64),
}

/// A pattern. e.g. `Ok(Dog {props = (1, x)})`.
#[derive(Debug, PartialEq)]
pub enum Pattern<'ast> {
    /// An enum pattern.
    Enum(EnumPattern<'ast>),
    /// A struct pattern.
    Struct(StructPattern<'ast>),
    /// A namespace pattern.
    Namespace(NamespacePattern<'ast>),
    /// A tuple pattern.
    Tuple(TuplePattern<'ast>),
    /// A literal pattern.
    Literal(LiteralPattern<'ast>),
    /// An alternative/"or" pattern.
    Or(OrPattern<'ast>),
    /// A conditional/"if" pattern.
    If(IfPattern<'ast>),
    /// A pattern name binding.
    Binding(AstNode<'ast, Name<'ast>>),
    /// The catch-all, i.e "ignore" pattern.
    Ignore,
}

/// A trait bound, e.g. "where eq<T>"
#[derive(Debug, PartialEq)]
pub struct TraitBound<'ast> {
    /// The name of the trait.
    pub name: AstNode<'ast, AccessName<'ast>>,
    /// The type arguments of the trait.
    pub type_args: AstNodes<'ast, Type<'ast>>,
}

/// A bound, e.g. "<T, U> where conv<U, T>".
///
/// Used in struct, enum, trait definitions.
#[derive(Debug, PartialEq)]
pub struct Bound<'ast> {
    /// The type arguments of the bound.
    pub type_args: AstNodes<'ast, Type<'ast>>,
    /// The traits that constrain the bound, if any.
    pub trait_bounds: AstNodes<'ast, TraitBound<'ast>>,
}

/// A let statement, e.g. `let x = 3;`.
#[derive(Debug, PartialEq)]
pub struct LetStatement<'ast> {
    /// The pattern to bind the right-hand side to.
    pub pattern: AstNode<'ast, Pattern<'ast>>,

    /// Any associated type with the expression
    pub ty: Option<AstNode<'ast, Type<'ast>>>,

    /// The bound of the let, if any.
    ///
    /// Used for trait implementations.
    pub bound: Option<AstNode<'ast, Bound<'ast>>>,

    /// Any value that is assigned to the statement, simply
    /// an expression. Since it is optional, it will be set
    /// to none if there is no expression.
    pub value: Option<AstNode<'ast, Expression<'ast>>>,
}

/// An assign statement, e.g. `x = 4;`.
#[derive(Debug, PartialEq)]
pub struct AssignStatement<'ast> {
    /// The left-hand side of the assignment.
    ///
    /// This should resolve to either a variable or a struct field.
    pub lhs: AstNode<'ast, Expression<'ast>>,
    /// The right-hand side of the assignment.
    ///
    /// The value will be assigned to the left-hand side.
    pub rhs: AstNode<'ast, Expression<'ast>>,
}

/// A field of a struct definition, e.g. "name: str".
#[derive(Debug, PartialEq)]
pub struct StructDefEntry<'ast> {
    /// The name of the struct field.
    pub name: AstNode<'ast, Name<'ast>>,
    /// The type of the struct field.
    ///
    /// Will be inferred if [None].
    pub ty: Option<AstNode<'ast, Type<'ast>>>,
    /// The default value of the struct field, if any.
    pub default: Option<AstNode<'ast, Expression<'ast>>>,
}

/// A struct definition, e.g. `struct Foo = { bar: int; };`.
#[derive(Debug, PartialEq)]
pub struct StructDef<'ast> {
    /// The name of the struct.
    pub name: AstNode<'ast, Name<'ast>>,
    /// The bound of the struct.
    pub bound: Option<AstNode<'ast, Bound<'ast>>>,
    /// The fields of the struct, in the form of [StructDefEntry].
    pub entries: AstNodes<'ast, StructDefEntry<'ast>>,
}

/// A variant of an enum definition, e.g. `Some(T)`.
#[derive(Debug, PartialEq)]
pub struct EnumDefEntry<'ast> {
    /// The name of the enum variant.
    pub name: AstNode<'ast, Name<'ast>>,
    /// The arguments of the enum variant, if any.
    pub args: AstNodes<'ast, Type<'ast>>,
}

/// An enum definition, e.g. `enum Option = <T> => { Some(T); None; };`.
#[derive(Debug, PartialEq)]
pub struct EnumDef<'ast> {
    /// The name of the enum.
    pub name: AstNode<'ast, Name<'ast>>,
    /// The bounds of the enum.
    pub bound: Option<AstNode<'ast, Bound<'ast>>>,
    /// The variants of the enum, in the form of [EnumDefEntry].
    pub entries: AstNodes<'ast, EnumDefEntry<'ast>>,
}

/// A trait definition, e.g. `trait add = <T> => (T, T) => T;`.
#[derive(Debug, PartialEq)]
pub struct TraitDef<'ast> {
    /// The name of the trait.
    pub name: AstNode<'ast, Name<'ast>>,
    /// The bound of the trait.
    pub bound: AstNode<'ast, Bound<'ast>>,
    /// The inner type of the trait. Expected to be a `Function` type.
    pub trait_type: AstNode<'ast, Type<'ast>>,
}

/// A statement.
#[derive(Debug, PartialEq)]
pub enum Statement<'ast> {
    /// An expression statement, e.g. `my_func();`
    Expr(AstNode<'ast, Expression<'ast>>),
    /// An return statement.
    ///
    /// Has an optional return expression, which becomes `void` if [None] is given.
    Return(Option<AstNode<'ast, Expression<'ast>>>),
    /// A block statement.
    Block(AstNode<'ast, Block<'ast>>),
    /// Break statement (only in loop context).
    Break,
    /// Continue statement (only in loop context).
    Continue,
    /// A let statement.
    Let(LetStatement<'ast>),
    /// An assign statement.
    Assign(AssignStatement<'ast>),
    /// A struct definition.
    StructDef(StructDef<'ast>),
    /// An enum definition.
    EnumDef(EnumDef<'ast>),
    /// A trait definition.
    TraitDef(TraitDef<'ast>),
}

/// A branch/"case" of a `match` block.
#[derive(Debug, PartialEq)]
pub struct MatchCase<'ast> {
    /// The pattern of the `match` case.
    pub pattern: AstNode<'ast, Pattern<'ast>>,
    /// The expression corresponding to the match case.
    ///
    /// Will be executed if the pattern succeeeds.
    pub expr: AstNode<'ast, Expression<'ast>>,
}

/// A `match` block.
#[derive(Debug, PartialEq)]
pub struct MatchBlock<'ast> {
    /// The expression to match on.
    pub subject: AstNode<'ast, Expression<'ast>>,
    /// The match cases to execute.
    pub cases: AstNodes<'ast, MatchCase<'ast>>,
}

/// A body block.
#[derive(Debug, PartialEq)]
pub struct BodyBlock<'ast> {
    /// Zero or more statements.
    pub statements: AstNodes<'ast, Statement<'ast>>,
    /// Zero or one expression.
    pub expr: Option<AstNode<'ast, Expression<'ast>>>,
}

/// A block.
#[derive(Debug, PartialEq)]
pub enum Block<'ast> {
    /// A match block.
    Match(MatchBlock<'ast>),
    /// A loop block.
    ///
    /// The inner block is the loop body.
    Loop(AstNode<'ast, Block<'ast>>),
    /// A body block.
    Body(BodyBlock<'ast>),
}

/// Function call arguments.
#[derive(Debug, PartialEq)]
pub struct FunctionCallArgs<'ast> {
    /// Each argument of the function call, as an expression.
    pub entries: AstNodes<'ast, Expression<'ast>>,
}

/// A function call expression.
#[derive(Debug, PartialEq)]
pub struct FunctionCallExpr<'ast> {
    /// An expression which evaluates to a function value.
    pub subject: AstNode<'ast, Expression<'ast>>,
    /// Arguments to the function, in the form of [FunctionCallArgs].
    pub args: AstNode<'ast, FunctionCallArgs<'ast>>,
}

/// A logical operator.
///
/// These are treated differently from all other operators due to short-circuiting.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum LogicalOp {
    /// The logical-and operator.
    And,
    /// The logical-or operator.
    Or,
}

/// A logical operation expression.
#[derive(Debug, PartialEq)]
pub struct LogicalOpExpr<'ast> {
    /// The operator of the logical operation.
    pub op: AstNode<'ast, LogicalOp>,
    /// The left-hand side of the operation.
    pub lhs: AstNode<'ast, Expression<'ast>>,
    /// The right-hand side of the operation.
    pub rhs: AstNode<'ast, Expression<'ast>>,
}

/// A property access exprssion.
#[derive(Debug, PartialEq)]
pub struct PropertyAccessExpr<'ast> {
    /// An expression which evaluates to a struct or tuple value.
    pub subject: AstNode<'ast, Expression<'ast>>,
    /// The property of the subject to access.
    pub property: AstNode<'ast, Name<'ast>>,
}

/// A typed expression, e.g. `foo as int`.
#[derive(Debug, PartialEq)]
pub struct TypedExpr<'ast> {
    /// The annotated type of the expression.
    pub ty: AstNode<'ast, Type<'ast>>,
    /// The expression being typed.
    pub expr: AstNode<'ast, Expression<'ast>>,
}

/// Represents a path to a module, given as a string literal to an `import` call.
#[derive(Debug, PartialEq)]
pub struct Import<'ast> {
    pub path: &'ast str,
    pub index: ModuleIdx,
}

/// A variable expression.
#[derive(Debug, PartialEq)]
pub struct VariableExpr<'ast> {
    /// The name of the variable.
    pub name: AstNode<'ast, AccessName<'ast>>,
    /// Any type arguments of the variable. Only valid for traits.
    pub type_args: AstNodes<'ast, Type<'ast>>,
}

/// A variable expression.
#[derive(Debug, PartialEq)]
pub struct IndexExpr<'ast> {
    /// The name of the variable.
    pub subject: AstNode<'ast, Expression<'ast>>,
    /// Any type arguments of the variable. Only valid for traits.
    pub index: AstNodes<'ast, Expression<'ast>>,
}

/// An expression.
#[derive(Debug, PartialEq)]
pub enum Expression<'ast> {
    /// A function call.
    FunctionCall(FunctionCallExpr<'ast>),
    /// An intrinsic symbol.
    Intrinsic(IntrinsicKey<'ast>),
    /// A logical operation.
    LogicalOp(LogicalOpExpr<'ast>),
    /// A variable.
    Variable(VariableExpr<'ast>),
    /// A property access.
    PropertyAccess(PropertyAccessExpr<'ast>),
    /// An index.
    Index(IndexExpr<'ast>),
    /// A reference expression.
    Ref(AstNode<'ast, Expression<'ast>>),
    /// A dereference expression.
    Deref(AstNode<'ast, Expression<'ast>>),
    /// A literal.
    LiteralExpr(AstNode<'ast, Literal<'ast>>),
    /// A typed expression.
    Typed(TypedExpr<'ast>),
    /// A block.
    Block(AstNode<'ast, Block<'ast>>),
    /// An `import` call.
    Import(AstNode<'ast, Import<'ast>>),
}

/// A module.
///
/// Represents a parsed `.hash` file.
#[derive(Debug, PartialEq)]
pub struct Module<'ast> {
    /// The contents of the module, as a list of statements.
    pub contents: AstNodes<'ast, Statement<'ast>>,
}
