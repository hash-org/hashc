//! Frontend-agnostic Hash AST (abstract syntax tree) type definitions.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use crate::ident::Identifier;
use crate::literal::StringLiteral;
use hash_alloc::brick::Brick;
use hash_alloc::collections::row::Row;
use hash_alloc::{row, Wall};
use hash_source::location::Location;
use hash_utils::counter;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;

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
            location: self.location,
            id: self.id,
        }
    }

    pub fn with_body<'u, U>(&self, body: &'u U) -> AstNodeRef<'u, U> {
        AstNodeRef {
            body,
            location: self.location,
            id: self.id,
        }
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

#[derive(Debug)]
pub struct AstNodeRef<'t, T> {
    body: &'t T,
    location: Location,
    id: AstNodeId,
}

impl<T> Clone for AstNodeRef<'_, T> {
    fn clone(&self) -> Self {
        Self {
            body: self.body,
            location: self.location,
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
            location: self.location,
            id: self.id,
        }
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
    pub span: Option<Location>,
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

    pub fn new(nodes: Row<'c, AstNode<'c, T>>, span: Option<Location>) -> Self {
        Self { nodes, span }
    }

    /// Function to adjust the span location of [AstNodes] if it is initially
    /// incorrectly offset because there is a 'pre-conditional' token that must
    /// be parsed before parsing the nodes. This token could be something like a
    /// '<' or '(' which starts a tuple, or type bound
    pub fn set_span(&mut self, span: Location) {
        self.span = Some(span);
    }

    pub fn location(&self) -> Option<Location> {
        self.span.or_else(|| {
            Some(
                self.nodes
                    .first()?
                    .location()
                    .join(self.nodes.last()?.location()),
            )
        })
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
#[derive(Hash, PartialEq, Debug)]
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

    pub fn path_with_locations(&self) -> Vec<(Identifier, Location)> {
        self.path
            .iter()
            .map(|part| (*part.body(), part.location()))
            .collect::<Vec<_>>()
    }
}

/// A concrete/"named" type.
#[derive(Debug, PartialEq)]
pub struct NamedType<'c> {
    /// The name of the type.
    pub name: AstNode<'c, AccessName<'c>>,
    /// The type arguments of the type, if any.
    pub type_args: AstNodes<'c, Type<'c>>,
}

/// A type variable.
#[derive(Debug, PartialEq)]
pub struct TypeVar<'c> {
    /// The name of the type variable.
    pub name: AstNode<'c, Name>,
}

/// Names for compound types that represent data structures or functions are
/// translated into string form, and thus are represented by these names.
pub const LIST_TYPE_NAME: &str = "List";
pub const SET_TYPE_NAME: &str = "Set";
pub const MAP_TYPE_NAME: &str = "Map";

/// Reference kind representing either a raw reference or a normal reference.
#[derive(Debug, PartialEq)]
pub enum RefKind {
    /// Raw reference type
    Raw,
    /// Normal reference type
    Normal,
}

/// A reference type.
#[derive(Debug, PartialEq)]
pub struct RefType<'c>(pub AstNode<'c, Type<'c>>);

/// A raw reference type
#[derive(Debug, PartialEq)]
pub struct RawRefType<'c>(pub AstNode<'c, Type<'c>>);

/// The existential type (`?`).
#[derive(Debug, PartialEq)]
pub struct ExistentialType;

/// The type infer operator.
#[derive(Debug, PartialEq)]
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

/// The function type.
#[derive(Debug, PartialEq)]
pub struct FnType<'c> {
    pub args: AstNodes<'c, NamedFieldTypeEntry<'c>>,
    pub return_ty: AstNode<'c, Type<'c>>,
}

/// A type.
#[derive(Debug, PartialEq)]
pub enum Type<'c> {
    Tuple(TupleType<'c>),
    Fn(FnType<'c>),
    Named(NamedType<'c>),
    Ref(RefType<'c>),
    RawRef(RawRefType<'c>),
    TypeVar(TypeVar<'c>),
    Existential(ExistentialType),
    Infer(InferType),
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

/// A function definition argument.
#[derive(Debug, PartialEq)]
pub struct FunctionDefArg<'c> {
    /// The name of the argument.
    pub name: AstNode<'c, Name>,
    /// The type of the argument, if any.
    ///
    /// Will be inferred if [None].
    pub ty: Option<AstNode<'c, Type<'c>>>,
    /// Default value of the type if provided.
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

/// A string literal.
#[derive(Debug, PartialEq)]
pub struct StrLiteral(pub StringLiteral);

/// A character literal.
#[derive(Debug, PartialEq)]
pub struct CharLiteral(pub char);

/// An integer literal.
#[derive(Debug, PartialEq)]
pub struct IntLiteral(pub u64);

/// A float literal.
#[derive(Debug, PartialEq)]
pub struct FloatLiteral(pub f64);

/// A boolean literal.
#[derive(Debug, PartialEq)]
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
    pub name: AstNode<'c, AccessName<'c>>,
    /// The arguments of the enum variant as patterns.
    pub fields: AstNodes<'c, Pattern<'c>>,
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

/// A struct pattern, e.g. `Dog { name = "Frank", age, }`
#[derive(Debug, PartialEq)]
pub struct StructPattern<'c> {
    /// The name of the struct.
    pub name: AstNode<'c, AccessName<'c>>,
    /// The entries of the struct, as [DestructuringPattern] entries.
    pub fields: AstNodes<'c, DestructuringPattern<'c>>,
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
#[derive(Debug, PartialEq)]
pub struct StrLiteralPattern(pub StringLiteral);

/// A character literal pattern.
#[derive(Debug, PartialEq)]
pub struct CharLiteralPattern(pub char);

/// An integer literal pattern.
#[derive(Debug, PartialEq)]
pub struct IntLiteralPattern(pub u64);

/// A float literal pattern.
#[derive(Debug, PartialEq)]
pub struct FloatLiteralPattern(pub f64);

/// A boolean literal pattern.
#[derive(Debug, PartialEq)]
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
pub struct BindingPattern<'c>(pub AstNode<'c, Name>);

/// A pattern spread
#[derive(Debug, PartialEq)]
pub struct SpreadPattern<'c> {
    pub name: Option<AstNode<'c, Name>>,
}

/// The catch-all, i.e "ignore" pattern.
#[derive(Debug, PartialEq)]
pub struct IgnorePattern;

/// A pattern. e.g. `Ok(Dog {props = (1, x)})`.
#[derive(Debug, PartialEq)]
pub enum Pattern<'c> {
    Enum(EnumPattern<'c>),
    Struct(StructPattern<'c>),
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

/// A trait bound, e.g. "where eq<T>"
#[derive(Debug, PartialEq)]
pub struct TraitBound<'c> {
    /// The name of the trait.
    pub name: AstNode<'c, AccessName<'c>>,
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
    /// The expression that the bound applies to
    pub expr: AstNode<'c, Expression<'c>>,
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
    pub value: AstNode<'c, Expression<'c>>,
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

/// A return statement.
///
/// Has an optional return expression, which becomes `void` if [None] is given.
#[derive(Debug, PartialEq)]
pub struct ReturnStatement<'c>(pub Option<AstNode<'c, Expression<'c>>>);

/// Break statement (only in loop context).
#[derive(Debug, PartialEq)]
pub struct BreakStatement;

/// Continue statement (only in loop context).
#[derive(Debug, PartialEq)]
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
#[derive(Debug, PartialEq)]
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

/// A block.
#[derive(Debug, PartialEq)]
pub enum Block<'c> {
    /// A match block.
    Match(MatchBlock<'c>),
    /// A loop block.
    ///
    /// The inner block is the loop body.
    Loop(LoopBlock<'c>),
    /// A body block.
    Body(BodyBlock<'c>),
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
    pub resolved_path: PathBuf,
}

/// A variable expression.
#[derive(Debug, PartialEq)]
pub struct VariableExpr<'c> {
    /// The name of the variable.
    pub name: AstNode<'c, AccessName<'c>>,
    /// Any type arguments of the variable. Only valid for traits.
    pub type_args: AstNodes<'c, Type<'c>>,
}

/// A reference expression with a flag denoting whether it is a raw ref or not
#[derive(Debug, PartialEq)]
pub struct RefExpr<'c> {
    pub inner_expr: AstNode<'c, Expression<'c>>,
    pub kind: RefKind,
}
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
    Typed(TypedExpr<'c>),
    Block(BlockExpr<'c>),
    Import(ImportExpr<'c>),
    StructDef(StructDef<'c>),
    EnumDef(EnumDef<'c>),
    Bound(Bound<'c>),
    TraitDef(TraitDef<'c>),
    Return(ReturnStatement<'c>),
    Break(BreakStatement),
    Continue(ContinueStatement),
    Assign(AssignExpression<'c>),
}

/// An expression.
#[derive(Debug, PartialEq)]
pub struct Expression<'c> {
    /// The kind of the expression
    kind: ExpressionKind<'c>,
}

impl<'c> Expression<'c> {
    /// Create a new [Expression] with a specific [ExpressionKind] and with
    /// no bound
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

    pub fn no_continuation(&self) -> bool {
        matches!(
            self.kind(),
            ExpressionKind::Import(_) | ExpressionKind::Break(_) | ExpressionKind::Continue(_)
        )
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
