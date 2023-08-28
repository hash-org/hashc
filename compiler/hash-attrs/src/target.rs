//! Defined data types for constructing diagnostics in regards to directive
//! expressions.

use std::fmt;

use hash_ast::ast;
use hash_utils::{
    bitflags,
    itertools::Itertools,
    printing::{SequenceDisplay, SequenceDisplayOptions, SequenceJoinMode},
};

bitflags::bitflags! {
    /// [AttrTarget] is a mapping between [Expr] to a simplified
    /// version for reporting on if a directive received the 'wrong' kind of
    /// argument. Some variants of [Expr] are collapsed into the general
    /// [AttrTarget::Expr] because it is irrelevant from the context of
    /// directive what the expression is.
    ///
    /// Additionally, some of the inner variants of [Expr::Block] are
    /// expanded into the [AttrTarget] variants as their own standalone
    /// variants.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct AttrTarget: u32 {
        /// General expression, this is used when it expected any variant of an
        /// expression, but did not receive one.
        const Expr = 1 << 1;

        /// Some function call, or a constructor initialisation.
        const ConstructorCall = 1 << 2;

        /// A directive expression.
        const MacroInvocation = 1 << 3;

        /// Unsafe block expression
        const Unsafe = 1 << 4;

        /// Literal expression.
        const Lit = 1 << 5;

        /// A loop expression, representing `loop`, `while` and `for` expressions.
        const Loop = 1 << 6;

        /// A match block, represents for `match` and `if` expressions.
        const Match = 1 << 7;

        /// An implementation definition block.
        const ImplDef = 1 << 8;

        /// A top-level module.
        const Mod = 1 << 9;

        /// A module definition block.
        const ModDef = 1 << 10;

        /// A block, specifically the [`hash_ast::ast::Block::Body`] variant.
        const Block = 1 << 11;

        /// An `import` statement.
        const Import = 1 << 12;

        /// A type function definition.
        const TyFnDef = 1 << 13;

        /// A `struct` definition.
        const StructDef = 1 << 14;

        /// An `enum` definition.
        const EnumDef = 1 << 15;

        /// An enum variant.
        const EnumVariant = 1 << 16;

        /// A function definition, regardless of the position.
        const FnDef = 1 << 17;

        /// A type.
        const Ty = 1 << 18;

        /// A type argument, whilst this has similar implications to
        /// a type, it adds additional context that this is a type
        /// argument.
        const TyArg = 1 << 19;

        /// A parameter in a struct, enum, tuple or function definition.
        const Param = 1 << 20;

        /// A field in a struct or enum.
        const Field = 1 << 21;

        /// A match branch.
        const MatchCase = 1 << 22;

        /// A pattern.
        const Pat  = 1 << 23;

        /// A pattern argument.
        const PatArg  = 1 << 24;

        /// A trait definition.
        const TraitDef = 1 << 25;

        /// A general item definition e.g. `struct`, `enum`, `impl`, `mod` and `fn`.
        const Item = Self::StructDef.bits() | Self::EnumDef.bits() | Self::FnDef.bits() | Self::TyFnDef.bits() | Self::ImplDef.bits() | Self::ModDef.bits() | Self::TraitDef.bits();
    }
}

impl AttrTarget {
    /// Classify the given [ast::Expr] into a [AttrTarget].
    pub fn classify_expr(expr: &ast::Expr) -> Self {
        match expr {
            ast::Expr::ConstructorCall(_) => AttrTarget::ConstructorCall,
            ast::Expr::Macro(_) => AttrTarget::MacroInvocation,
            ast::Expr::Unsafe(_) => AttrTarget::Unsafe,
            ast::Expr::Lit(_) => AttrTarget::Lit,
            ast::Expr::Block(ast::BlockExpr { data: block }) => match block.body() {
                ast::Block::Loop(_) | ast::Block::While(_) | ast::Block::For(_) => AttrTarget::Loop,
                ast::Block::Match(_) | ast::Block::If(_) => AttrTarget::Match,
                ast::Block::Body(_) => AttrTarget::Block,
            },
            ast::Expr::Import(_) => AttrTarget::Import,
            ast::Expr::StructDef(_) => AttrTarget::StructDef,
            ast::Expr::EnumDef(_) => AttrTarget::EnumDef,
            ast::Expr::TyFnDef(_) => AttrTarget::TyFnDef,
            ast::Expr::TraitDef(_) => AttrTarget::TraitDef,
            ast::Expr::ImplDef(_) => AttrTarget::ImplDef,
            ast::Expr::ModDef(_) => AttrTarget::ModDef,
            ast::Expr::FnDef(_) => AttrTarget::FnDef,
            ast::Expr::Ty(_) => AttrTarget::Ty,

            // If this is a declaration, we have to recurse into the subject...
            ast::Expr::Declaration(ast::Declaration { value: Some(value), .. }) => {
                AttrTarget::classify_expr(value.body())
            }
            _ => AttrTarget::Expr,
        }
    }
}

impl fmt::Display for AttrTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // We will collect all of the allowed argument kinds into a vector
        let allowed_argument_kinds = self
            .iter()
            .map(|item| match item {
                AttrTarget::ConstructorCall => "constructor call",
                AttrTarget::MacroInvocation => "directive",
                AttrTarget::Unsafe => "unsafe expression",
                AttrTarget::Lit => "literal",
                AttrTarget::Loop => "loop block",
                AttrTarget::Match => "match block",
                AttrTarget::ImplDef => "impl block",
                AttrTarget::Mod => "module",
                AttrTarget::ModDef => "mod block",
                AttrTarget::Block => "body block",
                AttrTarget::Import => "import",
                AttrTarget::StructDef => "`struct` definition",
                AttrTarget::EnumDef => "`enum` definition",
                AttrTarget::TyFnDef => "implicit function definition",
                AttrTarget::FnDef => "`function` definition",
                AttrTarget::Ty => "type",
                AttrTarget::Expr => "expression",
                AttrTarget::Pat | AttrTarget::PatArg => "pattern",
                AttrTarget::TyArg => "type argument",
                AttrTarget::Field => "field",
                AttrTarget::EnumVariant => "enum variant",
                AttrTarget::MatchCase => "match case",
                AttrTarget::TraitDef => "trait definition",
                _ => unreachable!(),
            })
            .collect_vec();

        write!(
            f,
            "{}",
            SequenceDisplay::new(
                &allowed_argument_kinds,
                SequenceDisplayOptions {
                    quote: false,
                    mode: SequenceJoinMode::Either,
                    ..Default::default()
                }
            )
        )
    }
}

/// The various kinds of AST nodes that an attribute can be applied to. The
/// [AttrNode] is used to perform further validation checks on attribute
/// applications after the initial parameter/subject checks have finished.
#[derive(Clone, Copy, Debug)]
pub enum AttrNode<'ast> {
    /// A more general reference to an expression.
    Expr(ast::AstNodeRef<'ast, ast::Expr>),

    /// A function.
    Fn(ast::AstNodeRef<'ast, ast::FnDef>),

    /// A struct definition.
    Struct(ast::AstNodeRef<'ast, ast::StructDef>),

    /// An enum definition.
    Enum(ast::AstNodeRef<'ast, ast::EnumDef>),

    /// A enum definition variant.
    EnumVariant(ast::AstNodeRef<'ast, ast::EnumDefEntry>),

    /// A module definition.
    Mod(ast::AstNodeRef<'ast, ast::ModDef>),

    /// A match case.
    MatchCase(ast::AstNodeRef<'ast, ast::MatchCase>),

    /// A field or function parameter.
    Param(ast::AstNodeRef<'ast, ast::Param>),

    /// An argument to a constructor.
    ExprArg(ast::AstNodeRef<'ast, ast::ExprArg>),

    /// A pattern.
    Pat(ast::AstNodeRef<'ast, ast::Pat>),

    /// A pattern argument.
    PatArg(ast::AstNodeRef<'ast, ast::PatArg>),

    /// A type.
    Ty(ast::AstNodeRef<'ast, ast::Ty>),

    /// A type argument.
    TyArg(ast::AstNodeRef<'ast, ast::TyArg>),
}

impl<'ast> AttrNode<'ast> {
    /// Create an [ApplicationTarget] from an [ast::Expr]. This will essentially
    /// compute a target from the expression.
    ///
    /// It follows the following rules:
    ///
    /// - If the expression is a declaration, we apply recurse and try to get
    ///   [ApplicationTarget] from the subject of the declaration. If the
    ///   declaration does not have a `value` we return an empty [AttrTarget].
    ///
    /// - Otherwise, get the equivalent [AttrTarget] from the expression.
    pub fn from_expr(expr: ast::AstNodeRef<'ast, ast::Expr>) -> Self {
        match expr.body() {
            ast::Expr::Declaration(ast::Declaration { value: Some(value), .. }) => {
                Self::from_expr(value.ast_ref())
            }
            ast::Expr::StructDef(def) => Self::Struct(expr.with_body(def)),
            ast::Expr::EnumDef(def) => Self::Enum(expr.with_body(def)),
            ast::Expr::FnDef(def) => Self::Fn(expr.with_body(def)),
            ast::Expr::ModDef(def) => Self::Mod(expr.with_body(def)),
            _ => Self::Expr(expr),
        }
    }

    /// Compute the [AttrTarget] from the [AttrNode].
    pub fn target(&self) -> AttrTarget {
        match self {
            AttrNode::Expr(expr) => AttrTarget::classify_expr(expr.body()),
            AttrNode::Fn(_) => AttrTarget::FnDef,
            AttrNode::Struct(_) => AttrTarget::StructDef,
            AttrNode::Enum(_) => AttrTarget::EnumDef,
            AttrNode::EnumVariant(_) => AttrTarget::EnumVariant,
            AttrNode::Mod(_) => AttrTarget::ModDef,
            AttrNode::MatchCase(_) => AttrTarget::MatchCase,
            AttrNode::Param(_) => AttrTarget::Param,
            AttrNode::ExprArg(_) => AttrTarget::Field,
            AttrNode::Pat(_) => AttrTarget::Pat,
            AttrNode::PatArg(_) => AttrTarget::PatArg,
            AttrNode::Ty(_) => AttrTarget::Ty,
            AttrNode::TyArg(_) => AttrTarget::TyArg,
        }
    }

    /// Get the [ast::AstNodeId] of the node.
    pub fn id(&self) -> ast::AstNodeId {
        match self {
            AttrNode::Expr(expr) => expr.id(),
            AttrNode::Fn(func) => func.id(),
            AttrNode::Struct(struct_def) => struct_def.id(),
            AttrNode::Enum(enum_def) => enum_def.id(),
            AttrNode::EnumVariant(enum_variant) => enum_variant.id(),
            AttrNode::Mod(mod_def) => mod_def.id(),
            AttrNode::MatchCase(match_case) => match_case.id(),
            AttrNode::Param(param) => param.id(),
            AttrNode::ExprArg(expr_arg) => expr_arg.id(),
            AttrNode::Pat(pat) => pat.id(),
            AttrNode::Ty(ty) => ty.id(),
            AttrNode::TyArg(ty_arg) => ty_arg.id(),
            AttrNode::PatArg(pat_arg) => pat_arg.id(),
        }
    }
}
