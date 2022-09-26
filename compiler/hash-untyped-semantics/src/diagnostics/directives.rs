//! Defined data types for constructing diagnostics in regards to directive
//! expressions.

use std::fmt::Display;

use hash_ast::ast::{Block, BlockExpr, Expr};

/// [DirectiveArgument] is a mapping between [Expr] to a simplified
/// version for reporting on if a directive received the 'wrong' kind of
/// argument. Some variants of [Expr] are collapsed into the general
/// [DirectiveArgument::Expr] because it is irrelevant from the context of
/// directive what the expression is.
///
/// Additionally, some of the inner variants of [Expr::Block] are
/// expanded into the [DirectiveArgument] variants as their own standalone
/// variants.
pub enum DirectiveArgument {
    ConstructorCall,
    Directive,
    Declaration,
    Unsafe,
    LitExpr,
    Cast,
    /// Since the AST is de-sugared at this point, it should be that `for`,
    /// `while` and `loop` blocks end up here...
    Loop,
    /// Since the AST is de-sugared at this point, it should be that both
    /// `match` and `if` blocks end up here...
    Match,
    /// The [hash_ast::ast::Block::Impl] variant
    ImplBlock,
    /// The [hash_ast::ast::Block::Mod] variant
    ModBlock,
    /// The [hash_ast::ast::Block::Body] variant
    Block,
    Import,
    StructDef,
    EnumDef,
    TyFnDef,
    TraitDef,
    FnDef,
    Ty,
    Return,
    Break,
    Continue,
    MergeDeclaration,
    TraitImpl,
    /// General expression
    Expr,
}

impl From<&Expr> for DirectiveArgument {
    fn from(expr: &Expr) -> Self {
        match expr {
            Expr::ConstructorCall(_) => DirectiveArgument::ConstructorCall,
            Expr::Directive(_) => DirectiveArgument::Directive,
            Expr::Declaration(_) => DirectiveArgument::Declaration,
            Expr::Unsafe(_) => DirectiveArgument::Unsafe,
            Expr::LitExpr(_) => DirectiveArgument::LitExpr,
            Expr::Cast(_) => DirectiveArgument::Cast,
            Expr::Block(BlockExpr { data: block }) => match block.body() {
                Block::Loop(_) | Block::While(_) | Block::For(_) => DirectiveArgument::Loop,
                Block::Match(_) | Block::If(_) => DirectiveArgument::Match,
                Block::Mod(_) => DirectiveArgument::ModBlock,
                Block::Body(_) => DirectiveArgument::Block,
                Block::Impl(_) => DirectiveArgument::ImplBlock,
            },
            Expr::Import(_) => DirectiveArgument::Import,
            Expr::StructDef(_) => DirectiveArgument::StructDef,
            Expr::EnumDef(_) => DirectiveArgument::EnumDef,
            Expr::TyFnDef(_) => DirectiveArgument::TyFnDef,
            Expr::TraitDef(_) => DirectiveArgument::TraitDef,
            Expr::FnDef(_) => DirectiveArgument::FnDef,
            Expr::Ty(_) => DirectiveArgument::Ty,
            Expr::Return(_) => DirectiveArgument::Return,
            Expr::Break(_) => DirectiveArgument::Break,
            Expr::Continue(_) => DirectiveArgument::Continue,
            Expr::MergeDeclaration(_) => DirectiveArgument::MergeDeclaration,
            Expr::TraitImpl(_) => DirectiveArgument::TraitImpl,
            _ => DirectiveArgument::Expr,
        }
    }
}

impl Display for DirectiveArgument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DirectiveArgument::ConstructorCall => write!(f, "a constructor call"),
            DirectiveArgument::Directive => write!(f, "directive"),
            DirectiveArgument::Declaration => write!(f, "declaration"),
            DirectiveArgument::MergeDeclaration => write!(f, "merge declaration"),
            DirectiveArgument::Unsafe => write!(f, "unsafe expression"),
            DirectiveArgument::LitExpr => write!(f, "literal"),
            DirectiveArgument::Cast => write!(f, "type cast"),
            DirectiveArgument::Loop => write!(f, "`loop` block"),
            DirectiveArgument::Match => write!(f, "`match` block"),
            DirectiveArgument::ImplBlock => write!(f, "`impl` block"),
            DirectiveArgument::ModBlock => write!(f, "`mod` block"),
            DirectiveArgument::Block => write!(f, "body block"),
            DirectiveArgument::Import => write!(f, "import"),
            DirectiveArgument::StructDef => write!(f, "struct definition"),
            DirectiveArgument::EnumDef => write!(f, "`enum` definition"),
            DirectiveArgument::TyFnDef => write!(f, "`type` function definition"),
            DirectiveArgument::TraitDef => write!(f, "`trait` definition"),
            DirectiveArgument::FnDef => write!(f, "`function` definition"),
            DirectiveArgument::Ty => write!(f, "type"),
            DirectiveArgument::Return => write!(f, "return statement"),
            DirectiveArgument::Break => write!(f, "break statement"),
            DirectiveArgument::Continue => write!(f, "continue statement"),
            DirectiveArgument::TraitImpl => write!(f, "`trait` implementation"),
            DirectiveArgument::Expr => write!(f, "expression"),
        }
    }
}
