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
    /// Some function call, or a constructor initialisation.
    ConstructorCall,
    /// A directive expression.
    Directive,
    /// A declaration.
    Declaration,
    /// Unsafe block expression
    Unsafe,
    /// Literal expression.
    Lit,
    /// A cast expression, casting the lhs to the rhs type.
    Cast,
    /// Since the AST is de-sugared at this point, it should be that `for`,
    /// `while` and `loop` blocks end up here...
    Loop,
    /// Since the AST is de-sugared at this point, it should be that both
    /// `match` and `if` blocks end up here...
    Match,
    /// The [hash_ast::ast::Block::Impl] variant
    ImplDef,
    /// The [hash_ast::ast::Block::Mod] variant
    ModDef,
    /// The [hash_ast::ast::Block::Body] variant
    Block,
    /// An `import` statement.
    Import,
    /// A `struct` definition.
    StructDef,
    /// An `enum` definition.
    EnumDef,
    /// A type function definition.
    TyFnDef,
    /// A `trait` definition as the argument to the function.
    TraitDef,
    /// A function definition, regardless of the position.
    FnDef,
    /// A type.
    Ty,
    /// A `return` expression.
    Return,
    /// A `break` expression.
    Break,
    /// A `continue` expression.
    Continue,
    /// A merge declaration.
    MergeDeclaration,
    /// A trait implementation block e.g. `impl T {}`.
    TraitImpl,
    /// General expression, this is used when it expected any variant of an
    /// expression, but did not receive one.
    Expr,
}

impl From<&Expr> for DirectiveArgument {
    fn from(expr: &Expr) -> Self {
        match expr {
            Expr::ConstructorCall(_) => DirectiveArgument::ConstructorCall,
            Expr::Directive(_) => DirectiveArgument::Directive,
            Expr::Declaration(_) => DirectiveArgument::Declaration,
            Expr::Unsafe(_) => DirectiveArgument::Unsafe,
            Expr::Lit(_) => DirectiveArgument::Lit,
            Expr::Cast(_) => DirectiveArgument::Cast,
            Expr::Block(BlockExpr { data: block }) => match block.body() {
                Block::Loop(_) | Block::While(_) | Block::For(_) => DirectiveArgument::Loop,
                Block::Match(_) | Block::If(_) => DirectiveArgument::Match,
                Block::Body(_) => DirectiveArgument::Block,
            },
            Expr::Import(_) => DirectiveArgument::Import,
            Expr::StructDef(_) => DirectiveArgument::StructDef,
            Expr::EnumDef(_) => DirectiveArgument::EnumDef,
            Expr::TyFnDef(_) => DirectiveArgument::TyFnDef,
            Expr::TraitDef(_) => DirectiveArgument::TraitDef,
            Expr::ImplDef(_) => DirectiveArgument::ImplDef,
            Expr::ModDef(_) => DirectiveArgument::ModDef,
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
            DirectiveArgument::Lit => write!(f, "literal"),
            DirectiveArgument::Cast => write!(f, "type cast"),
            DirectiveArgument::Loop => write!(f, "`loop` block"),
            DirectiveArgument::Match => write!(f, "`match` block"),
            DirectiveArgument::ImplDef => write!(f, "`impl` block"),
            DirectiveArgument::ModDef => write!(f, "`mod` block"),
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
