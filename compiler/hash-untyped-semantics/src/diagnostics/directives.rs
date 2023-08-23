//! Defined data types for constructing diagnostics in regards to directive
//! expressions.

use std::fmt;

use hash_ast::ast::{Block, BlockExpr, Expr};
use hash_utils::{printing::SequenceDisplay, bitflags};

bitflags::bitflags! {
    /// [DirectiveArgument] is a mapping between [Expr] to a simplified
    /// version for reporting on if a directive received the 'wrong' kind of
    /// argument. Some variants of [Expr] are collapsed into the general
    /// [DirectiveArgument::Expr] because it is irrelevant from the context of
    /// directive what the expression is.
    ///
    /// Additionally, some of the inner variants of [Expr::Block] are
    /// expanded into the [DirectiveArgument] variants as their own standalone
    /// variants.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct DirectiveArgument: u32 {
        /// General expression, this is used when it expected any variant of an
        /// expression, but did not receive one.
        const Expr = 1 << 1;

        /// Some function call, or a constructor initialisation.
        const ConstructorCall = 1 << 2;

        /// A directive expression.
        const MacroInvocation = 1 << 3;

        /// A declaration.
        const Declaration = 1 << 4;

        /// Unsafe block expression
        const Unsafe = 1 << 5;

        /// Literal expression.
        const Lit = 1 << 6;

        /// A cast expression, casting the lhs to the rhs type.
        const Cast = 1 << 7;

        /// A loop expression, representing `loop`, `while` and `for` expressions.
        const Loop = 1 << 8;

        /// A match block, represents for `match` and `if` expressions.
        const Match = 1 << 9;

        /// An implementation definition block.
        const ImplDef = 1 << 10;

        /// A module definition block.
        const ModDef = 1 << 11;

        /// A block, specifically the [`hash_ast::ast::Block::Body`] variant.
        const Block = 1 << 12;

        /// An `import` statement.
        const Import = 1 << 13;

        /// A `struct` definition.
        const StructDef = 1 << 14;

        /// An `enum` definition.
        const EnumDef = 1 << 15;

        /// A type function definition.
        const TyFnDef = 1 << 16;

        /// A `trait` definition as the argument to the function.
        const TraitDef = 1 << 17;

        /// A trait implementation block e.g. `impl T {}`.
        const TraitImpl = 1 << 18;

        /// A function definition, regardless of the position.
        const FnDef = 1 << 19;

        /// A type.
        const Ty = 1 << 20;

        /// A `return` expression.
        const Return = 1 << 21;

        /// A `break` expression.
        const Break = 1 << 22;

        /// A `continue` expression.
        const Continue = 1 << 23;

        /// A merge declaration.
        const MergeDeclaration = 1 << 24;
    }
}

impl From<&Expr> for DirectiveArgument {
    fn from(expr: &Expr) -> Self {
        match expr {
            Expr::ConstructorCall(_) => DirectiveArgument::ConstructorCall,
            Expr::Macro(_) => DirectiveArgument::MacroInvocation,
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

impl fmt::Display for DirectiveArgument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let item_count = self.bits().count_ones();

        // We will collect all of the allowed argument kinds into a vector
        let mut allowed_argument_kinds = Vec::with_capacity(item_count as usize);

        for kind in (*self).iter() {
            match kind {
                DirectiveArgument::ConstructorCall => {
                    allowed_argument_kinds.push("constructor call")
                }
                DirectiveArgument::MacroInvocation => allowed_argument_kinds.push("directive"),
                DirectiveArgument::Declaration => allowed_argument_kinds.push("declaration"),
                DirectiveArgument::MergeDeclaration => {
                    allowed_argument_kinds.push("merge declaration")
                }
                DirectiveArgument::Unsafe => allowed_argument_kinds.push("unsafe expression"),
                DirectiveArgument::Lit => allowed_argument_kinds.push("literal"),
                DirectiveArgument::Cast => allowed_argument_kinds.push("type cast"),
                DirectiveArgument::Loop => allowed_argument_kinds.push("loop block"),
                DirectiveArgument::Match => allowed_argument_kinds.push("match block"),
                DirectiveArgument::ImplDef => allowed_argument_kinds.push("impl block"),
                DirectiveArgument::ModDef => allowed_argument_kinds.push("mod block"),
                DirectiveArgument::Block => allowed_argument_kinds.push("body block"),
                DirectiveArgument::Import => allowed_argument_kinds.push("import"),
                DirectiveArgument::StructDef => allowed_argument_kinds.push("struct definition"),
                DirectiveArgument::EnumDef => allowed_argument_kinds.push("enum definition"),
                DirectiveArgument::TyFnDef => {
                    allowed_argument_kinds.push("type function definition")
                }
                DirectiveArgument::TraitDef => allowed_argument_kinds.push("`trait` definition"),
                DirectiveArgument::FnDef => allowed_argument_kinds.push("`function` definition"),
                DirectiveArgument::Ty => allowed_argument_kinds.push("type"),
                DirectiveArgument::Return => allowed_argument_kinds.push("return statement"),
                DirectiveArgument::Break => allowed_argument_kinds.push("break statement"),
                DirectiveArgument::Continue => allowed_argument_kinds.push("continue statement"),
                DirectiveArgument::TraitImpl => allowed_argument_kinds.push("trait implementation"),
                DirectiveArgument::Expr => allowed_argument_kinds.push("expression"),
                _ => unreachable!(),
            }
        }

        write!(f, "{}", SequenceDisplay::either(&allowed_argument_kinds))
    }
}
