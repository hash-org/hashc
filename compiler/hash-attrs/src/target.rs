//! Defined data types for constructing diagnostics in regards to directive
//! expressions.

use std::fmt;

use hash_ast::ast;
use hash_utils::{bitflags, printing::SequenceDisplay};

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

        /// A type function definition.
        const TyFnDef = 1 << 14;

        /// A trait implementation block e.g. `impl T {}`.
        const TraitImpl = 1 << 16;

        /// A `struct` definition.
        const StructDef = 1 << 17;

        /// An `enum` definition.
        const EnumDef = 1 << 18;

        /// A function definition, regardless of the position.
        const FnDef = 1 << 19;

        /// A type.
        const Ty = 1 << 20;

        /// A general item definition e.g. `struct`, `enum`, `impl`, `mod` and `fn`.
        const Item = Self::StructDef.bits() | Self::EnumDef.bits() | Self::FnDef.bits() | Self::TyFnDef.bits() | Self::ImplDef.bits() | Self::ModDef.bits();
    }
}

impl From<&ast::Expr> for AttrTarget {
    fn from(expr: &ast::Expr) -> Self {
        match expr {
            ast::Expr::ConstructorCall(_) => AttrTarget::ConstructorCall,
            ast::Expr::Macro(_) => AttrTarget::MacroInvocation,
            ast::Expr::Declaration(_) => AttrTarget::Declaration,
            ast::Expr::Unsafe(_) => AttrTarget::Unsafe,
            ast::Expr::Lit(_) => AttrTarget::Lit,
            ast::Expr::Cast(_) => AttrTarget::Cast,
            ast::Expr::Block(ast::BlockExpr { data: block }) => match block.body() {
                ast::Block::Loop(_) | ast::Block::While(_) | ast::Block::For(_) => AttrTarget::Loop,
                ast::Block::Match(_) | ast::Block::If(_) => AttrTarget::Match,
                ast::Block::Body(_) => AttrTarget::Block,
            },
            ast::Expr::Import(_) => AttrTarget::Import,
            ast::Expr::StructDef(_) => AttrTarget::StructDef,
            ast::Expr::EnumDef(_) => AttrTarget::EnumDef,
            ast::Expr::TyFnDef(_) => AttrTarget::TyFnDef,
            ast::Expr::TraitDef(_) => AttrTarget::Item,
            ast::Expr::ImplDef(_) => AttrTarget::ImplDef,
            ast::Expr::ModDef(_) => AttrTarget::ModDef,
            ast::Expr::FnDef(_) => AttrTarget::FnDef,
            ast::Expr::Ty(_) => AttrTarget::Ty,
            ast::Expr::TraitImpl(_) => AttrTarget::TraitImpl,
            _ => AttrTarget::Expr,
        }
    }
}

impl fmt::Display for AttrTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let item_count = self.bits().count_ones();

        // We will collect all of the allowed argument kinds into a vector
        let mut allowed_argument_kinds = Vec::with_capacity(item_count as usize);

        for kind in (*self).iter() {
            match kind {
                AttrTarget::ConstructorCall => allowed_argument_kinds.push("constructor call"),
                AttrTarget::MacroInvocation => allowed_argument_kinds.push("directive"),
                AttrTarget::Declaration => allowed_argument_kinds.push("declaration"),
                AttrTarget::Unsafe => allowed_argument_kinds.push("unsafe expression"),
                AttrTarget::Lit => allowed_argument_kinds.push("literal"),
                AttrTarget::Cast => allowed_argument_kinds.push("type cast"),
                AttrTarget::Loop => allowed_argument_kinds.push("loop block"),
                AttrTarget::Match => allowed_argument_kinds.push("match block"),
                AttrTarget::ImplDef => allowed_argument_kinds.push("impl block"),
                AttrTarget::ModDef => allowed_argument_kinds.push("mod block"),
                AttrTarget::Block => allowed_argument_kinds.push("body block"),
                AttrTarget::Import => allowed_argument_kinds.push("import"),
                AttrTarget::StructDef => allowed_argument_kinds.push("struct definition"),
                AttrTarget::EnumDef => allowed_argument_kinds.push("enum definition"),
                AttrTarget::TyFnDef => allowed_argument_kinds.push("type function definition"),
                AttrTarget::FnDef => allowed_argument_kinds.push("`function` definition"),
                AttrTarget::Ty => allowed_argument_kinds.push("type"),
                AttrTarget::TraitImpl => allowed_argument_kinds.push("trait implementation"),
                AttrTarget::Expr => allowed_argument_kinds.push("expression"),
                _ => unreachable!(),
            }
        }

        write!(f, "{}", SequenceDisplay::either(&allowed_argument_kinds))
    }
}
