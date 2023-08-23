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

        /// A function definition, regardless of the position.
        const FnDef = 1 << 16;

        /// A type.
        const Ty = 1 << 17;

        /// A type argument, whilst this has similar implications to
        /// a type, it adds additional context that this is a type
        /// argument.
        const TyArg = 1 << 18;

        /// A field in a struct or enum.
        const Field = 1 << 19;

        /// An enum variant.
        const EnumVariant = 1 << 20;

        /// A match branch.
        const MatchCase = 1 << 21;

        /// A pattern.
        const Pat  = 1 << 22;

        /// A general item definition e.g. `struct`, `enum`, `impl`, `mod` and `fn`.
        const Item = Self::StructDef.bits() | Self::EnumDef.bits() | Self::FnDef.bits() | Self::TyFnDef.bits() | Self::ImplDef.bits() | Self::ModDef.bits();
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
            ast::Expr::TraitDef(_) => AttrTarget::Item,
            ast::Expr::ImplDef(_) => AttrTarget::ImplDef,
            ast::Expr::ModDef(_) => AttrTarget::ModDef,
            ast::Expr::FnDef(_) => AttrTarget::FnDef,
            ast::Expr::Ty(_) => AttrTarget::Ty,
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
                AttrTarget::Unsafe => allowed_argument_kinds.push("unsafe expression"),
                AttrTarget::Lit => allowed_argument_kinds.push("literal"),
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
                AttrTarget::Expr => allowed_argument_kinds.push("expression"),
                _ => unreachable!(),
            }
        }

        write!(f, "{}", SequenceDisplay::either(&allowed_argument_kinds))
    }
}
