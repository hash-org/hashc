use hash_ast::ast::{AstNodeRef, Expr, Lit};
use hash_ir::ir;
use hash_reporting::macros::panic_on_span;

use super::{unpack, BlockAnd, BlockAndExtend, Builder};

impl<'tcx> Builder<'tcx> {
    /// Lower a simple literal into an [ir::Const], this does not deal
    /// with literals that are arrays or other compound data structures.
    pub(crate) fn as_constant(&mut self, lit: AstNodeRef<'tcx, Lit>) -> ir::Const {
        match lit.body {
            Lit::Str(literal) => ir::Const::Str(literal.data),
            Lit::Char(literal) => ir::Const::Char(literal.data),
            Lit::Int(literal) => ir::Const::Int(literal.value),
            Lit::Float(literal) => ir::Const::Float(literal.value),
            Lit::Bool(literal) => ir::Const::Byte(literal.data.into()),
            Lit::Set(_) | Lit::Map(_) | Lit::List(_) | Lit::Tuple(_) => {
                panic_on_span!(
                    lit.span().into_location(self.source_id),
                    self.source_map,
                    "cannot lower compound literal into constant"
                )
            }
        }
    }
}
