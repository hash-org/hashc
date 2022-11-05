use hash_ast::ast::{AstNodeRef, Expr};
use hash_ir::ir::{BasicBlock, RValueId};
use hash_utils::store::Store;

use super::{BlockAnd, BlockAndExtend, Builder};

impl<'tcx> Builder<'tcx> {
    /// Construct an [RValue] from the given [Expr] and return the [RValueId].
    pub(crate) fn as_rvalue(
        &mut self,
        block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
    ) -> BlockAnd<RValueId> {
        // @@Todo: use a notion of `categories` to determine if we should
        // lower it as a constant or else, the `category` is derived from
        // the expression itself,
        let rvalue = match expr.body {
            Expr::Lit(lit) => self.as_constant(lit.data.ast_ref()).into(),
            _ => unimplemented!(),
        };

        let rvalue_id = self.storage.rvalue_store().create(rvalue);
        block.and(rvalue_id)
    }
}
