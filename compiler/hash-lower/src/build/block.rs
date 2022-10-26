use hash_ast::ast::{AstNodeRef, Block};
use hash_ir::ir::{BasicBlock, Place};

use super::{BlockAnd, Builder};

impl<'a, 'tcx> Builder<'a, 'tcx> {
    pub(crate) fn block_into_dest(
        &mut self,
        place: Place,
        block: BasicBlock,
        body: AstNodeRef<'a, Block>,
    ) -> BlockAnd<()> {
        todo!()
    }
}
