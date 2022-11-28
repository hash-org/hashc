//! Lowering logic for compiling an [Expr] into a temporary [Local].

use hash_ast::ast::{AstNodeRef, Expr};
use hash_ir::{
    ir::{BasicBlock, Local, LocalDecl, Place},
    ty::{IrTyId, Mutability},
};

use super::{BlockAnd, Builder};
use crate::build::{unpack, BlockAndExtend};

impl<'tcx> Builder<'tcx> {
    /// Compile an [Expr] into a freshly created temporary [Place].
    pub(crate) fn expr_into_temp(
        &mut self,
        mut block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
        mutability: Mutability,
    ) -> BlockAnd<Local> {
        let temp = {
            let ty = self.get_ty_id_of_node(expr.id());
            let local = LocalDecl::new_auxiliary(ty, mutability);
            let scope = self.current_scope();

            self.push_local(local, scope)
        };
        let temp_place = Place::from(temp);

        unpack!(block = self.expr_into_dest(temp_place, block, expr));
        block.and(temp)
    }

    /// Create a temporary place with a given type.
    pub(crate) fn temp_place(&mut self, ty: IrTyId) -> Place {
        let local = LocalDecl::new_auxiliary(ty, Mutability::Immutable);
        let scope = self.current_scope();

        let local = self.push_local(local, scope);
        Place::from(local)
    }
}
