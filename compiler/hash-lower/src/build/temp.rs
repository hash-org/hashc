//! Lowering logic for compiling an [ast::Expr] into a temporary [Local].

use hash_ir::{
    ir::{BasicBlock, Local, LocalDecl, Place},
    ty::{IrTyId, Mutability},
};
use hash_tir::tir::terms::TermId;

use super::{BlockAnd, BodyBuilder};
use crate::build::{unpack, BlockAndExtend};

impl<'tcx> BodyBuilder<'tcx> {
    /// Compile an "term" into a freshly created temporary [Place].
    pub(crate) fn term_into_temp(
        &mut self,
        mut block: BasicBlock,
        term: TermId,
        mutability: Mutability,
    ) -> BlockAnd<Local> {
        let ty = self.ty_id_from_tir_term(term);
        let local = LocalDecl::new_auxiliary(ty, mutability);

        let temp = self.declarations.push(local);
        let temp_place = Place::from_local(temp);

        unpack!(block = self.term_into_dest(temp_place, block, term));
        block.and(temp)
    }

    /// Create a temporary place with a given type.
    pub(crate) fn temp_place(&mut self, ty: IrTyId) -> Place {
        let decl = LocalDecl::new_auxiliary(ty, Mutability::Immutable);

        Place::from_local(self.declarations.push(decl))
    }
}
