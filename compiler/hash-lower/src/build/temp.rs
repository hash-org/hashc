//! Lowering logic for compiling an [ast::Expr] into a temporary [Local].

use hash_ir::{
    ir::{BasicBlock, Local, LocalDecl, Place},
    ty::{Mutability, ReprTyId},
};
use hash_tir::tir::TermId;

use super::{BlockAnd, BodyBuilder};
use crate::build::{unpack, BlockAndExtend};

impl BodyBuilder<'_> {
    /// Compile an "term" into a freshly created temporary [Place].
    pub(crate) fn term_into_temp(
        &mut self,
        mut block: BasicBlock,
        term: TermId,
        mutability: Mutability,
    ) -> BlockAnd<Local> {
        let ty = self.ty_id_from_tir_term(term);
        let local = LocalDecl::new_auxiliary(ty, mutability);

        let temp = self.locals.push(local);
        let temp_place = Place::from_local(temp);

        unpack!(block = self.term_into_dest(temp_place, block, term));
        block.and(temp)
    }

    /// Create a temporary place with a given type.
    pub(crate) fn temp_place(&mut self, ty: ReprTyId) -> Place {
        let decl = LocalDecl::new_auxiliary(ty, Mutability::Immutable);

        Place::from_local(self.locals.push(decl))
    }
}
