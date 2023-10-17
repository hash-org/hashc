use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::tir::{Hole, TermId, TyId, VarTerm};

use crate::{
    diagnostics::TcResult, env::TcEnv, options::normalisation::NormaliseResult, tc::Tc,
    traits::OperationsOn,
};

impl<E: TcEnv> Tc<'_, E> {
    /// Unify two holes.
    ///
    /// This modifies src to have the contents of dest, and adds a unification
    /// to the context.
    pub fn unify_hole_with(&self, hole: Hole, hole_src: TermId, sub_dest: TermId) -> TcResult<()> {
        if self.unification_opts.modify_terms.get() {
            hole_src.set(sub_dest.value());
        }
        self.add_unification(hole.0, sub_dest);
        Ok(())
    }
}

impl<E: TcEnv> OperationsOn<Hole> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _item: &mut Hole,
        _item_ty: Self::AnnotNode,
        _item_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        // No-op
        Ok(())
    }

    fn try_normalise(
        &self,
        hole: Hole,
        item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        self.try_normalise(VarTerm { symbol: hole.0 }, item_node)
    }

    fn unify(
        &self,
        h1: &mut Hole,
        h2: &mut Hole,
        src_id: Self::Node,
        target_id: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        if h1 == h2 {
            Ok(())
        } else {
            // We can't unify two holes, so we have to block
            self.unification_blocked(src_id, target_id)
        }
    }
}
