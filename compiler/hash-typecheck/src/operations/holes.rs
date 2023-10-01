use hash_storage::store::statics::StoreId;
use hash_tir::tir::{Hole, TermId, TyId, VarTerm};

use crate::{env::TcEnv, errors::TcResult, tc::Tc, traits::Operations};

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

impl<E: TcEnv> Operations<Hole> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _item: &mut Hole,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        // No-op
        Ok(())
    }

    fn normalise(
        &self,
        hole: Hole,
        item_node: Self::Node,
    ) -> crate::options::normalisation::NormaliseResult<Self::Node> {
        self.normalise(VarTerm { symbol: hole.0 }, item_node)
    }

    fn unify(
        &self,
        h1: &mut Hole,
        h2: &mut Hole,
        src_id: Self::Node,
        target_id: Self::Node,
    ) -> crate::errors::TcResult<()> {
        if h1 == h2 {
            Ok(())
        } else {
            // We can't unify two holes, so we have to block
            self.unification_blocked(src_id, target_id)
        }
    }
}
