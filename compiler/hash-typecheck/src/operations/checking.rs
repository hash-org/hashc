use hash_tir::tir::{NodeOrigin, Ty, TyId};

use crate::{checker::Checker, env::TcEnv, errors::TcResult};

impl<E: TcEnv> Checker<'_, E> {
    pub fn check_is_universe(&self, ty: TyId) -> TcResult<()> {
        self.uni_ops().unify_terms(ty, Ty::universe(NodeOrigin::Expected))
    }
}
