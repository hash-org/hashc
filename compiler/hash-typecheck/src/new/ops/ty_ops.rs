use derive_more::Constructor;
use hash_types::new::{
    holes::{Hole, HoleKind},
    tys::{Ty, TyId},
};
use hash_utils::store::Store;

use crate::{
    impl_access_to_tc_env,
    new::data::env::{AccessToTcEnv, TcEnv},
};

#[derive(Constructor)]
pub struct TyOps<'tc> {
    env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(TyOps<'tc>);

impl<'tc> TyOps<'tc> {
    pub fn new_ty_hole(&self) -> TyId {
        let hole_id = self.stores().hole().create_with(|id| Hole { id, kind: HoleKind::Ty });
        self.stores().ty().create_with(|_id| Ty::Hole(hole_id))
    }
}
