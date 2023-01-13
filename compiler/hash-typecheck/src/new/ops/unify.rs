use derive_more::Constructor;
use hash_types::new::tys::TyId;

use crate::{
    impl_access_to_tc_env,
    new::{diagnostics::error::TcResult, environment::tc_env::TcEnv},
};

#[derive(Constructor)]
pub struct UnifyOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(UnifyOps<'tc>);

impl<'tc> UnifyOps<'tc> {
    pub fn unify_tys(&self, _src: TyId, _target: TyId) -> TcResult<TyId> {
        todo!()
    }
}
