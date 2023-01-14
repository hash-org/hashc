//! Operations for unifying types.
use derive_more::Constructor;
use hash_types::new::{params::ParamsId, tys::TyId};

use crate::{
    impl_access_to_tc_env,
    new::{diagnostics::error::TcResult, environment::tc_env::TcEnv, primitives::subs::Sub},
};

#[derive(Constructor)]
pub struct UnifyOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(UnifyOps<'tc>);

impl<'tc> UnifyOps<'tc> {
    /// Unify two types, creating a substitution of holes.
    pub fn unify_tys(&self, _src: TyId, _target: TyId) -> TcResult<TyId> {
        todo!()
    }

    /// Unify two parameter lists, creating a substitution of holes.
    pub fn unify_params(&self, _src: ParamsId, _target: ParamsId) -> TcResult<Sub> {
        todo!()
    }

    /// Unify two terms, creating a substitution of holes.
    pub fn unify_terms(&self, _src: TyId, _target: TyId) -> TcResult<Sub> {
        todo!()
    }
}
