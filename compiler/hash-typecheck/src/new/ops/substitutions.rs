//! Operations to substitute variables in types and terms.
use derive_more::Constructor;
use hash_types::new::{args::ArgsId, params::ParamsId, terms::TermId, tys::TyId};

use crate::{
    impl_access_to_tc_env,
    new::{diagnostics::error::TcResult, environment::tc_env::TcEnv, primitives::subs::Sub},
};

#[derive(Constructor)]
pub struct SubstituteOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(SubstituteOps<'tc>);

impl<'tc> SubstituteOps<'tc> {
    pub fn apply_sub_to_term(&self, _term_id: TermId, _sub: &Sub) -> TermId {
        todo!()
    }

    pub fn apply_sub_to_ty(&self, _ty_id: TyId, _sub: &Sub) -> TyId {
        todo!()
    }

    pub fn apply_sub_to_args(&self, _args_id: ArgsId, _sub: &Sub) -> TermId {
        todo!()
    }

    pub fn apply_sub_to_args_in_place(&self, _args_id: ArgsId, _sub: &Sub) {
        todo!()
    }

    /// Create a substitution from applying the arguments to the parameters.
    ///
    /// For argument terms `a1, a2, ..., an` and parameter indices `p1, p2, ...,
    /// pn` this creates a substitution `s` such that `s(p1) = a1, s(p2) =
    /// a2, ..., s(pn) = an`.
    pub fn create_sub_from_applying_args_to_params(
        &self,
        _args_id: ArgsId,
        _params_id: ParamsId,
    ) -> TcResult<Sub> {
        todo!()
    }
}
