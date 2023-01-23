//! Operations to substitute variables in types and terms.

use hash_tir::new::{args::ArgsId, defs::DefArgsId, params::ParamsId, terms::TermId, tys::TyId};
use hash_utils::store::SequenceStoreKey;

use crate::{errors::TcResult, subs::Sub, AccessToTypechecking};

pub(super) trait SubstituteOps: AccessToTypechecking {
    fn apply_sub_to_term(&self, term_id: TermId, _sub: &Sub) -> TermId {
        // @@Todo
        term_id
    }

    fn apply_sub_to_term_in_place(&self, _term_id: TermId, _sub: &Sub) {
        // @@Todo
    }

    fn apply_sub_to_ty(&self, ty_id: TyId, _sub: &Sub) -> TyId {
        // @@Todo
        ty_id
    }

    fn apply_sub_to_ty_in_place(&self, _ty_id: TyId, _sub: &Sub) {
        // @@Todo
    }

    fn apply_sub_to_args(&self, args_id: ArgsId, _sub: &Sub) -> ArgsId {
        // @@Todo
        args_id
    }

    fn apply_sub_to_params_in_place(&self, _params_id: ParamsId, _sub: &Sub) {
        // @@Todo
    }

    fn apply_sub_to_def_args_in_place(&self, _def_args_id: DefArgsId, _sub: &Sub) {
        // @@Todo
    }

    fn apply_sub_to_args_in_place(&self, _args_id: ArgsId, _sub: &Sub) {
        // @@Todo
    }

    /// Create a substitution from applying the arguments to the parameters.
    ///
    /// For argument terms `a1, a2, ..., an` and parameter indices `p1, p2, ...,
    /// pn` this creates a substitution `s` such that `s(p1) = a1, s(p2) =
    /// a2, ..., s(pn) = an`.
    fn create_sub_from_applying_args_to_params(
        &self,
        args_id: ArgsId,
        params_id: ParamsId,
    ) -> TcResult<Sub> {
        assert!(args_id.len() == params_id.len());
        todo!()
    }
}

impl<T: AccessToTypechecking> SubstituteOps for T {}
