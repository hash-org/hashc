//! Operations for normalising terms and types.
use derive_more::Constructor;
use hash_tir::new::terms::TermId;

use crate::{
    impl_access_to_tc_env,
    new::{diagnostics::error::TcResult, environment::tc_env::TcEnv},
};

#[derive(Constructor)]
pub struct NormalisationOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(NormalisationOps<'tc>);

impl<'tc> NormalisationOps<'tc> {
    /// Turn a term to weak head normal form.
    pub fn standardise_term(&self, _term_id: TermId) -> TcResult<TermId> {
        todo!()
    }

    /// Turn a term to weak head normal form, or return `None` .
    pub fn potentially_standardise_term(&self, _term_id: TermId) -> TcResult<Option<TermId>> {
        todo!()
    }

    /// Reduce a term to normal form.
    pub fn potentially_normalise_term(&self, _term_id: TermId) -> TcResult<Option<TermId>> {
        todo!()
    }
}
