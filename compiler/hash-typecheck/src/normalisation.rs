//! Operations for normalising terms and types.
use derive_more::{Constructor, Deref};
use hash_tir::new::terms::TermId;

use crate::{errors::TcResult, AccessToTypechecking};

#[derive(Constructor, Deref)]
pub struct NormalisationOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> NormalisationOps<'_, T> {
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
