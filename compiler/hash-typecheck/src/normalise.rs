//! Operations for normalising terms and types.
use hash_tir::new::terms::TermId;

use crate::{errors::TcResult, AccessToTypechecking};

pub(super) trait NormalisationOps: AccessToTypechecking {
    /// Turn a term to weak head normal form.
    fn standardise_term(&self, _term_id: TermId) -> TcResult<TermId> {
        todo!()
    }

    /// Turn a term to weak head normal form, or return `None` .
    fn potentially_standardise_term(&self, _term_id: TermId) -> TcResult<Option<TermId>> {
        todo!()
    }

    /// Reduce a term to normal form.
    fn potentially_normalise_term(&self, _term_id: TermId) -> TcResult<Option<TermId>> {
        todo!()
    }
}
