#![feature(
    unwrap_infallible,
    never_type,
    try_trait_v2,
    try_blocks,
    control_flow_enum,
    let_chains,
    if_let_guard
)]

use errors::TcError;
use hash_exhaustiveness::diagnostics::{ExhaustivenessError, ExhaustivenessWarning};
use hash_reporting::diagnostic::{AccessToDiagnostics, Diagnostics};
use hash_source::entry_point::EntryPointState;
use hash_target::HasTarget;
use hash_tir::{
    environment::env::{AccessToEnv, Env},
    fns::FnDefId,
    intrinsics::make::IntrinsicAbilities,
    terms::TermId,
};
use inference::InferenceOps;
use substitution::SubstitutionOps;
use unification::UnificationOps;

pub mod errors;
pub mod inference;
pub mod normalisation;
pub mod substitution;
pub mod unification;

pub trait AccessToTypechecking: AccessToEnv + AccessToDiagnostics + Sized {
    /// Convert a typechecking error to a diagnostic error.
    ///
    /// Provided by the implementer.
    fn convert_tc_error(
        &self,
        error: TcError,
    ) -> <<Self as AccessToDiagnostics>::Diagnostics as Diagnostics>::Error;

    /// Convert an exhaustiveness error to a diagnostic error.
    fn convert_exhaustiveness_error(
        &self,
        error: ExhaustivenessError,
    ) -> <<Self as AccessToDiagnostics>::Diagnostics as Diagnostics>::Error;

    /// Convert an exhaustiveness warning to a diagnostic warning.
    fn convert_exhaustiveness_warning(
        &self,
        warning: ExhaustivenessWarning,
    ) -> <<Self as AccessToDiagnostics>::Diagnostics as Diagnostics>::Warning;

    /// Get the entry point of the current compilation, if any.
    fn entry_point(&self) -> &EntryPointState<FnDefId>;

    /// Whether the typechecker should monomorphise all pure functions.
    fn should_monomorphise(&self) -> bool;

    fn infer_ops(&self) -> InferenceOps<Self> {
        InferenceOps::new(self)
    }

    fn sub_ops(&self) -> SubstitutionOps<Self> {
        SubstitutionOps::new(self)
    }

    fn uni_ops(&self) -> UnificationOps<Self> {
        UnificationOps::new(self)
    }

    fn norm_ops(&self) -> normalisation::NormalisationOps<Self> {
        normalisation::NormalisationOps::new(self)
    }
}

pub struct IntrinsicAbilitiesWrapper<'tc, T: AccessToTypechecking> {
    tc: &'tc T,
}

impl<T: AccessToTypechecking> IntrinsicAbilities for IntrinsicAbilitiesWrapper<'_, T> {
    fn normalise_term(&self, term: TermId) -> Result<Option<TermId>, String> {
        let norm = self.tc.norm_ops();

        norm.potentially_normalise(term.into())
            .map(|result| result.map(|r| norm.to_term(r)))
            .map_err(|e| {
                self.tc.diagnostics().add_error(self.tc.convert_tc_error(e));
                "normalisation error".to_string()
            })
    }

    fn env(&self) -> &Env {
        self.tc.env()
    }

    fn resolve_from_prelude(
        &self,
        _name: impl Into<hash_source::identifier::Identifier>,
    ) -> TermId {
        todo!()
    }
}
