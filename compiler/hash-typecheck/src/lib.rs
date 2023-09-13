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
use hash_reporting::diagnostic::{Diagnostics, HasDiagnostics};
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_target::{HasTarget, Target};
use hash_tir::{
    atom_info::HasAtomInfo,
    context::{Context, HasContext},
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

pub trait TcEnv: HasDiagnostics + HasTarget + HasContext + HasAtomInfo + Sized {
    /// Convert a typechecking error to a diagnostic error.
    ///
    /// Provided by the implementer.
    fn convert_tc_error(
        &self,
        error: TcError,
    ) -> <<Self as HasDiagnostics>::Diagnostics as Diagnostics>::Error;

    /// Convert an exhaustiveness error to a diagnostic error.
    fn convert_exhaustiveness_error(
        &self,
        error: ExhaustivenessError,
    ) -> <<Self as HasDiagnostics>::Diagnostics as Diagnostics>::Error;

    /// Convert an exhaustiveness warning to a diagnostic warning.
    fn convert_exhaustiveness_warning(
        &self,
        warning: ExhaustivenessWarning,
    ) -> <<Self as HasDiagnostics>::Diagnostics as Diagnostics>::Warning;

    /// Get the entry point of the current compilation, if any.
    fn entry_point(&self) -> &EntryPointState<FnDefId>;

    /// Whether the typechecker should monomorphise all pure functions.
    fn should_monomorphise(&self) -> bool;

    /// The current source ID.
    fn current_source(&self) -> SourceId;

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

pub struct IntrinsicAbilitiesWrapper<'tc, T: TcEnv> {
    tc: &'tc T,
}

impl<T: TcEnv> HasContext for IntrinsicAbilitiesWrapper<'_, T> {
    fn context(&self) -> &Context {
        self.tc.context()
    }
}

impl<T: TcEnv> HasTarget for IntrinsicAbilitiesWrapper<'_, T> {
    fn target(&self) -> &Target {
        self.tc.target()
    }
}

impl<T: TcEnv> IntrinsicAbilities for IntrinsicAbilitiesWrapper<'_, T> {
    fn normalise_term(&self, term: TermId) -> Result<Option<TermId>, String> {
        let norm = self.tc.norm_ops();

        norm.potentially_normalise(term.into())
            .map(|result| result.map(|r| norm.to_term(r)))
            .map_err(|e| {
                self.tc.diagnostics().add_error(self.tc.convert_tc_error(e));
                "normalisation error".to_string()
            })
    }

    fn resolve_from_prelude(
        &self,
        _name: impl Into<hash_source::identifier::Identifier>,
    ) -> TermId {
        // @@Todo: actually implement this to be able to resolve prelude items
        todo!()
    }
}
