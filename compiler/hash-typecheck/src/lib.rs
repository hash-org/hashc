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
use hash_pipeline::settings::HasCompilerSettings;
use hash_reporting::diagnostic::{Diagnostics, HasDiagnostics};
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_target::{HasTarget, Target};
use hash_tir::{
    atom_info::HasAtomInfo,
    context::{Context, HasContext},
    intrinsics::make::IntrinsicAbilities,
    tir::{FnDefId, TermId},
};
use hash_utils::timing::HasMetrics;
use inference::InferenceOps;
use substitution::SubstitutionOps;
use unification::UnificationOps;

pub mod errors;
pub mod inference;
pub mod normalisation;
pub mod substitution;
pub mod unification;

pub trait HasTcDiagnostics: HasDiagnostics<Diagnostics = Self::TcDiagnostics> {
    type ForeignError: From<TcError> + From<ExhaustivenessError>;
    type ForeignWarning: From<ExhaustivenessWarning>;
    type TcDiagnostics: Diagnostics<Error = Self::ForeignError, Warning = Self::ForeignWarning>;
}

pub trait TcEnv:
    HasTcDiagnostics + HasTarget + HasContext + HasMetrics + HasAtomInfo + HasCompilerSettings + Sized
{
    /// Get the entry point of the current compilation, if any.
    fn entry_point(&self) -> &EntryPointState<FnDefId>;

    /// The current source ID.
    fn current_source(&self) -> SourceId;

    /// Whether the typechecker should monomorphise all pure functions.
    fn should_monomorphise(&self) -> bool {
        self.settings().semantic_settings.mono_tir
    }

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

pub struct IntrinsicAbilitiesImpl<'tc, T: TcEnv> {
    tc: &'tc T,
}

impl<T: TcEnv> HasContext for IntrinsicAbilitiesImpl<'_, T> {
    fn context(&self) -> &Context {
        self.tc.context()
    }
}

impl<T: TcEnv> HasTarget for IntrinsicAbilitiesImpl<'_, T> {
    fn target(&self) -> &Target {
        self.tc.target()
    }
}

impl<T: TcEnv> IntrinsicAbilities for IntrinsicAbilitiesImpl<'_, T> {
    fn normalise_term(&self, term: TermId) -> Result<Option<TermId>, String> {
        let norm = self.tc.norm_ops();

        norm.potentially_normalise(term.into())
            .map(|result| result.map(|r| norm.to_term(r)))
            .map_err(|e| {
                self.tc.diagnostics().add_error(e.into());
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
