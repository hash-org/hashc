//! Contains definitions related to intrinsics
pub mod definitions;
pub mod make;

use hash_source::identifier::Identifier;

use crate::{environment::env::Env, fns::FnTy, terms::TermId};

pub trait IntrinsicAbilities {
    /// Normalise a term fully.
    fn normalise_term(&self, term: TermId) -> Result<Option<TermId>, String>;

    /// Resolve a term from the prelude.
    fn resolve_from_prelude(&self, name: impl Into<Identifier>) -> TermId;

    /// Get the current environment.
    fn env(&self) -> &Env;
}

pub trait IsIntrinsic {
    /// Get the name of the intrinsic.
    fn name(&self) -> Identifier;

    /// Get the function type of the intrinsic.
    fn ty(&self) -> FnTy;

    /// Get the implementation of the intrinsic.
    fn call<I: IntrinsicAbilities>(
        &self,
        env: I,
        args: &[TermId],
    ) -> Result<Option<TermId>, String>;
}
