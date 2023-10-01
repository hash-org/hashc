use hash_reporting::diagnostic::Diagnostics;
use hash_target::{HasTarget, Target};
use hash_tir::{
    context::{Context, HasContext},
    intrinsics::make::IntrinsicAbilities,
    tir::TermId,
};
use hash_utils::derive_more::{Constructor, Deref};

use crate::{checker::Tc, env::TcEnv};

#[derive(Deref, Constructor)]
pub struct IntrinsicAbilitiesImpl<'tc, T: TcEnv> {
    tc: &'tc Tc<'tc, T>,
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
        self.tc
            .potentially_normalise(term.into())
            .map(|result| result.map(|r| r.to_term()))
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
