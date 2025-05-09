//! Wrapper around the typechecker to provide an interface to
//! intrinsic functions.

use derive_more::{Constructor, Deref};
use hash_reporting::diagnostic::Diagnostics;
use hash_repr::{HasLayout, compute::LayoutComputer};
use hash_source::identifier::Identifier;
use hash_target::{HasTarget, Target};
use hash_tir::{
    context::{Context, HasContext},
    intrinsics::make::IntrinsicAbilities,
    tir::TermId,
};

use crate::{env::TcEnv, tc::Tc};

/// Wrapper around the typechecker to provide an interface to
/// intrinsic functions.
///
/// Intrinsic functions expect something that implements `IntrinsicAbilities`,
/// which is implemented for this struct.
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

impl<T: TcEnv> HasLayout for IntrinsicAbilitiesImpl<'_, T> {
    fn layout_computer(&self) -> LayoutComputer {
        self.tc.layout_computer()
    }
}

impl<T: TcEnv> IntrinsicAbilities for IntrinsicAbilitiesImpl<'_, T> {
    fn normalise_term(&self, term: TermId) -> Result<Option<TermId>, String> {
        // Allow intrinsics to normalise terms through the typechecker:
        self.tc.potentially_normalise_node_no_signals(term).map_err(|e| {
            self.tc.diagnostics().add_error(e.into());
            "normalisation error".to_string()
        })
    }

    fn resolve_from_prelude(&self, _name: impl Into<Identifier>) -> TermId {
        // @@Todo: actually implement this to be able to resolve prelude items
        todo!()
    }
}
