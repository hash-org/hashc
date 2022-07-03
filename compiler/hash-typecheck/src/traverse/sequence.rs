//! Typechecking traversal sequence utilities. This file contains utility
//! functions that allow for the unification of a variadic list of terms
//! in order to perform specific operations.

use crate::{
    diagnostics::error::TcResult,
    ops::AccessToOpsMut,
    storage::{primitives::TermId, AccessToStorageMut},
};

use super::TcVisitor;

impl<'gs, 'ls, 'cd, 'src> TcVisitor<'gs, 'ls, 'cd, 'src> {
    /// Function used to verify a variadic sequence of terms. This ensures that
    /// the terms can all be unified.
    pub(crate) fn unify_term_sequence(
        &mut self,
        sequence: impl IntoIterator<Item = TermId>,
    ) -> TcResult<TermId> {
        let mut elements = sequence.into_iter().peekable();

        // Create a shared term that is used to verify all elements within the
        // list can be unified with one another, and then iterate over all of the
        // elements.

        let mut shared_term = self.builder().create_unresolved_term();

        while let Some(element) = elements.next() {
            let element_ty = self.typer().ty_of_term(element)?;
            let sub = self.unifier().unify_terms(element_ty, shared_term)?;

            // apply the substitution on the `shared_term`
            shared_term = self.substituter().apply_sub_to_term(&sub, shared_term);

            // Only add the position to the last term...
            if elements.peek().is_none() {
                self.location_store_mut().copy_location(element_ty, shared_term);
            }
        }

        Ok(shared_term)
    }
}
