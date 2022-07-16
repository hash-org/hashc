//! Functionality related to pattern matching.

use crate::{
    diagnostics::error::TcResult,
    ops::{validate::TermValidation, AccessToOpsMut},
    storage::{
        primitives::{Member, MemberData, Pattern, PatternId, TermId},
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};

use super::AccessToOps;

/// Contains functions related to pattern matching.
pub struct PatternMatcher<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for PatternMatcher<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for PatternMatcher<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> PatternMatcher<'gs, 'ls, 'cd, 's> {
    /// Create a new [PatternMatcher].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Match the given pattern with the given term, returning
    /// `Some(member_list)` if the pattern matches (with a list of bound
    /// members), or `None` if it doesn't match. If the types mismatch, it
    /// returns an error.
    pub fn match_pattern_with_term(
        &mut self,
        pattern_id: PatternId,
        term_id: TermId,
    ) -> TcResult<Option<Vec<Member>>> {
        let TermValidation { simplified_term_id, term_ty_id } =
            self.validator().validate_term(term_id)?;
        let pattern_ty = self.typer().ty_of_pattern(pattern_id)?;

        // First unify the pattern type with the subject type to ensure the match is
        // valid:
        let _ = self.unifier().unify_terms(pattern_ty, term_ty_id)?;

        let pattern = self.reader().get_pattern(pattern_id).clone();
        match pattern {
            Pattern::Binding(binding) => Ok(Some(vec![Member {
                name: binding.name,
                mutability: binding.mutability,
                visibility: binding.visibility,
                data: MemberData::from_ty_and_value(Some(term_ty_id), Some(simplified_term_id)),
            }])),
            Pattern::Ignore => Ok(Some(vec![])),
            Pattern::Lit(lit_term) => {
                match self.unifier().unify_terms(lit_term, simplified_term_id) {
                    Ok(_) => Ok(Some(vec![])),
                    Err(_) => Ok(None),
                }
            }
            Pattern::Tuple(_) => {
                // Get the term of the tuple and try to unify it with the subject:
                let tuple_term = self.typer().term_of_pattern(pattern_id)?;
                match self.unifier().unify_terms(tuple_term, simplified_term_id) {
                    Ok(_) => {
                        // @@Todo: Get the vars:
                        Ok(Some(vec![]))
                    }
                    Err(_) => Ok(None),
                }
            }
            Pattern::Mod(_) => {
                //  Here we have to basically try to access the given members using ns access...
                todo!()
            }
            Pattern::Constructor(_) => {
                // Get the term of the constructor and try to unify it with the subject:
                let tuple_term = self.typer().term_of_pattern(pattern_id)?;
                match self.unifier().unify_terms(tuple_term, simplified_term_id) {
                    Ok(_) => {
                        // @@Todo: Get the vars:
                        Ok(Some(vec![]))
                    }
                    Err(_) => Ok(None),
                }
            }
            Pattern::Or(_) => {
                todo!()
            }
            Pattern::If(_) => todo!(),
        }
    }
}
