//! Functionality related to pattern matching.

use itertools::Itertools;

use crate::{
    diagnostics::{error::TcResult, macros::tc_panic},
    ops::{validate::TermValidation, AccessToOpsMut},
    storage::{
        primitives::{IfPat, Member, MemberData, Pat, PatId, TermId},
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};

use super::{params::pair_args_with_params, AccessToOps};

/// Contains functions related to pattern matching.
pub struct PatMatcher<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for PatMatcher<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for PatMatcher<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> PatMatcher<'gs, 'ls, 'cd, 's> {
    /// Create a new [PatMatcher].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Match the given pattern with the given term, returning
    /// `Some(member_list)` if the pattern matches (with a list of bound
    /// members), or `None` if it doesn't match. If the types mismatch, it
    /// returns an error.
    pub fn match_pat_with_term(
        &mut self,
        pat_id: PatId,
        term_id: TermId,
    ) -> TcResult<Option<Vec<Member>>> {
        let TermValidation { simplified_term_id, term_ty_id } =
            self.validator().validate_term(term_id)?;
        let pat_ty = self.typer().infer_ty_of_pat(pat_id)?;

        // First unify the pattern type with the subject type to ensure the match is
        // valid:
        let _ = self.unifier().unify_terms(pat_ty, term_ty_id)?;

        let pat = self.reader().get_pat(pat_id).clone();
        match pat {
            // Binding: Add the binding as a member
            Pat::Binding(binding) => Ok(Some(vec![Member {
                name: binding.name,
                mutability: binding.mutability,
                visibility: binding.visibility,
                data: MemberData::from_ty_and_value(Some(term_ty_id), Some(simplified_term_id)),
                is_closed: true,
            }])),
            // Ignore: No bindings but always matches
            Pat::Ignore => Ok(Some(vec![])),
            // Lit: Unify the literal with the subject
            Pat::Lit(lit_term) => match self.unifier().unify_terms(lit_term, simplified_term_id) {
                Ok(_) => Ok(Some(vec![])),
                Err(_) => Ok(None),
            },
            // Tuple: Unify the tuple with the subject, and then recurse to inner patterns
            Pat::Tuple(tuple_pat_params_id) => {
                // Get the term of the tuple and try to unify it with the subject:
                let tuple_term = self.typer().get_term_of_pat(pat_id)?;
                match self.unifier().unify_terms(tuple_term, simplified_term_id) {
                    Ok(_) => {
                        let tuple_pat_params =
                            self.reader().get_pat_params(tuple_pat_params_id).clone();

                        // First, we get the tuple pattern parameters in the form of args (for
                        // `pair_args_with_params` error reporting):
                        let tuple_pat_params_as_args_id =
                            self.typer().infer_args_of_pat_params(tuple_pat_params_id)?;

                        // We get the subject tuple's parameters:
                        let subject_params_id = self
                            .typer()
                            .get_params_ty_of_tuple_term(simplified_term_id)?
                            .unwrap_or_else(|| {
                                tc_panic!(simplified_term_id, self, "This is not a tuple term.")
                            });
                        let subject_params = self.reader().get_params(subject_params_id).clone();

                        // For each param pair: accumulate the bound members
                        let bound_members = pair_args_with_params(
                            &subject_params,
                            &tuple_pat_params,
                            subject_params_id,
                            tuple_pat_params_as_args_id,
                            term_id,
                            pat_id,
                        )?
                        .into_iter()
                        .map(|(param, pat_param)| {
                            let param_value = param
                                .default_value
                                .unwrap_or_else(|| self.builder().create_rt_term(param.ty));

                            // @@Todo: retain information about useless patterns
                            Ok(self
                                .match_pat_with_term(pat_param.pat, param_value)?
                                .into_iter()
                                .flatten()
                                .collect::<Vec<_>>())
                        })
                        .flatten_ok()
                        .collect::<TcResult<Vec<_>>>()?;
                        Ok(Some(bound_members))
                    }
                    Err(_) => Ok(None),
                }
            }
            Pat::Mod(_) => {
                //  Here we have to basically try to access the given members using ns access...
                todo!()
            }
            Pat::Constructor(_) => {
                // Get the term of the constructor and try to unify it with the subject:
                let constructor_term = self.typer().get_term_of_pat(pat_id)?;
                match self.unifier().unify_terms(constructor_term, simplified_term_id) {
                    Ok(_) => {
                        // @@Todo: Get the vars:
                        Ok(Some(vec![]))
                    }
                    Err(_) => Ok(None),
                }
            }
            Pat::Or(_) => {
                // Here we have to get the union of all the pattern terms, and also need to
                // ensure that the bound variables are the same for each
                // branch and of the same type
                todo!()
            }
            Pat::If(IfPat { pat, .. }) => {
                // Recurse to inner, but never say it is redundant:
                match self.match_pat_with_term(pat, term_id)? {
                    Some(result) => Ok(Some(result)),
                    None => Ok(Some(vec![])),
                }
            }
        }
    }
}
