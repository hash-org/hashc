//! Functionality related to pattern matching.

use hash_ast::ast::ParamOrigin;
use itertools::Itertools;

use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::tc_panic,
    },
    ops::{unify::UnifyParamsWithArgsMode, validate::TermValidation, AccessToOpsMut},
    storage::{
        primitives::{
            AccessPat, ConstPat, ConstructorPat, IfPat, ListPat, Member, MemberData, Mutability,
            Pat, PatId, SpreadPat, TermId, Visibility,
        },
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

        let pat = self.reader().get_pat(pat_id).clone();

        // Note: for spread patterns, unifying between the `term` and the type
        // of the pattern doesn't make sense because the term will always be `T`
        // where the type of the spread is `List<T>`.
        if !matches!(pat, Pat::Spread(_)) {
            // unify the pattern type with the subject type to ensure the match is
            // valid:
            let _ = self.unifier().unify_terms(pat_ty, term_ty_id)?;
        }

        match pat {
            // Binding: Add the binding as a member
            Pat::Binding(binding) => Ok(Some(vec![Member::closed(
                binding.name,
                binding.visibility,
                binding.mutability,
                MemberData::from_ty_and_value(Some(term_ty_id), Some(simplified_term_id)),
            )])),
            Pat::Access(AccessPat { subject, property }) => {
                let subject_term = self.typer().get_term_of_pat(subject)?;
                let term = self.builder().create_ns_access(subject_term, property);

                match self.unifier().unify_terms(term, simplified_term_id) {
                    Ok(_) => Ok(Some(vec![])),
                    Err(_) => Ok(None),
                }
            }
            Pat::Const(ConstPat { term, .. }) => {
                match self.unifier().unify_terms(term, simplified_term_id) {
                    Ok(_) => Ok(Some(vec![])),
                    Err(_) => Ok(None),
                }
            }
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
            Pat::Constructor(ConstructorPat { params, .. }) => {
                // Get the term of the constructor and try to unify it with the subject:
                let constructor_term = self.typer().get_term_of_pat(pat_id)?;

                if let Some(params_id) = params {
                    let pat_args = self.typer().infer_args_of_pat_params(params_id)?;
                    let constructor_args = self.reader().get_pat_params(params_id).clone();

                    let possible_params =
                        self.typer().infer_params_ty_of_nominal_term(simplified_term_id)?;

                    for (_, params) in possible_params {
                        match self.unifier().unify_params_with_args(
                            params,
                            pat_args,
                            constructor_term,
                            simplified_term_id,
                            UnifyParamsWithArgsMode::UnifyParamTypesWithArgTypes,
                        ) {
                            Ok(_) => {
                                let subject_params = self.reader().get_params(params).clone();

                                let bound_members = pair_args_with_params(
                                    &subject_params,
                                    &constructor_args,
                                    params,
                                    pat_args,
                                    term_id,
                                    pat_id,
                                )?
                                .into_iter()
                                .map(|(param, pat_param)| {
                                    let param_value = param
                                        .default_value
                                        .unwrap_or_else(|| self.builder().create_rt_term(param.ty));

                                    Ok(self
                                        .match_pat_with_term(pat_param.pat, param_value)?
                                        .into_iter()
                                        .flatten()
                                        .collect::<Vec<_>>())
                                })
                                .flatten_ok()
                                .collect::<TcResult<Vec<_>>>()?;

                                return Ok(Some(bound_members));
                            }
                            Err(_) => continue,
                        }
                    }

                    return Err(TcError::NoConstructorOnType { subject: constructor_term });
                }

                Ok(Some(vec![]))
            }
            Pat::List(ListPat { term, inner }) => {
                // We need to collect all of the binds from the inner patterns of
                // the list
                let params = self.reader().get_pat_params(inner).clone();

                let mut bound_members = vec![];

                let shared_term = self.builder().create_rt_term(term);

                for param in params.positional().iter() {
                    match self.match_pat_with_term(param.pat, shared_term)? {
                        Some(members) => {
                            bound_members.extend(members);
                        }
                        // If one of them fails, we should fail as a whole
                        None => return Ok(None),
                    }
                }

                Ok(Some(bound_members))
            }
            Pat::Spread(SpreadPat { name }) => match name {
                Some(name) => {
                    // Since `pat_ty` will be `List<T = Unresolved>`, we need to create a new
                    // `List<T = term_ty_id>` and perform a unification...
                    let list_inner_ty = self.core_defs().list_ty_fn;
                    let builder = self.builder();

                    let pat_ty = builder.create_app_ty_fn_term(
                        list_inner_ty,
                        builder.create_args(
                            [builder.create_nameless_arg(term_ty_id)],
                            ParamOrigin::TyFn,
                        ),
                    );

                    let rt_term = self.builder().create_rt_term(pat_ty);

                    let TermValidation { simplified_term_id, term_ty_id } =
                        self.validator().validate_term(rt_term)?;

                    Ok(Some(vec![Member::closed(
                        name,
                        Visibility::Private,
                        Mutability::Immutable,
                        MemberData::from_ty_and_value(Some(term_ty_id), Some(simplified_term_id)),
                    )]))
                }
                _ => Ok(Some(vec![])),
            },
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
