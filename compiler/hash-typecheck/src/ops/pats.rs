//! Functionality related to pattern matching.

use std::collections::{HashMap, HashSet};

use hash_ast::ast::ParamOrigin;
use hash_source::identifier::Identifier;
use itertools::Itertools;

use super::{params::pair_args_with_params, AccessToOps};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::tc_panic,
    },
    ops::validate::TermValidation,
    storage::{
        pats::PatId,
        primitives::{
            AccessOp, AccessPat, ConstPat, ConstructorPat, IfPat, ListPat, Member, ModPat,
            Mutability, Param, Pat, PatArg, SpreadPat,
        },
        terms::TermId,
        AccessToStorage, StorageRef,
    },
};

/// Contains functions related to pattern matching.
pub struct PatMatcher<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for PatMatcher<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> PatMatcher<'tc> {
    /// Create a new [PatMatcher].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Internal function to infer a pattern from a `Param`.
    fn param_to_pat(&self, param: &Param) -> PatArg {
        let Param { name, default_value, .. } = param;
        let pat = self.builder().create_constant_pat(default_value.unwrap());

        PatArg { name: *name, pat }
    }

    /// Internal function to verify that the members that are produced from
    /// traversing a pattern are only binded once.
    pub fn verify_members_are_bound_once(&self, members: &[(Member, PatId)]) -> TcResult<()> {
        let mut names: HashSet<Identifier> = HashSet::new();

        for (member, pat) in members.iter() {
            if names.contains(&member.name()) {
                return Err(TcError::IdentifierBoundMultipleTimes {
                    name: member.name(),
                    pat: *pat,
                });
            } else {
                names.insert(member.name());
            }
        }

        Ok(())
    }

    /// Convert a list of [Member]s with their corresponding [PatId] into map
    /// between the [Member] binding name, the type of the member and the
    /// [PatId].
    ///
    /// **Note**: This function assumes that the uniqueness of the members has
    /// been checked before creating the map.
    fn map_variables_to_terms(
        &self,
        members: &[(Member, PatId)],
    ) -> HashMap<Identifier, (TermId, PatId)> {
        members.iter().map(|(member, pat)| (member.name(), (member.ty(), *pat))).collect()
    }

    /// Function to check that the inner patterns of a [Pat::Or] adhere to the
    /// following rule:
    ///
    /// - For every inner pattern, the resultant members must be equivalent in
    ///   terms of name and type.
    fn pat_members_match(&self, members: &[(Vec<(Member, PatId)>, PatId)]) -> TcResult<()> {
        let member_maps = members
            .iter()
            .map(|(members, pat)| (self.map_variables_to_terms(members), pat))
            .collect_vec();

        // Take the first member as we'll use it for our comparison
        let mut members = member_maps.iter();
        let (first_map, first_pat_id) = members.next().unwrap();
        let first_binds = first_map.keys().copied().collect::<HashSet<Identifier>>();

        // Compute the difference in `name` keys, if there exists a
        // difference then we can immediately report the error and abort...
        //
        // @@ErrorReporting: It would be nice to produce multiple errors here
        for (member, cur_pat_id) in members {
            // We want to find the largest member and report that that member doesn't
            // contain the binds...
            let cur_binds = member.keys().copied().collect::<HashSet<Identifier>>();

            let (mut diff, pat) = if first_binds.len() > cur_binds.len() {
                (first_binds.difference(&cur_binds).peekable(), *cur_pat_id)
            } else {
                (cur_binds.difference(&first_binds).peekable(), *first_pat_id)
            };

            // If there is at-least one discrepancy, we want to generate the report already
            if diff.peek().is_some() {
                return Err(TcError::MissingPatternBounds {
                    pat: *pat,
                    bounds: diff.copied().collect_vec(),
                });
            }
        }

        // Now we need to verify that all of the member binds are of the
        // same type...
        for bind in first_binds {
            let shared_terms =
                member_maps.iter().map(|(map, _)| map.get(&bind).unwrap()).copied().collect_vec();

            self.unifier().unify_pat_terms(shared_terms)?;
        }

        Ok(())
    }

    /// Match the given pattern with the given term, returning a potential list
    /// of extracted `binds` that the pattern describes.
    ///
    /// @@Fixme Re-work level 0 unification (i.e. should never work when Rts are
    /// involved), and that this function should unify the types, rather
    /// than the values, of the pattern and term.
    fn match_pat_with_term_and_extract_binds(
        &self,
        pat_id: PatId,
        term_id: TermId,
    ) -> TcResult<Option<Vec<(Member, PatId)>>> {
        let TermValidation { simplified_term_id, term_ty_id } =
            self.validator().validate_term(term_id)?;

        let pat = self.reader().get_pat(pat_id);
        let pat_ty = self.typer().infer_ty_of_pat(pat_id)?;

        // Note: for spread patterns, unifying between the `term` and the type
        // of the pattern doesn't make sense because the term will always be `T`
        // where the type of the spread is `List<T>`.
        //
        // @@Todo: do this in the Pat::List loop below rather than here.. For spread
        // patterns the term_id should be List<T>.
        if !matches!(pat, Pat::Spread(_)) {
            // unify the pattern type with the subject type to ensure the match is
            // valid:
            let _ = self.unifier().unify_terms(pat_ty, term_ty_id)?;
        }

        let bound_members = match pat {
            // Binding: Add the binding as a member
            Pat::Binding(binding) => Ok(Some(vec![(
                Member::variable(binding.name, binding.mutability, term_ty_id, simplified_term_id),
                pat_id,
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
            // No bindings in range patterns
            //
            // @@Todo: we could add a check in the future that tries to see if this is a useful
            // match?
            Pat::Range(_) => Ok(Some(vec![])),
            // No bindings but always matches
            Pat::Wild => Ok(Some(vec![])),
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
                        let tuple_pat_args =
                            self.reader().get_pat_args_owned(tuple_pat_params_id).clone();

                        // First, we get the tuple pattern parameters in the form of args (for
                        // `pair_args_with_params` error reporting):
                        let tuple_pat_params_as_args_id =
                            self.typer().infer_args_of_pat_args(tuple_pat_params_id)?;

                        // We get the subject tuple's parameters:
                        let subject_params_id = self
                            .typer()
                            .infer_params_ty_of_tuple_term(simplified_term_id)?
                            .unwrap_or_else(|| {
                                tc_panic!(simplified_term_id, self, "This is not a tuple term.")
                            });
                        let subject_params =
                            self.reader().get_params_owned(subject_params_id).clone();

                        // For each param pair: accumulate the bound members
                        let bound_members = pair_args_with_params(
                            &subject_params,
                            &tuple_pat_args,
                            subject_params_id,
                            tuple_pat_params_as_args_id,
                            |param| self.param_to_pat(param),
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
                                .match_pat_with_term_and_extract_binds(pat_param.pat, param_value)?
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
            Pat::Mod(ModPat { members }) => {
                let members = self.reader().get_pat_args_owned(members).clone();

                let mut bound_members = vec![];

                //  Here we have to basically try to access the given members using ns access...
                for member in members.positional() {
                    let PatArg { name, pat } = *member;

                    // Before we recurse into the inner pattern, we need to
                    // create an access term that accesses `name` from the
                    // current term... and then we recurse into pattern
                    let term =
                        self.builder().create_access(term_id, name.unwrap(), AccessOp::Namespace);

                    // If one of them fails, then we have to fail as a whole
                    match self.match_pat_with_term_and_extract_binds(pat, term)? {
                        Some(inner_members) => bound_members.extend(inner_members),
                        None => return Ok(None),
                    }
                }

                Ok(Some(bound_members))
            }
            Pat::Constructor(ConstructorPat { args, .. }) => {
                // Get the term of the constructor and try to unify it with the subject:
                let constructor_term = self.typer().get_term_of_pat(pat_id)?;

                let pat_args = self.typer().infer_args_of_pat_args(args)?;
                let constructor_args = self.reader().get_pat_args_owned(args).clone();

                let possible_params =
                    self.typer().infer_constructors_of_nominal_term(simplified_term_id)?;

                for (_, params) in possible_params {
                    let subject_params = self.reader().get_params_owned(params).clone();

                    match pair_args_with_params(
                        &subject_params,
                        &constructor_args,
                        params,
                        pat_args,
                        |param| self.param_to_pat(param),
                        term_id,
                        pat_id,
                    ) {
                        Ok(members) => {
                            let bound_members = members
                                .into_iter()
                                .map(|(param, arg)| {
                                    let param_value = param
                                        .default_value
                                        .unwrap_or_else(|| self.builder().create_rt_term(param.ty));

                                    Ok(self
                                        .match_pat_with_term_and_extract_binds(
                                            arg.pat,
                                            param_value,
                                        )?
                                        .into_iter()
                                        .flatten()
                                        .collect::<Vec<_>>())
                                })
                                .flatten_ok()
                                .collect::<TcResult<Vec<_>>>()?;

                            // @@Refactor: we need to verify that the members are declared once.
                            // Since this happens at the bottom of the
                            // function already, it would be nice to
                            // factor out this step to be at the bottom or factor out constructor
                            // pattern checking into a separate
                            // function.
                            self.verify_members_are_bound_once(&bound_members)?;
                            return Ok(Some(bound_members));
                        }
                        Err(_) => continue,
                    }
                }

                Err(TcError::NoConstructorOnType { subject: constructor_term })
            }
            Pat::List(ListPat { term, inner }) => {
                // We need to collect all of the binds from the inner patterns of
                // the list
                let params = self.reader().get_pat_args_owned(inner).clone();

                let mut bound_members = vec![];

                let shared_term = self.builder().create_rt_term(term);

                for param in params.positional().iter() {
                    match self.match_pat_with_term_and_extract_binds(param.pat, shared_term)? {
                        Some(members) => {
                            bound_members.extend(members);
                        }
                        // If one of them fails, we should fail as a whole
                        None => return Ok(None),
                    }
                }

                Ok(Some(bound_members))
            }
            Pat::Spread(SpreadPat { name, .. }) => match name {
                Some(name) => {
                    // Since `pat_ty` will be `List<T = Unresolved>`, we need to create a new
                    // `List<T = term_ty_id>` and perform a unification...
                    let list_inner_ty = self.core_defs().list_ty_fn();
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

                    Ok(Some(vec![(
                        Member::variable(
                            name,
                            Mutability::Immutable,
                            term_ty_id,
                            simplified_term_id,
                        ),
                        pat_id,
                    )]))
                }
                _ => Ok(Some(vec![])),
            },
            Pat::Or(pats) => {
                // Traverse all of the inner patterns within the `or` pattern, create a
                // map between the member names that are produced and the type of the
                // pattern... Then we want to ensure all of them are equal
                let pat_members = pats
                    .iter()
                    .map(|pat| {
                        self.match_pat_with_term_and_extract_binds(*pat, term_id)
                            .map(|m| m.map(|t| (t, *pat)))
                    })
                    .flatten_ok()
                    .collect::<TcResult<Vec<_>>>()?;

                // One of the cases never matches with the subject if the length is not the same
                if pat_members.len() != pats.len() {
                    return Ok(None);
                }

                self.pat_members_match(&pat_members)?;

                // Since all verification happens, we can now return the first member
                // since we know that all of the types are the same, and all the binds
                // will be in scope, regardless of which pattern is matched at runtime
                Ok(Some(pat_members[0].0.clone()))
            }
            Pat::If(IfPat { pat, .. }) => {
                // Recurse to inner, but never say it is redundant:
                match self.match_pat_with_term_and_extract_binds(pat, term_id)? {
                    Some(result) => Ok(Some(result)),
                    None => Ok(Some(vec![])),
                }
            }
        }?;

        // Here, we verify that the produced members from the pattern are unique...
        if let Some(members) = bound_members {
            self.verify_members_are_bound_once(&members)?;

            Ok(Some(members))
        } else {
            Ok(None)
        }
    }

    /// Match the given pattern with the given term, returning
    /// [`Vec<Member>`] if the pattern matches (with a list of bound
    /// members), or [`None`] if it doesn't match. If the types mismatch, it
    /// returns an error.
    pub fn match_pat_with_term(
        &self,
        pat_id: PatId,
        term_id: TermId,
    ) -> TcResult<Option<Vec<Member>>> {
        self.match_pat_with_term_and_extract_binds(pat_id, term_id)
            .map(|members| members.map(|inner| inner.into_iter().map(|(m, _)| m).collect()))
    }
}
