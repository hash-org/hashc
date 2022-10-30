//! Utilities related to type unification and substitution.
use std::{borrow::Borrow, collections::HashSet};

use hash_types::{
    args::{Arg, ArgsId},
    location::LocationTarget,
    params::{Param, ParamsId},
    pats::PatId,
    scope::{ScopeId, ScopeKind},
    terms::{Level0Term, Level1Term, Level2Term, Level3Term, Sub, Term, TermId},
};
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey};

use super::{params::pair_args_with_params, AccessToOps};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::{tc_panic, tc_panic_on_many},
        params::ParamUnificationErrorReason,
    },
    storage::{AccessToStorage, StorageRef},
};

/// Options that are received by the unifier when unifying types.
pub struct UnifyTysOpts {}

/// Performs type unification and other related operations.
pub struct Unifier<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for Unifier<'tc> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'tc> Unifier<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Get the super-substitution of the two substitutions.
    ///
    /// Equivalent to first unifying `U(s0, s1)` and then applying `s1` or `s0`.
    pub(crate) fn get_super_sub(&self, s0: &Sub, s1: &Sub) -> TcResult<Sub> {
        let fv_s1 = self.discoverer().get_free_sub_vars_in_sub(s1);
        let dom_s0: HashSet<_> = s0.domain().collect();
        if fv_s1.intersection(&dom_s0).next().is_some() {
            panic!("Super-sub is not well formed!");
        }
        Ok(self.unify_subs(s0, s1)?.with_extension(s0))
    }

    /// Unify two substitutions to produce another substitution which is the
    /// unifier of the two.
    ///
    /// The resultant substitution contains all the information of the two
    /// source substitutions, without any common free variables in their
    /// domains.
    ///
    /// This implements the algorithm outlined in the paper:
    /// <https://www.researchgate.net/publication/221600544_On_the_Unification_of_Substitutions_in_Type_Interfaces>
    pub(crate) fn unify_subs(&self, s0: &Sub, s1: &Sub) -> TcResult<Sub> {
        let dom_s0: HashSet<_> = s0.domain().collect();
        let dom_s1: HashSet<_> = s1.domain().collect();
        let substituter = self.substituter();

        // First split the domains into three parts: d0, d1 (not directly needed), and
        // the intersection (see second loop)
        let d0: HashSet<_> = dom_s0.difference(&dom_s1).copied().collect();
        let d1: HashSet<_> = dom_s1.difference(&dom_s0).copied().collect();
        let t0 = Sub::from_pairs(d0.iter().map(|&a| (a, substituter.apply_sub_to_subject(s0, a))));
        let t1 = Sub::from_pairs(d1.iter().map(|&a| (a, substituter.apply_sub_to_subject(s1, a))));

        // Start with t0 and add terms for d1 one at a time, always producing well
        // formed substitutions
        let mut result = t0;
        for (a, t) in t1.pairs() {
            // Remove elements of dom(result) from t, and remove a from result.
            let subbed_t = self.substituter().apply_sub_to_term(&result, t);
            let discoverer = self.discoverer();
            if discoverer.get_free_sub_vars_in_term(subbed_t).contains(&a) {
                tc_panic!(subbed_t, self.storage, "Unexpected free variable in one of the substitutions being unified (occurs error)");
            }

            result.add_pair(a, subbed_t);
        }
        // result is now the unifier for t0 and t1

        // Now deal with the intersection:
        for &b in dom_s0.intersection(&dom_s1) {
            let substituter = self.substituter();
            let subbed0_b = substituter.apply_sub_to_subject(s0, b);
            let subbed1_b = substituter.apply_sub_to_subject(s1, b);
            let x0 = substituter.apply_sub_to_term(&result, subbed0_b);
            let x1 = substituter.apply_sub_to_term(&result, subbed1_b);

            let discoverer = self.discoverer();
            if discoverer.get_free_sub_vars_in_term(x0).contains(&b)
                || discoverer.get_free_sub_vars_in_term(x1).contains(&b)
            {
                tc_panic_on_many!([x0, x1], self, "Unexpected free variable in intersection of substitutions being unified (occurs error)");
            }

            let v = self.unify_terms(x0, x1)?;
            result.extend(&v);
        }

        Ok(result)
    }

    /// Unify the given parameters with the given arguments. This function
    /// will first perform a pairing operation between the arguments and the
    /// provided parameters in order to ensure that they can be unified.
    ///
    /// Unification is actually performed by
    /// [this](Unifier::unify_param_arg_pairs) function.
    pub(crate) fn unify_params_with_args(
        &self,
        params_id: ParamsId,
        args_id: ArgsId,
        params_subject: TermId,
        args_subject: TermId,
    ) -> TcResult<Sub> {
        let params = self.params_store().get_owned_param_list(params_id);
        let args = self.args_store().get_owned_param_list(args_id);

        let pairs = pair_args_with_params(
            &params,
            &args,
            params_id,
            args_id,
            |param| self.typer().infer_arg_from_param(param),
            params_subject,
            args_subject,
        )?;

        self.unify_param_arg_pairs(pairs)
    }

    /// Unify paired arguments and parameters.
    ///
    /// This is done by first getting the type of each argument, and unifying
    /// with the type of each parameter. Then, a substitution is created
    /// from each parameter to each argument value.
    pub(crate) fn unify_param_arg_pairs(
        &self,
        pairs: impl IntoIterator<Item = (impl Borrow<Param>, impl Borrow<Arg>)>,
    ) -> TcResult<Sub> {
        let mut sub = Sub::empty();

        for (param, arg) in pairs.into_iter() {
            // Ensure their types unify:
            let ty_of_arg = self.typer().infer_ty_of_term(arg.borrow().value)?;
            let ty_sub = self.unify_terms(ty_of_arg, param.borrow().ty)?;

            // Add the ty sub to the sub
            sub = self.get_super_sub(&sub, &ty_sub)?;
        }
        Ok(sub)
    }

    /// Unify the two given argument lists, by argument-wise unifying terms.
    /// The function requires a reference to the parent source and target
    /// terms in order to give meaningful error messages.
    pub(crate) fn unify_args(
        &self,
        src_args_id: ArgsId,
        target_args_id: ArgsId,
        src_id: TermId,
        target_id: TermId,
    ) -> TcResult<Sub> {
        let src_args = self.args_store().get_owned_param_list(src_args_id);
        let target_args = self.args_store().get_owned_param_list(target_args_id);

        let cannot_unify = |reason: ParamUnificationErrorReason| {
            Err(TcError::CannotUnifyArgs {
                src_args_id,
                target_args_id,
                reason,
                src: src_id,
                target: target_id,
            })
        };

        // Ensure the argument lengths match
        if src_args.positional().len() != target_args.positional().len() {
            return cannot_unify(ParamUnificationErrorReason::LengthMismatch);
        }

        let mut cumulative_sub = Sub::empty();

        for (index, target_arg) in target_args.positional().iter().enumerate() {
            let src_arg = if let Some(name) = target_arg.name {
                // The name should be present within the `source_params`. Otherwise
                // we'll raise a name-mismatch?
                match src_args.get_by_name(name) {
                    Some((_, src_param)) => src_param,
                    None => src_args.positional().get(index).unwrap(),
                }
            } else {
                src_args.positional().get(index).unwrap()
            };

            let ty_sub = self.unify_terms(src_arg.value, target_arg.value)?;

            // Add to cumulative substitution
            cumulative_sub.extend(&ty_sub);
        }

        // Return the cumulative substitution of all the arguments:
        Ok(cumulative_sub)
    }

    /// Unify the two given parameter lists, by parameter-wise unifying terms.
    /// The function requires a reference to the parent source and target
    /// terms in order to give meaningful error messages.
    pub(crate) fn unify_params(
        &self,
        src_params_id: ParamsId,
        target_params_id: ParamsId,
        src: impl Into<LocationTarget>,
        target: impl Into<LocationTarget>,
    ) -> TcResult<Sub> {
        let src_params = self.params_store().get_owned_param_list(src_params_id);
        let target_params = self.params_store().get_owned_param_list(target_params_id);

        let cannot_unify = |reason: ParamUnificationErrorReason| {
            Err(TcError::CannotUnifyParams {
                src_params_id,
                target_params_id,
                reason,
                src: src.into(),
                target: target.into(),
            })
        };

        // Ensure the parameter lengths match
        if src_params.positional().len() != target_params.positional().len() {
            return cannot_unify(ParamUnificationErrorReason::LengthMismatch);
        }

        let mut cumulative_sub = Sub::empty();

        // @@Todo: handle default values.
        for (index, target_param) in target_params.positional().iter().enumerate() {
            let src_param = if let Some(name) = target_param.name {
                // The name should be present within the `source_params`. Otherwise
                // we'll raise a name-mismatch?
                match src_params.get_by_name(name) {
                    Some((_, src_param)) => src_param,
                    None => src_params.positional().get(index).unwrap(),
                }
            } else {
                src_params.positional().get(index).unwrap()
            };

            let ty_sub = self.unify_terms(src_param.ty, target_param.ty)?;

            // Add to cumulative substitution
            cumulative_sub.extend(&ty_sub);
        }

        Ok(cumulative_sub)
    }

    /// Bi-directional-unification
    pub(crate) fn unify_terms_bi(&mut self, lhs: TermId, rhs: TermId) -> TcResult<Sub> {
        let mut lhs_subs = self.unify_terms(lhs, rhs)?;
        let rhs_subs = self.unify_terms(rhs, lhs)?;

        lhs_subs.extend(&rhs_subs);
        Ok(lhs_subs)
    }

    /// Terms are equal if they unify both ways without any substitutions.
    pub(crate) fn terms_are_equal(&self, a: TermId, b: TermId) -> bool {
        self.unify_terms(a, b).contains(&Sub::empty())
            && self.unify_terms(b, a).contains(&Sub::empty())
    }

    /// The two given set bound scopes are equivalent if they have the same
    /// distinct members.
    ///
    /// This panics if either scope is not [ScopeKind::SetBound], or if a type
    /// error occurs.
    pub(crate) fn set_bound_scopes_are_equivalent(
        &self,
        a: ScopeId,
        b: ScopeId,
        a_originating_term: TermId,
        b_originating_term: TermId,
    ) -> bool {
        // Short-circuit: same scope IDs:
        if a == b {
            return true;
        }

        let reader = self.reader();
        let scope_a = reader.get_scope_copy(a);
        let scope_b = reader.get_scope_copy(b);

        // Ensure kinds are both [Scope::SetBound]
        if scope_a.kind != ScopeKind::SetBound || scope_b.kind != ScopeKind::SetBound {
            tc_panic_on_many!(
                [a_originating_term, b_originating_term],
                self,
                "set_bound_scopes_are_equal called with non-set-bound scopes"
            );
        }

        // Ensure names are the same:
        let a_names: HashSet<_> = HashSet::from_iter(scope_a.iter_names());
        let b_names: HashSet<_> = HashSet::from_iter(scope_b.iter_names());
        if a_names != b_names {
            return false;
        }

        // Ensure same members
        for name in a_names {
            let (a_member, _) = scope_a.get(name).unwrap();
            let (b_member, _) = scope_b.get(name).unwrap();
            match (a_member.value(), b_member.value()) {
                (Some(a_value), Some(b_value)) => {
                    if !self.terms_are_equal(a_member.ty(), b_member.ty())
                        || !self.terms_are_equal(a_value, b_value)
                    {
                        return false;
                    }
                }
                (None, None) => {
                    if !self.terms_are_equal(a_member.ty(), b_member.ty()) {
                        return false;
                    }
                }
                _ => return false,
            }
        }

        true
    }

    /// Unify the two given terms, producing a substitution.
    ///
    /// The relation between src and target is that src must be a subtype (or
    /// eq) of target.
    ///
    /// Note: Assumes that both terms have been validated.
    pub(crate) fn unify_terms(&self, src_id: TermId, target_id: TermId) -> TcResult<Sub> {
        // Shortcut: terms have the same ID:
        if src_id == target_id {
            return Ok(Sub::empty());
        }

        if let Some(sub) = self.cacher().has_been_unified((src_id, target_id)) {
            return Ok(sub);
        }

        // First we want to simplify the terms:
        let simplified_src_id = self.simplifier().potentially_simplify_term(src_id)?;
        let simplified_target_id = self.simplifier().potentially_simplify_term(target_id)?;
        let simplified_src = self.reader().get_term(simplified_src_id);
        let simplified_target = self.reader().get_term(simplified_target_id);

        // Helper to return a unification error
        let cannot_unify = || Err(TcError::CannotUnify { src: src_id, target: target_id });

        let sub = match (simplified_src, simplified_target) {
            // Unresolved
            (Term::Unresolved(unresolved_src), _) => {
                // Substitute target for source
                Ok(Sub::from_pairs([(unresolved_src, simplified_target_id)]))
            }
            (_, Term::Unresolved(unresolved_target)) => {
                // Substitute source for target
                Ok(Sub::from_pairs([(unresolved_target, simplified_src_id)]))
            }

            // Typeof unifies if the inner terms unify.
            (Term::TyOf(src_inner), Term::TyOf(dest_inner)) => {
                self.unify_terms(src_inner, dest_inner)
            }
            (Term::TyOf(src_inner), _) => {
                if let Some(src_scope_var) = self.oracle().term_as_scope_var(src_inner) {
                    // If it is a scope var, try to just forward to its type
                    self.unify_terms(
                        self.scope_manager().get_scope_var_member(src_scope_var).member.ty(),
                        simplified_target_id,
                    )
                } else {
                    match self.term_store().get(src_inner) {
                        // When the `src_inner` is an unresolved term, the unification between the
                        // target will yield a substitution `unresolved` ->
                        // `Rt(inner)`, so we need to verify that the inner
                        // term is runtime instantiable...
                        Term::Unresolved(inner)
                            if self
                                .validator()
                                .term_is_runtime_instantiable(simplified_target_id)? =>
                        {
                            let instantiated_target =
                                self.builder().create_rt_term(simplified_target_id);

                            Ok(Sub::from_pairs([(inner, instantiated_target)]))
                        }
                        // If the inner is not runtime instantiable, it succeeds but with no
                        // substitution.
                        Term::Unresolved(_) => Ok(Sub::empty()),

                        // If it is a double TyOf (no more), then it should be equivalent to Sized
                        //
                        // @@Inconsistent,@@Todo: this is not always valid, but it would be
                        // fixed by having more information in case of
                        // unresolved variables.
                        Term::TyOf(inner) if self.oracle().term_as_ty_of(inner).is_none() => self
                            .unify_terms(
                                self.builder().create_sized_ty_term(),
                                simplified_target_id,
                            ),
                        _ => cannot_unify(),
                    }
                }
            }
            (_, Term::TyOf(target_inner)) => match self.term_store().get(target_inner) {
                // When the `target_inner` is an unresolved term, the unification between the target
                // will yield a substitution `unresolved` -> `Rt(inner)`, so we need to verify
                // that the inner term is runtime instantiable...
                Term::Unresolved(inner)
                    if self.validator().term_is_runtime_instantiable(simplified_src_id)? =>
                {
                    let instantiated_source = self.builder().create_rt_term(simplified_src_id);

                    Ok(Sub::from_pairs([(inner, instantiated_source)]))
                }
                // If the inner is not runtime instantiable, it succeeds but with no substitution.
                Term::Unresolved(_) => Ok(Sub::empty()),
                _ => cannot_unify(),
            },

            // Merging:
            (_, Term::Merge(inner_target)) => {
                // Try to merge source with each individual term in target. If all succeed,
                // then the whole thing should succeed.
                let mut subs = Sub::empty();
                for idx in inner_target.to_index_range() {
                    let inner_target_id = self.term_list_store().get_at_index(inner_target, idx);

                    match self.unify_terms(simplified_src_id, inner_target_id) {
                        Ok(result) => {
                            subs.extend(&result);
                            continue;
                        }
                        Err(e) => return Err(e),
                    }
                }
                Ok(subs)
            }
            (Term::Merge(inner_src), _) => {
                // Try to merge each individual term in source, with target. If any one
                // succeeds, then the whole thing should succeed.
                let mut first_error = None;
                for idx in inner_src.to_index_range() {
                    let inner_src_id = self.term_list_store().get_at_index(inner_src, idx);

                    match self.unify_terms(inner_src_id, simplified_target_id) {
                        Ok(result) => return Ok(result),
                        Err(e) => first_error = first_error.or(Some(e)),
                    }
                }

                match first_error {
                    Some(first_error) => Err(first_error),
                    None => cannot_unify(),
                }
            }

            // Union:
            (_, Term::Union(inner_target)) => {
                // Try to merge each individual term in source, with target. If any one
                // succeeds, then the whole thing should succeed.
                let mut first_error = None;
                for idx in inner_target.to_index_range() {
                    let inner_target_id = self.term_list_store().get_at_index(inner_target, idx);

                    match self.unify_terms(simplified_src_id, inner_target_id) {
                        Ok(result) => return Ok(result),
                        Err(e) => first_error = first_error.or(Some(e)),
                    }
                }
                match first_error {
                    Some(first_error) => Err(first_error),
                    None => cannot_unify(),
                }
            }
            (Term::Union(inner_src), _) => {
                // Try to merge source with each individual term in target. If all succeed,
                // then the whole thing should succeed.
                let mut subs = Sub::empty();
                for idx in inner_src.to_index_range() {
                    let inner_src_id = self.term_list_store().get_at_index(inner_src, idx);

                    match self.unify_terms(inner_src_id, simplified_target_id) {
                        Ok(result) => {
                            subs = self.unify_subs(&subs, &result)?;
                            continue;
                        }
                        Err(e) => return Err(e),
                    }
                }
                Ok(subs)
            }

            // Access:
            (Term::Access(src_access), Term::Access(target_access))
                if src_access.name == target_access.name =>
            {
                // Unify the subjects
                self.unify_terms(src_access.subject, target_access.subject)
            }
            (Term::Access(_), _) | (_, Term::Access(_)) => {
                // Since these cannot be simplified further, we don't know if they can be
                // unified:
                cannot_unify()
            }

            // Variables:
            (Term::Var(src_var), Term::Var(target_var)) if src_var.name == target_var.name => {
                // Same variables unify
                Ok(Sub::empty())
            }
            (Term::Var(_), _) | (_, Term::Var(_)) => {
                // Different variables do not unify (since they cannot be simplified)
                cannot_unify()
            }
            (Term::BoundVar(src_var), Term::BoundVar(target_var))
                if src_var.name == target_var.name =>
            {
                // Same bound variables unify
                Ok(Sub::empty())
            }
            (Term::BoundVar(_), _) | (_, Term::BoundVar(_)) => {
                // Different bound variables do not unify (since they cannot be simplified)
                cannot_unify()
            }
            (Term::ScopeVar(src_var), Term::ScopeVar(target_var))
                if (src_var.scope, src_var.index) == (target_var.scope, target_var.index) =>
            {
                // Same scope variables unify (i.e. same member, not necessarily same name)
                Ok(Sub::empty())
            }
            (Term::ScopeVar(_), _) | (_, Term::ScopeVar(_)) => {
                // Different scope variables do not unify
                cannot_unify()
            }

            // Apply substitution:
            (Term::SetBound(src_set_bound), Term::SetBound(target_set_bound))
                if self.set_bound_scopes_are_equivalent(
                    src_set_bound.scope,
                    target_set_bound.scope,
                    src_id,
                    target_id,
                ) =>
            {
                // Unify inner, then unify the resultant substitution with the ones given
                //  here:
                //
                // Notice: this should never produce a substitution since we start with
                // simplified terms.
                let sub = self.scope_manager().enter_scope(src_set_bound.scope, |this| {
                    this.unifier().unify_terms(src_set_bound.term, target_set_bound.term)
                })?;
                if sub != Sub::empty() {
                    tc_panic_on_many!(
                        [src_set_bound.term, target_set_bound.term],
                        self,
                        "got non-empty substitution when unifying terms inside SetBound"
                    );
                }
                Ok(sub)
            }
            (Term::SetBound(_), _) | (_, Term::SetBound(_)) => {
                // Otherwise they don't unify (since we start with simplified terms)
                cannot_unify()
            }

            // Type functions:
            (Term::TyFn(_), _) | (_, Term::TyFn(_)) => {
                // For now, type functions never unify, because unifying them would require a
                // lot of work to match each of the cases.
                //  @@Enhancement: in principle this is possible, though unclear if useful.
                cannot_unify()
            }

            // Type function application:
            (Term::TyFnCall(src_app_ty_fn), Term::TyFnCall(target_app_ty_fn)) => {
                // This case would be hit if the subject is a variable, for example.

                // Unify the subjects to ensure they are compatible:
                let subject_sub =
                    self.unify_terms(src_app_ty_fn.subject, target_app_ty_fn.subject)?;

                // Get the type of the subject and ensure it is a type function type:
                let subject = self
                    .substituter()
                    // Here we use the target's subject but it shouldn't matter.
                    .apply_sub_to_term(&subject_sub, target_app_ty_fn.subject);

                let subject_ty_id = self.typer().infer_ty_of_term(subject)?;
                let reader = self.reader();
                let subject_ty = reader.get_term(subject_ty_id);
                match subject_ty {
                    Term::TyFnTy(_) => {
                        // Match the two args:
                        let sub = self.unify_args(
                            src_app_ty_fn.args,
                            target_app_ty_fn.args,
                            src_id,
                            target_id,
                        )?;

                        Ok(sub)
                    }
                    // If the subject is not a function type then application is invalid:
                    _ => Err(TcError::UnsupportedTyFnApplication { subject_id: subject }),
                }
            }
            (Term::TyFnCall(_), _) | (_, Term::TyFnCall(_)) => {
                // Any other type function application (asymmetric) doesn't unify
                cannot_unify()
            }

            // Type function type:
            (Term::TyFnTy(src_ty_fn_ty), Term::TyFnTy(target_ty_fn_ty)) => {
                // Unify params and return:

                // Params need to be unified inversely.
                // @@Correctness: figure out exact variance rules.
                let params_sub = self.unify_params(
                    target_ty_fn_ty.params,
                    src_ty_fn_ty.params,
                    src_id,
                    target_id,
                )?;

                let return_sub =
                    self.unify_terms(src_ty_fn_ty.return_ty, target_ty_fn_ty.return_ty)?;

                // Merge the subs
                self.unify_subs(&params_sub, &return_sub)
            }
            (Term::TyFnTy(_), _) | (_, Term::TyFnTy(_)) => cannot_unify(),

            // Level 3 terms:
            (Term::Level3(src_level3_term), Term::Level3(target_level3_term)) => {
                match (src_level3_term, target_level3_term) {
                    // "TraitKind" always unifies:
                    (Level3Term::TrtKind, Level3Term::TrtKind) => Ok(Sub::empty()),
                }
            }
            (Term::Level3(_), _) | (_, Term::Level3(_)) => {
                // Mismatching level:
                cannot_unify()
            }

            // Level 2 terms:
            (Term::Level2(src_level2_term), Term::Level2(target_level2_term)) => {
                match (src_level2_term, target_level2_term) {
                    // Traits only unify if the IDs are the same:
                    (Level2Term::Trt(src_id), Level2Term::Trt(target_id)) => {
                        if src_id == target_id {
                            Ok(Sub::empty())
                        } else {
                            cannot_unify()
                        }
                    }
                    (Level2Term::Trt(_), Level2Term::AnyTy)
                    | (Level2Term::AnyTy, Level2Term::AnyTy)
                    | (Level2Term::SizedTy, Level2Term::SizedTy)
                    | (Level2Term::SizedTy, Level2Term::AnyTy) => Ok(Sub::empty()),
                    (Level2Term::AnyTy, Level2Term::Trt(_))
                    | (Level2Term::AnyTy, Level2Term::SizedTy)
                    | (Level2Term::Trt(_), Level2Term::SizedTy)
                    | (Level2Term::SizedTy, Level2Term::Trt(_)) => cannot_unify(),
                }
            }
            (Term::Level2(_), _) | (_, Term::Level2(_)) => {
                // Mismatching level:
                cannot_unify()
            }

            // Level 1 terms:
            (Term::Level1(src_level1_term), Term::Level1(target_level1_term)) => {
                match (src_level1_term, target_level1_term) {
                    // Mod defs only unify if their IDs are the same
                    (Level1Term::ModDef(src_id), Level1Term::ModDef(target_id)) => {
                        if src_id == target_id {
                            Ok(Sub::empty())
                        } else {
                            cannot_unify()
                        }
                    }
                    // Nominal defs only unify if their IDs are the same
                    (Level1Term::NominalDef(src_id), Level1Term::NominalDef(target_id)) => {
                        if src_id == target_id {
                            Ok(Sub::empty())
                        } else {
                            cannot_unify()
                        }
                    }
                    // Tuples unify if all their members unify:
                    (Level1Term::Tuple(src_tuple), Level1Term::Tuple(target_tuple)) => self
                        .unify_params(src_tuple.members, target_tuple.members, src_id, target_id),
                    // Functions unify if their parameters and return unify:
                    (Level1Term::Fn(src_fn_ty), Level1Term::Fn(target_fn_ty)) => {
                        // Once again, params need to be unified inversely.
                        let params_sub = self.unify_params(
                            target_fn_ty.params,
                            src_fn_ty.params,
                            target_id,
                            src_id,
                        )?;

                        let return_sub =
                            self.unify_terms(src_fn_ty.return_ty, target_fn_ty.return_ty)?;

                        // Merge the subs
                        Ok(self.get_super_sub(&params_sub, &return_sub)?)
                    }
                    // Mismatching level 1 term variants do not unify:
                    _ => cannot_unify(),
                }
            }
            (Term::Level1(_), _) | (_, Term::Level1(_)) => {
                // Mismatching level:
                cannot_unify()
            }

            // Level 0 terms:
            (Term::Level0(src_level0_term), Term::Level0(target_level0_term)) => {
                match (src_level0_term, target_level0_term) {
                    (
                        Level0Term::EnumVariant(src_enum_variant),
                        Level0Term::EnumVariant(target_enum_variant),
                    ) => {
                        if src_enum_variant.enum_def_id == target_enum_variant.enum_def_id
                            && src_enum_variant.variant_name == target_enum_variant.variant_name
                        {
                            // They are the same variant from the same enum:
                            Ok(Sub::empty())
                        } else {
                            cannot_unify()
                        }
                    }
                    (Level0Term::Lit(src_lit), Level0Term::Lit(target_lit)) => {
                        if src_lit == target_lit {
                            // They are the same literal:
                            Ok(Sub::empty())
                        } else {
                            cannot_unify()
                        }
                    }
                    (
                        Level0Term::Constructed(src_constructed_term),
                        Level0Term::Constructed(target_constructed_term),
                    ) => {
                        // Unify the subject of the constructed terms
                        self.unify_terms(
                            src_constructed_term.subject,
                            target_constructed_term.subject,
                        )?;

                        // Unify the arguments of the constructed terms
                        self.unify_args(
                            src_constructed_term.members,
                            target_constructed_term.members,
                            src_id,
                            target_id,
                        )
                    }
                    (Level0Term::Tuple(src_tuple_lit), Level0Term::Tuple(target_tuple_lit)) => {
                        // Unify each argument:
                        self.unifier().unify_args(
                            src_tuple_lit.members,
                            target_tuple_lit.members,
                            src_id,
                            target_id,
                        )
                    }
                    (
                        Level0Term::Lit(_)
                        | Level0Term::Tuple(_)
                        | Level0Term::Constructed(_)
                        | Level0Term::EnumVariant(_),
                        _,
                    ) => {
                        // Try to get the type of the src literal, and the type of the target, and
                        // unify:
                        let src_lit_ty =
                            self.typer().infer_ty_of_simplified_term(simplified_src_id)?;
                        let target_non_lit_ty =
                            self.typer().infer_ty_of_simplified_term(simplified_target_id)?;
                        self.unify_terms(src_lit_ty, target_non_lit_ty)
                    }
                    // Any other level-0 term does not unify:
                    _ => cannot_unify(),
                }
            }

            // Root unifies with root and nothing else:
            (Term::Root, Term::Root) => Ok(Sub::empty()),
            (_, Term::Root) | (Term::Root, _) => cannot_unify(),
        }?;

        self.cacher().add_unification_entry((src_id, target_id), &sub);

        Ok(sub)
    }

    /// Function used to verify a sequence of terms. This ensures that
    /// the types of all the terms can be unified.
    ///
    /// Returns the *type* of the sequence.
    pub(crate) fn unify_rt_term_sequence(
        &self,
        sequence: impl IntoIterator<Item = TermId>,
    ) -> TcResult<TermId> {
        let mut elements = sequence.into_iter().peekable();

        // Create a shared term that is used to verify all elements within the
        // list can be unified with one another, and then iterate over all of the
        // elements.
        let mut shared_term = self.builder().create_unresolved_term();

        while let Some(element) = elements.next() {
            let element_ty = self.typer().infer_ty_of_term(element)?;
            let sub = self.unifier().unify_terms(element_ty, shared_term)?;

            // apply the substitution on the `shared_term`
            shared_term = self.substituter().apply_sub_to_term(&sub, shared_term);

            // Only add the position to the last term...
            if elements.peek().is_none() {
                self.location_store().copy_location(element_ty, shared_term);
            }
        }

        Ok(shared_term)
    }

    /// Function used to verify a sequence of pattern terms with associated
    /// [PatId]s. The term is expected to be already the type and thus a
    /// multi-term unification is applied.
    ///
    /// @@ErrorReporting: The function does not currently produce good location
    /// messages because the terms are being clobbered, ideally the
    /// associated `PatId` should be used here.
    pub(crate) fn unify_pat_terms(
        &self,
        sequence: impl IntoIterator<Item = (TermId, PatId)>,
    ) -> TcResult<TermId> {
        let mut elements = sequence.into_iter().peekable();

        // Create a shared term that is used to verify all elements within the
        // list can be unified with one another, and then iterate over all of the
        // elements.
        let mut shared_term = self.builder().create_unresolved_term();

        // @@TODO: rather than using `Term` as the location, we should use the `Pat` as
        // the location, but this requires some additional infrastructure within
        // diagnostics in order to support patterns as being arguments to
        // `CannotUnify`
        while let Some((element_ty, _)) = elements.next() {
            let sub = self.unifier().unify_terms(element_ty, shared_term)?;

            // apply the substitution on the `shared_term`
            shared_term = self.substituter().apply_sub_to_term(&sub, shared_term);

            // Only add the position to the last term...
            if elements.peek().is_none() {
                self.location_store().copy_location(element_ty, shared_term);
            }
        }

        Ok(shared_term)
    }
}
