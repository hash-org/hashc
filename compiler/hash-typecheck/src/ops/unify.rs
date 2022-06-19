//! Utilities related to type unification and substitution.
use super::{AccessToOps, AccessToOpsMut};
use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{
            Args, Level0Term, Level1Term, Level2Term, Level3Term, Params, Sub, Term, TermId,
        },
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};
use std::collections::HashSet;

/// Options that are received by the unifier when unifying types.
pub struct UnifyTysOpts {}

/// Performs type unification and other related operations.
pub struct Unifier<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Unifier<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Unifier<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd> Unifier<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Unify two substitutions to produce another substitution.
    ///
    /// The resultant substitution contains all the information of the two source substitutions,
    /// without any common free variables in their domains.
    ///
    /// This implements the algorithm outlined in the paper:
    /// <https://www.researchgate.net/publication/221600544_On_the_Unification_of_Substitutions_in_Type_Interfaces>
    ///
    pub fn unify_subs(&mut self, s0: &Sub, s1: &Sub) -> TcResult<Sub> {
        let dom_s0: HashSet<_> = s0.domain().collect();
        let dom_s1: HashSet<_> = s1.domain().collect();
        let mut substituter = self.substituter();

        // First split the domains into three parts: d0, d1 (not directly needed), and the
        // intersection (see second loop)
        let d0: HashSet<_> = dom_s0.difference(&dom_s1).copied().collect();
        let t0 = Sub::from_pairs(
            d0.iter()
                .map(|&a| (a, substituter.apply_sub_to_subject(s0, a))),
        );

        // Start with t0 and add terms for d1 one at a time, always producing well formed
        // substitutions
        let mut result = t0.clone();
        for (a, t) in t0.pairs() {
            // Remove elements of dom(result) from t, and remove a from result.
            let subbed_t = substituter.apply_sub_to_term(&result, t);
            if substituter.get_free_vars_in_term(subbed_t).contains(&a) {
                // @@ErrorReporting: here we can error with the span for more info.
                panic!("Unexpected free variable in one of the substitutions being unified (occurs error)");
            }

            result.add_pair(a, subbed_t);
        }
        // result is now the unifier for t0 and t1

        // Now deal with the intersection:
        for &b in dom_s0.intersection(&dom_s1) {
            let mut substituter = self.substituter();
            let subbed0_b = substituter.apply_sub_to_subject(s0, b);
            let subbed1_b = substituter.apply_sub_to_subject(s1, b);
            let x0 = substituter.apply_sub_to_term(&result, subbed0_b);
            let x1 = substituter.apply_sub_to_term(&result, subbed1_b);

            if substituter.get_free_vars_in_term(x0).contains(&b)
                || substituter.get_free_vars_in_term(x1).contains(&b)
            {
                panic!("Unexpected free variable in intersection of substitutions being unified (occurs error)");
            }

            let v = self.unify_terms(x0, x1)?;
            result.extend(&v);
        }

        Ok(result)
    }

    /// Unify the given parameters with the given arguments.
    ///
    /// This is done by first getting the type of each argument, and unifying with the type of each
    /// parameter. Then, a substitution is created from each parameter to each argument value.
    pub fn unify_params_with_args(&mut self, _params: &Params, _args: &Args) -> TcResult<Sub> {
        todo!()
    }

    /// Unify the two given argument lists, by argument-wise unifying terms.
    pub fn unify_args(&mut self, _src_args: &Args, _target_args: &Args) -> TcResult<Sub> {
        todo!()
    }

    /// Unify the two given parameter lists, by parameter-wise unifying terms.
    pub fn unify_params(&mut self, _src_params: &Params, _target_params: &Params) -> TcResult<Sub> {
        todo!()
    }

    /// Unify the two given terms, producing a substitution.
    ///
    /// The relation between src and target is that src must be a subtype (or eq) of target.
    pub fn unify_terms(&mut self, src_id: TermId, target_id: TermId) -> TcResult<Sub> {
        // Shortcut: terms have the same ID:
        if src_id == target_id {
            return Ok(Sub::empty());
        }

        // First we want to simplify the terms:
        let simplified_src_id = self.simplifier().potentially_simplify_term(src_id)?;
        let simplified_target_id = self.simplifier().potentially_simplify_term(target_id)?;
        let simplified_src = self.reader().get_term(simplified_src_id).clone();
        let simplified_target = self.reader().get_term(simplified_target_id).clone();

        // Helper to return a unification error
        let cannot_unify = || {
            Err(TcError::CannotUnify {
                src: src_id,
                target: target_id,
            })
        };

        match (simplified_src, simplified_target) {
            // Unresolved
            (Term::Unresolved(unresolved_src), _) => {
                // Substitute target for source
                Ok(Sub::from_pairs([(unresolved_src, simplified_target_id)]))
            }
            (_, Term::Unresolved(unresolved_target)) => {
                // Substitute source for target
                Ok(Sub::from_pairs([(unresolved_target, simplified_src_id)]))
            }

            // Merging:
            (Term::Merge(_), Term::Merge(inner_target)) => {
                // Try to merge source with each individual term in target. If all succeed,
                // then the whole thing should succeed.
                let mut subs = Sub::empty();
                for inner_target_id in inner_target {
                    match self.unify_terms(src_id, inner_target_id) {
                        Ok(result) => {
                            subs = self.unify_subs(&subs, &result)?;
                            continue;
                        }
                        Err(e) => return Err(e),
                    }
                }
                Ok(subs)
            }
            (_, Term::Merge(inner_target)) => {
                // This is only valid if the merge has one element and unifies with source
                match inner_target.as_slice() {
                    [inner_target_id] => self.unify_terms(src_id, *inner_target_id),
                    _ => cannot_unify(),
                }
            }
            (Term::Merge(inner_src), _) => {
                // Try to merge each individual term in source, with target. If any one succeeds,
                // then the whole thing should succeed.
                let mut first_error = None;
                for inner_src_id in inner_src {
                    match self.unify_terms(inner_src_id, target_id) {
                        Ok(result) => {
                            return Ok(result);
                        }
                        Err(e) if first_error.is_none() => {
                            first_error = Some(e);
                            continue;
                        }
                        _ => continue,
                    }
                }
                match first_error {
                    Some(first_error) => Err(first_error),
                    None => cannot_unify(),
                }
            }

            // Access:
            (Term::Access(src_access), Term::Access(target_access))
                if src_access.name == target_access.name =>
            {
                // Unify the subjects
                self.unify_terms(src_access.subject, target_access.subject)
            }
            (Term::Access(_), _) | (_, Term::Access(_)) => {
                // Since these cannot be simplified further, we don't know if they can be unified:
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

            // Apply substitution:
            (Term::AppSub(src_app_sub), Term::AppSub(target_app_sub))
                if self
                    .validator()
                    .subs_are_equivalent(&src_app_sub.sub, &target_app_sub.sub)? =>
            {
                // Unify inner, then unify the resultant substitution with the ones given here:
                let inner_sub = self.unify_terms(src_app_sub.term, target_app_sub.term)?;
                self.unify_subs(&src_app_sub.sub, &inner_sub)
            }
            (Term::AppSub(_), _) | (_, Term::AppSub(_)) => {
                // Otherwise they don't unify (since we start with simplified terms)
                cannot_unify()
            }

            // Type functions:
            (Term::TyFn(_), _) | (_, Term::TyFn(_)) => {
                // For now, type functions never unify, because unifying them would require a lot
                // of work to match each of the cases.
                //  @@Enhancement: in principle this is possible, though unclear if useful.
                cannot_unify()
            }

            // Type function application:
            (Term::AppTyFn(src_app_ty_fn), Term::AppTyFn(target_app_ty_fn)) => {
                // Unify the subject, and unify the arguments:
                // This case would be hit if the subject is a variable, for example.
                let subject_sub =
                    self.unify_terms(src_app_ty_fn.subject, target_app_ty_fn.subject)?;

                // Here we have to unify both ways, because of potential invariance:
                // @@Future: find a way to specify variance on type function arguments.
                let args_sub1 = self.unify_args(&src_app_ty_fn.args, &target_app_ty_fn.args)?;
                let args_sub2 = self.unify_args(&target_app_ty_fn.args, &src_app_ty_fn.args)?;

                // Unify all the created substitutions
                let args_unified_sub = self.unify_subs(&args_sub1, &args_sub2)?;
                self.unify_subs(&args_unified_sub, &subject_sub)
            }
            (Term::AppTyFn(_), _) | (_, Term::AppTyFn(_)) => {
                // Any other type function application (asymmetric) doesn't unify
                cannot_unify()
            }

            // Type function type:
            (Term::TyFnTy(src_ty_fn_ty), Term::TyFnTy(target_ty_fn_ty)) => {
                // Unify params and return:

                // Params need to be unified inversely.
                // @@Todo: figure out exact variance rules.
                let params_sub =
                    self.unify_params(&target_ty_fn_ty.params, &src_ty_fn_ty.params)?;
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
                    // If a trait tries to be unified with "Type", it is always successful:
                    (Level2Term::Trt(_), Level2Term::AnyTy) => Ok(Sub::empty()),
                    // The other way around doesn't hold however:
                    (Level2Term::AnyTy, Level2Term::Trt(_)) => cannot_unify(),
                    // "Type" unifies with "Type":
                    (Level2Term::AnyTy, Level2Term::AnyTy) => Ok(Sub::empty()),
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
                    (Level1Term::Tuple(src_tuple), Level1Term::Tuple(target_tuple)) => {
                        self.unify_params(&src_tuple.members, &target_tuple.members)
                    }
                    // Tuples unify if their parameters and return unify:
                    (Level1Term::Fn(src_fn_ty), Level1Term::Fn(target_fn_ty)) => {
                        // Once again, params need to be unified inversely.
                        let params_sub =
                            self.unify_params(&target_fn_ty.params, &src_fn_ty.params)?;
                        let return_sub =
                            self.unify_terms(src_fn_ty.return_ty, target_fn_ty.return_ty)?;

                        // Merge the subs
                        self.unify_subs(&params_sub, &return_sub)
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
                    // Any other level-0 term does not unify:
                    _ => cannot_unify(),
                }
            }
        }
    }
}
