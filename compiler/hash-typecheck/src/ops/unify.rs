//! Utilities related to type unification and substitution.
//!
//! @@Incomplete(kontheocharis): this module is currently under construction.

// @@Remove
#![allow(unused)]

use super::{building::PrimitiveBuilder, substitute::Substituter};
use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{AppTyFn, Arg, Args, Param, Params, Sub, Term, TermId, UnresolvedTerm, Var},
        scope::ScopeStack,
        AccessToStorage, AccessToStorageMut, GlobalStorage, StorageRefMut,
    },
};
use std::{
    borrow::Cow,
    cell::RefCell,
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut},
};

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

    /// Pair the given parameters with the given arguments.
    ///
    /// This does not perform any typechecking, it simply matches parameters and arguments by
    /// position or name.
    fn pair_args_with_params<'p, 'a>(
        &self,
        params: &'p Params,
        args: &'a Args,
    ) -> TcResult<Vec<(&'p Param, &'a Arg)>> {
        let mut result = vec![];

        // Keep track of used params to ensure no parameter is given twice.
        let mut params_used = HashSet::new();

        // @@Incomplete: handle default args

        // Ensure the length of params and args is the same
        if params.positional().len() != args.positional().len() {
            return Err(TcError::MismatchingArgParamLength(
                args.clone(),
                params.clone(),
            ));
        }

        // Keep track of the first non-positional argument
        let mut done_positional = false;
        for (i, arg) in args.positional().iter().enumerate() {
            match arg.name {
                Some(arg_name) => {
                    // Named argument
                    done_positional = true;
                    match params.get_by_name(arg_name) {
                        Some((param_i, param)) => {
                            if params_used.contains(&i) {
                                // Ensure not already used
                                return Err(TcError::ParamGivenTwice(
                                    args.clone(),
                                    params.clone(),
                                    param_i,
                                ));
                            } else {
                                params_used.insert(param_i);
                                result.push((param, arg));
                            }
                        }
                        None => return Err(TcError::ParamNotFound(params.clone(), arg_name)),
                    }
                }
                None => {
                    // Positional argument
                    if done_positional {
                        // Using positional args after named args is an error
                        return Err(TcError::CannotUsePositionalArgAfterNamedArg(
                            args.clone(),
                            i,
                        ));
                    } else if params_used.contains(&i) {
                        // Ensure not already used
                        return Err(TcError::ParamGivenTwice(args.clone(), params.clone(), i));
                    } else {
                        params_used.insert(i);
                        result.push((params.positional().get(i).unwrap(), arg));
                    }
                }
            }
        }

        Ok(result)
    }

    fn apply_args_to_params_make_sub(
        &mut self,
        _params: &Params,
        _args: &Args,
        _unify_opts: &UnifyTysOpts,
    ) -> TcResult<Sub> {
        todo!()
        // let pairs = self.pair_args_with_params(params, args)?;
        // let mut subs = Sub::empty();

        // for (param, arg) in pairs {
        //     // Unify each argument's type with the type of the parameter
        //     let arg_ty = self.ty_of_term(arg.value)?;
        //     let sub = self.unify_tys(arg_ty, param.ty, unify_opts)?;
        //     subs.merge_with(&sub);
        // }

        // Ok(subs)
    }

    fn apply_ty_fn(&mut self, apply_ty_fn: &AppTyFn) -> TcResult<Option<TermId>> {
        let subject_id = self
            .simplify_term(apply_ty_fn.subject)?
            .unwrap_or(apply_ty_fn.subject);
        let subject = self.storage.term_store().get(subject_id);
        match subject {
            Term::TyFn(_) => {
                todo!()
            }
            Term::AppTyFn(inner_apply_ty_fn) => {
                let inner_apply_ty_fn = inner_apply_ty_fn.clone();
                // Recurse
                let inner_apply_ty_fn_result_id = self.apply_ty_fn(&inner_apply_ty_fn)?;
                match inner_apply_ty_fn_result_id {
                    Some(inner_apply_ty_fn_result_id) => {
                        match self.storage.term_store().get(inner_apply_ty_fn_result_id) {
                            Term::TyFn(_) => self.apply_ty_fn(&AppTyFn {
                                subject: inner_apply_ty_fn_result_id,
                                args: apply_ty_fn.args.clone(),
                            }),
                            _ => Err(TcError::NotATypeFunction(subject_id)),
                        }
                    }
                    None => Ok(None),
                }
            }
            _ => Err(TcError::NotATypeFunction(subject_id)),
        }
    }

    /// Simplify the given term, just returning the original if no simplification occured.
    pub fn potentially_simplify_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        Ok(self.simplify_term(term_id)?.unwrap_or(term_id))
    }

    /// Simplify the given term.
    pub fn simplify_term(&mut self, value_id: TermId) -> TcResult<Option<TermId>> {
        let value = self.storage.term_store().get(value_id);
        match value {
            Term::AppTyFn(apply_ty_fn) => {
                let apply_ty_fn = apply_ty_fn.clone();
                let result = self.apply_ty_fn(&apply_ty_fn)?;
                match result {
                    Some(result) => Ok(Some(result)),
                    None => Ok(None),
                }
            }
            Term::Merge(inner) => {
                let inner = inner.clone();
                let inner_tys = inner
                    .iter()
                    .map(|&ty| self.simplify_term(ty))
                    .collect::<Result<Vec<_>, _>>()?;
                if inner_tys.iter().any(|x| x.is_some()) {
                    Ok(Some(
                        self.builder().create_merge_term(
                            inner_tys
                                .iter()
                                .zip(inner)
                                .map(|(new, old)| new.unwrap_or(old)),
                        ),
                    ))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    /// Get the type of the given term, as another term.
    pub fn ty_of_term(&mut self, term_id: TermId) -> TcResult<TermId> {
        todo!()
        // let value = self.storage.value_store().get(value_id).clone();
        // Ok(match value {
        //     Term::Trt(_) => self.primitive_builder().create_trt_kind(),
        //     Term::Ty(ty_id) => self.primitive_builder().create_ty_of_ty(),
        //     Term::Rt(rt_ty_id) => rt_ty_id,
        //     Term::TyFn(ty_fn) => self.primitive_builder().create_ty_fn_ty(
        //         ty_fn.general_params.positional().iter().cloned(),
        //         ty_fn.general_return_ty,
        //     ),
        //     // @@Incomplete:
        //     Term::AppTyFn(_) => todo!(),
        //     Term::ModDef(mod_def_id) => self.primitive_builder().create_mod_def_ty(mod_def_id),
        //     Term::NominalDef(nominal_def_id) => {
        //         self.primitive_builder().create_nominal_ty(nominal_def_id)
        //     }
        //     // @@Incomplete: We need scopes for this:
        //     Term::Var(_) => todo!(),
        //     Term::Merge(values) => {
        //         let inner_tys = values
        //             .iter()
        //             .map(|&value| self.ty_of_term(value))
        //             .collect::<Result<Vec<_>, _>>()?;

        //         self.primitive_builder().create_merge_ty(inner_tys)
        //     }
        //     Term::Unset(ty_id) => ty_id,
        //     Term::Access(_) => todo!(),
        //     Term::EnumVariant(_) => todo!(),
        // })
    }

    /// Convenience method to get a substitutor.
    fn substitutor(&mut self) -> Substituter {
        Substituter::new(self.storages_mut())
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
        let mut substitutor = self.substitutor();

        /// First split the domains into three parts: d0, d1, and the intersection (see second
        /// loop)
        let d0: HashSet<_> = dom_s0.difference(&dom_s1).copied().collect();
        let t0 = Sub::from_pairs(
            d0.iter()
                .map(|&a| (a, substitutor.apply_sub_to_subject(s0, a))),
        );

        let d1: HashSet<_> = dom_s1.difference(&dom_s0).copied().collect();
        let t1 = Sub::from_pairs(
            d1.iter()
                .map(|&a| (a, substitutor.apply_sub_to_subject(s1, a))),
        );

        // Start with t0 and add terms for d1 one at a time, always producing well formed
        // substitutions
        let mut result = t0.clone();
        for (a, t) in t0.pairs() {
            // Remove elements of dom(result) from t, and remove a from result.
            let subbed_t = substitutor.apply_sub_to_term(&result, t);
            if substitutor.get_free_vars_in_term(subbed_t).contains(&a) {
                // @@ErrorReporting: here we can error with the span for more info.
                panic!("Unexpected free variable in one of the substitutions being unified (occurs error)");
            }

            result.add_pair(a, subbed_t);
        }
        // result is now the unifier for t0 and t1

        // Now deal with the intersection:
        for &b in dom_s0.intersection(&dom_s1) {
            let mut substitutor = self.substitutor();
            let subbed0_b = substitutor.apply_sub_to_subject(s0, b);
            let subbed1_b = substitutor.apply_sub_to_subject(s1, b);
            let x0 = substitutor.apply_sub_to_term(&result, subbed0_b);
            let x1 = substitutor.apply_sub_to_term(&result, subbed1_b);

            if substitutor.get_free_vars_in_term(x0).contains(&b)
                || substitutor.get_free_vars_in_term(x1).contains(&b)
            {
                panic!("Unexpected free variable in intersection of substitutions being unified (occurs error)");
            }

            let v = self.unify_terms(x0, x1)?;
            result.extend(&v);
        }

        Ok(result)
    }

    pub fn unify_terms(&mut self, src_id: TermId, target_id: TermId) -> TcResult<Sub> {
        todo!()
        // let src = self.storage.ty_store().get(src_id).clone();
        // let target = self.storage.ty_store().get(target_id).clone();
        // let cannot_unify = || -> TcResult<Sub> { Err(TcError::CannotUnify(src_id, target_id)) };

        // // Basically, can src be used where a target is required?
        // match (src, target) {
        //     // First, type functions:
        //     (Ty::AppTyFn(_), Ty::AppTyFn(_)) => {
        //         // Check if same subject and unify, otherwise evaluate and unify
        //         // match self.values_are_equal(src_ty_fn_value, target_ty_fn_value) {
        //         //     ValuesAreEqual::Yes => {
        //         //             // If the values are equal, then if the arguments unify then we have
        //         //             // the same tys
        //         //             self.unify_tys(src_args, target_args, opts)
        //         //         }
        //         //     ValuesAreEqual::No => {}
        //         //     ValuesAreEqual::Unsure => {}
        //         // }
        //         todo!()
        //     }
        //     (_, Ty::AppTyFn(_)) => {
        //         // Try to apply the RHS, if it works then try to unify again, else error:
        //         let simplified_target = self.simplify_ty(target_id)?;
        //         match simplified_target {
        //             Some(simplified_target_id) => {
        //                 self.unify_tys(src_id, simplified_target_id, opts)
        //             }
        //             None => cannot_unify(),
        //         }
        //     }
        //     (Ty::AppTyFn(_), _) => {
        //         // Try to apply the LHS, if it works then try to unify again, else error:
        //         let simplified_src = self.simplify_ty(src_id)?;
        //         match simplified_src {
        //             Some(simplified_src_id) => self.unify_tys(simplified_src_id, target_id, opts),
        //             None => cannot_unify(),
        //         }
        //     }

        //     // Merging:
        //     (Ty::Merge(_), Ty::Merge(inner_target)) => {
        //         // Try to merge source with each individual type in target. If all succeed,
        //         // then the whole thing should succeed.
        //         let mut subs = Sub::empty();
        //         for inner_target_id in inner_target {
        //             match self.unify_tys(src_id, inner_target_id, opts) {
        //                 Ok(result) => {
        //                     subs.merge_with(&result);
        //                     continue;
        //                 }
        //                 Err(e) => return Err(e),
        //             }
        //         }
        //         Ok(subs)
        //     }
        //     (_, Ty::Merge(inner_target)) => {
        //         // This is only valid if the merge has one element and unifies with source
        //         match inner_target.as_slice() {
        //             [inner_target_id] => self.unify_tys(src_id, *inner_target_id, opts),
        //             _ => cannot_unify(),
        //         }
        //     }
        //     (Ty::Merge(inner_src), _) => {
        //         // Try to merge each individual type in source, with target. If any one succeeds,
        //         // then the whole thing should succeed.
        //         let mut first_error = None;
        //         for inner_src_id in inner_src {
        //             match self.unify_tys(inner_src_id, target_id, opts) {
        //                 Ok(result) => {
        //                     return Ok(result);
        //                 }
        //                 Err(e) if first_error.is_none() => {
        //                     first_error = Some(e);
        //                     continue;
        //                 }
        //                 _ => continue,
        //             }
        //         }
        //         match first_error {
        //             Some(first_error) => Err(first_error),
        //             None => cannot_unify(),
        //         }
        //     }

        //     // Traits:
        //     (Ty::Trt, Ty::Trt) => Ok(Sub::empty()),
        //     (Ty::Trt, Ty::Unresolved(unresolved)) => Ok(Sub::from_pairs([(
        //         SubSubject::Unresolved(unresolved),
        //         self.primitive_builder().create_ty_value(src_id),
        //     )])),
        //     (Ty::Trt, _) => cannot_unify(),
        //     (Ty::Ty(_), Ty::Unresolved(unresolved)) => Ok(Sub::from_pairs([(
        //         SubSubject::Unresolved(unresolved),
        //         self.primitive_builder().create_ty_value(src_id),
        //     )])),

        //     // Types:
        //     (Ty::Ty(src_bound), Ty::Ty(target_bound)) => {
        //         match target_bound {
        //             Some(target_bound) => {
        //                 match src_bound {
        //                     // Trait bounds are the same
        //                     Some(src_bound) if src_bound == target_bound => Ok(Sub::empty()),
        //                     Some(_) | None => {
        //                         // Missing bound on source required by target
        //                         cannot_unify()
        //                     }
        //                 }
        //             }
        //             // No bounds on target
        //             None => Ok(Sub::empty()),
        //         }
        //     }
        //     (Ty::Ty(_), _) => cannot_unify(),

        //     // Nominals
        //     (Ty::NominalDef(_), Ty::NominalDef(_)) => todo!(),
        //     (Ty::NominalDef(_), Ty::Unresolved(_)) => todo!(),
        //     (Ty::NominalDef(_), _) => cannot_unify(),

        //     // TyFns
        //     (Ty::TyFn(_), Ty::TyFn(_)) => todo!(),
        //     (Ty::TyFn(_), Ty::Unresolved(_)) => todo!(),
        //     (Ty::TyFn(_), _) => cannot_unify(),

        //     // Unresolved source
        //     (Ty::Unresolved(_), Ty::Trt) => todo!(),
        //     (Ty::Unresolved(_), Ty::Ty(_)) => todo!(),
        //     (Ty::Unresolved(_), Ty::TyFn(_)) => todo!(),
        //     (Ty::Unresolved(_), Ty::Unresolved(_)) => todo!(),
        //     (Ty::Unresolved(_), _) => todo!(),

        //     // Modules
        //     (Ty::ModDef(_), Ty::ModDef(_)) => todo!(),
        //     (Ty::ModDef(_), Ty::Unresolved(_)) => todo!(),
        //     (Ty::ModDef(_), _) => todo!(),

        //     // Tuples
        //     (Ty::Tuple(_), Ty::Tuple(_)) => todo!(),
        //     (Ty::Tuple(_), Ty::Unresolved(_)) => todo!(),
        //     (Ty::Tuple(_), _) => cannot_unify(),

        //     // Functions
        //     (Ty::Fn(_), Ty::Fn(_)) => todo!(),
        //     (Ty::Fn(_), Ty::TyFn(_)) => todo!(), // Should type functions unify? we infer type args anyway...
        //     (Ty::Fn(_), Ty::Unresolved(_)) => todo!(),
        //     (Ty::Fn(_), _) => cannot_unify(),

        //     // Type variables
        //     (Ty::Var(_), Ty::Var(_)) => todo!(),
        //     (Ty::Var(_), Ty::Unresolved(_)) => todo!(),
        //     (Ty::Var(_), _) => todo!(),
        // }
    }
}

#[cfg(test)]
mod tests {
    use super::{Unifier, UnifyTysOpts};
    use crate::{
        ops::building::PrimitiveBuilder,
        storage::{core::CoreDefs, GlobalStorage},
    };

    #[test]
    fn unify_test() {
        // let mut gs = GlobalStorage::new();
        // let core_defs = CoreDefs::new(&mut gs);
        // let builder = PrimitiveBuilder::new(&mut gs);

        // let hash_ty_1 = builder.create_ty_of_ty_with_bound(core_defs.hash_trt);
        // let hash_ty_2 = builder.create_ty_of_ty_with_bound(core_defs.eq_trt);

        // drop(builder);

        // let mut unifier = Unifier::new(&mut gs);
        // let unify_result = unifier.unify_tys(hash_ty_1, hash_ty_2, &UnifyTysOpts {});
        // println!("{:?}", unify_result);
    }
}
