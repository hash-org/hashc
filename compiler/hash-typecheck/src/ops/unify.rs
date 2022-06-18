//! Utilities related to type unification and substitution.
use super::AccessToOpsMut;
use crate::{
    error::TcResult,
    storage::{
        primitives::{Args, Params, Sub, TermId},
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

        // First split the domains into three parts: d0, d1, and the intersection (see second loop)
        let d0: HashSet<_> = dom_s0.difference(&dom_s1).copied().collect();
        let t0 = Sub::from_pairs(
            d0.iter()
                .map(|&a| (a, substituter.apply_sub_to_subject(s0, a))),
        );

        let d1: HashSet<_> = dom_s1.difference(&dom_s0).copied().collect();
        let _t1 = Sub::from_pairs(
            d1.iter()
                .map(|&a| (a, substituter.apply_sub_to_subject(s1, a))),
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

    /// Unify the two given terms, producing a substitution.
    ///
    /// The relation between src and target is that src must be a subtype (or eq) of target.
    pub fn unify_terms(&mut self, _src_id: TermId, _target_id: TermId) -> TcResult<Sub> {
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
