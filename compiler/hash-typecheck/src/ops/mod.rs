use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{Ty, TyId, UnresolvedTy, ValueId, Var},
        AccessToStorage, StorageRefMut,
    },
};
use std::collections::HashMap;

pub mod building;

pub struct Unifier<'gs, 'ls> {
    storage: StorageRefMut<'gs, 'ls>,
}

pub struct UnifyTysOpts {}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TySubSubject {
    Var(Var),
    Unresolved(UnresolvedTy),
}

/// A substitution for a ty.
#[derive(Debug, Default, Clone)]
pub struct TySub {
    data: HashMap<TySubSubject, TyId>,
}

impl TySub {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn from_pairs(pairs: impl IntoIterator<Item = (TySubSubject, TyId)>) -> Self {
        Self {
            data: pairs.into_iter().collect(),
        }
    }

    pub fn get_sub_for(&self, subject: TySubSubject) -> Option<TyId> {
        self.data.get(&subject).map(|&x| x)
    }

    pub fn merge_with(&mut self, _other: &TySub) {
        todo!()
    }
}

impl PartialEq for TySub {
    fn eq(&self, other: &Self) -> bool {
        // @@Todo: more sophisticated substitution equivalence
        self.data == other.data
    }
}

pub enum ValuesAreEqual {
    Yes,
    No,
    Unsure,
}

impl<'gs, 'ls> Unifier<'gs, 'ls> {
    pub fn new(storage: StorageRefMut<'gs, 'ls>) -> Self {
        Self { storage }
    }

    /// Simplify the given ty
    ///
    /// This basically evaluates any [Ty::AppTyFn], and this is done it returns
    /// `Some(evaluated_ty)`, otherwise returns `None` if no simplification occured.
    pub fn simplify_ty(&self, _ty_id: TyId) -> TcResult<Option<TyId>> {
        // @@Todo eval ty fns
        Ok(None)
    }

    pub fn simplify_value(&self, _value_id: ValueId) -> TcResult<Option<ValueId>> {
        // @@Todo eval ty fns
        Ok(None)
    }

    pub fn ty_of_value(&self, _value_id: ValueId) -> TcResult<TyId> {
        todo!()
    }

    // Use a value as a ty
    pub fn value_as_ty(&self, _value_id: ValueId) -> TcResult<TyId> {
        todo!()
    }

    // Use a value as a ty
    pub fn values_are_equal(&self, _a_id: ValueId, _b_id: ValueId) -> ValuesAreEqual {
        todo!()
    }

    // pub fn unify_args(&self, src_args: &Args, target_args: &Args) -> TcResult<TySub> {}

    pub fn unify_tys(&self, src_id: TyId, target_id: TyId, opts: &UnifyTysOpts) -> TcResult<TySub> {
        let src = self.storage.ty_store().get(src_id);
        let target = self.storage.ty_store().get(target_id);
        let cannot_unify = || -> TcResult<TySub> { Err(TcError::CannotUnify(src_id, target_id)) };

        // Basically, can src be used where a target is required?
        match (src, target) {
            // First, type functions:
            (Ty::AppTyFn(_), Ty::AppTyFn(_)) => {
                todo!()
                // Check if same subject and unify, otherwise evaluate and unify
                // match self.values_are_equal(src_ty_fn_value, target_ty_fn_value) {
                //     ValuesAreEqual::Yes => {
                //             // If the values are equal, then if the arguments unify then we have
                //             // the same tys
                //             self.unify_tys(src_args, target_args, opts)
                //         }
                //     ValuesAreEqual::No => {}
                //     ValuesAreEqual::Unsure => {}
                // }
            }
            (_, Ty::AppTyFn(_)) => {
                // Try to apply the RHS, if it works then try to unify again, else error:
                let simplified_target = self.simplify_ty(target_id)?;
                match simplified_target {
                    Some(simplified_target_id) => {
                        self.unify_tys(src_id, simplified_target_id, opts)
                    }
                    None => cannot_unify(),
                }
            }
            (Ty::AppTyFn(_), _) => {
                // Try to apply the LHS, if it works then try to unify again, else error:
                let simplified_src = self.simplify_ty(src_id)?;
                match simplified_src {
                    Some(simplified_src_id) => self.unify_tys(simplified_src_id, target_id, opts),
                    None => cannot_unify(),
                }
            }

            // Merging:
            (Ty::Merge(_), Ty::Merge(inner_target)) => {
                // Try to merge source with each individual type in target. If all succeed,
                // then the whole thing should succeed.
                let mut subs = TySub::empty();
                for inner_target_id in inner_target {
                    match self.unify_tys(src_id, *inner_target_id, opts) {
                        Ok(result) => {
                            subs.merge_with(&result);
                            continue;
                        }
                        Err(e) => return Err(e),
                    }
                }
                Ok(subs)
            }
            (_, Ty::Merge(inner_target)) => {
                // This is only valid if the merge has one element and unifies with source
                match inner_target.as_slice() {
                    [inner_target_id] => self.unify_tys(src_id, *inner_target_id, opts),
                    _ => cannot_unify(),
                }
            }
            (Ty::Merge(inner_src), _) => {
                // Try to merge each individual type in source, with target. If any one succeeds,
                // then the whole thing should succeed.
                let mut first_error = None;
                for inner_src_id in inner_src {
                    match self.unify_tys(*inner_src_id, target_id, opts) {
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

            // Traits:
            (Ty::Trt, Ty::Trt) => Ok(TySub::empty()),
            (Ty::Trt, Ty::Unresolved(unresolved)) => Ok(TySub::from_pairs([(
                TySubSubject::Unresolved(*unresolved),
                src_id,
            )])),
            (Ty::Trt, _) => cannot_unify(),
            (Ty::Ty(_), Ty::Unresolved(unresolved)) => Ok(TySub::from_pairs([(
                TySubSubject::Unresolved(*unresolved),
                src_id,
            )])),

            // Types:
            (Ty::Ty(src_bound), Ty::Ty(target_bound)) => {
                match target_bound {
                    Some(target_bound) => {
                        match src_bound {
                            // Trait bounds are the same
                            Some(src_bound) if src_bound == target_bound => Ok(TySub::empty()),
                            Some(_) | None => {
                                // Missing bound on source required by target
                                cannot_unify()
                            }
                        }
                    }
                    // No bounds on target
                    None => Ok(TySub::empty()),
                }
            }
            (Ty::Ty(_), _) => cannot_unify(),

            // Runtime
            // (Ty::Rt(_), Ty::Rt(_)) => todo!(),
            // (Ty::Rt(_), Ty::Unresolved(_)) => todo!(),
            // (Ty::Rt(_), _) => cannot_unify(),

            // TyFns
            (Ty::TyFn(_), Ty::TyFn(_)) => todo!(),
            (Ty::TyFn(_), Ty::Unresolved(_)) => todo!(),
            (Ty::TyFn(_), _) => cannot_unify(),

            // Unresolved
            (Ty::Unresolved(_), Ty::Trt) => todo!(),
            (Ty::Unresolved(_), Ty::Ty(_)) => todo!(),
            // (Ty::Unresolved(_), Ty::Rt(_)) => todo!(),
            (Ty::Unresolved(_), Ty::TyFn(_)) => todo!(),
            (Ty::Unresolved(_), Ty::Unresolved(_)) => todo!(),
            (Ty::NominalDef(_), Ty::TyFn(_)) => todo!(),
            (Ty::NominalDef(_), Ty::Trt) => todo!(),
            (Ty::NominalDef(_), Ty::Ty(_)) => todo!(),
            (Ty::NominalDef(_), Ty::NominalDef(_)) => todo!(),
            (Ty::NominalDef(_), Ty::ModDef(_)) => todo!(),
            (Ty::NominalDef(_), Ty::Tuple(_)) => todo!(),
            (Ty::NominalDef(_), Ty::Fn(_)) => todo!(),
            (Ty::NominalDef(_), Ty::Var(_)) => todo!(),
            (Ty::NominalDef(_), Ty::Unresolved(_)) => todo!(),
            (Ty::ModDef(_), Ty::TyFn(_)) => todo!(),
            (Ty::ModDef(_), Ty::Trt) => todo!(),
            (Ty::ModDef(_), Ty::Ty(_)) => todo!(),
            (Ty::ModDef(_), Ty::NominalDef(_)) => todo!(),
            (Ty::ModDef(_), Ty::ModDef(_)) => todo!(),
            (Ty::ModDef(_), Ty::Tuple(_)) => todo!(),
            (Ty::ModDef(_), Ty::Fn(_)) => todo!(),
            (Ty::ModDef(_), Ty::Var(_)) => todo!(),
            (Ty::ModDef(_), Ty::Unresolved(_)) => todo!(),
            (Ty::Tuple(_), Ty::TyFn(_)) => todo!(),
            (Ty::Tuple(_), Ty::Trt) => todo!(),
            (Ty::Tuple(_), Ty::Ty(_)) => todo!(),
            (Ty::Tuple(_), Ty::NominalDef(_)) => todo!(),
            (Ty::Tuple(_), Ty::ModDef(_)) => todo!(),
            (Ty::Tuple(_), Ty::Tuple(_)) => todo!(),
            (Ty::Tuple(_), Ty::Fn(_)) => todo!(),
            (Ty::Tuple(_), Ty::Var(_)) => todo!(),
            (Ty::Tuple(_), Ty::Unresolved(_)) => todo!(),
            (Ty::Fn(_), Ty::TyFn(_)) => todo!(),
            (Ty::Fn(_), Ty::Trt) => todo!(),
            (Ty::Fn(_), Ty::Ty(_)) => todo!(),
            (Ty::Fn(_), Ty::NominalDef(_)) => todo!(),
            (Ty::Fn(_), Ty::ModDef(_)) => todo!(),
            (Ty::Fn(_), Ty::Tuple(_)) => todo!(),
            (Ty::Fn(_), Ty::Fn(_)) => todo!(),
            (Ty::Fn(_), Ty::Var(_)) => todo!(),
            (Ty::Fn(_), Ty::Unresolved(_)) => todo!(),
            (Ty::Var(_), Ty::TyFn(_)) => todo!(),
            (Ty::Var(_), Ty::Trt) => todo!(),
            (Ty::Var(_), Ty::Ty(_)) => todo!(),
            (Ty::Var(_), Ty::NominalDef(_)) => todo!(),
            (Ty::Var(_), Ty::ModDef(_)) => todo!(),
            (Ty::Var(_), Ty::Tuple(_)) => todo!(),
            (Ty::Var(_), Ty::Fn(_)) => todo!(),
            (Ty::Var(_), Ty::Var(_)) => todo!(),
            (Ty::Var(_), Ty::Unresolved(_)) => todo!(),
            (Ty::Unresolved(_), Ty::NominalDef(_)) => todo!(),
            (Ty::Unresolved(_), Ty::ModDef(_)) => todo!(),
            (Ty::Unresolved(_), Ty::Tuple(_)) => todo!(),
            (Ty::Unresolved(_), Ty::Fn(_)) => todo!(),
            (Ty::Unresolved(_), Ty::Var(_)) => todo!(),
        }
    }
}
