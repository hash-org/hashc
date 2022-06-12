use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{
            self, AppTyFn, Kind, KindId, Params, ResolutionId, TyFnKind, UnresolvedTy, Value,
            ValueId, Var,
        },
        AccessToStorage, AccessToStorageMut, StorageRefMut,
    },
};
use hash_ast::ident::Identifier;
use std::collections::HashMap;

pub struct Unifier<'gs, 'ls> {
    storage: StorageRefMut<'gs, 'ls>,
}

pub struct UnifyKindsOpts {}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum KindSubSubject {
    Var(Var),
    Unresolved(UnresolvedTy),
}

/// A substitution for a kind.
#[derive(Debug, Default, Clone)]
pub struct KindSub {
    data: HashMap<KindSubSubject, KindId>,
}

impl KindSub {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn from_pairs(pairs: impl IntoIterator<Item = (KindSubSubject, KindId)>) -> Self {
        Self {
            data: pairs.into_iter().collect(),
        }
    }

    pub fn get_sub_for(&self, subject: KindSubSubject) -> Option<KindId> {
        self.data.get(&subject).map(|&x| x)
    }

    pub fn merge_with(&mut self, other: &KindSub) {
        todo!()
    }
}

impl<'gs, 'ls> Unifier<'gs, 'ls> {
    pub fn new(storage: StorageRefMut<'gs, 'ls>) -> Self {
        Self { storage }
    }

    /// Simplify the given kind
    ///
    /// This basically evaluates any [Kind::AppTyFn], and this is done it returns
    /// `Some(evaluated_kind)`, otherwise returns `None` if no simplification occured.
    pub fn simplify_kind(&self, kind_id: KindId) -> TcResult<Option<KindId>> {
        // @@Todo eval ty fns
        Ok(None)
    }

    pub fn simplify_value(&self, value_id: ValueId) -> TcResult<Option<ValueId>> {
        // @@Todo eval ty fns
        Ok(None)
    }

    pub fn kind_of_value(&self, value_id: ValueId) -> TcResult<KindId> {
        todo!()
    }

    pub fn unify_kinds(
        &self,
        src_id: KindId,
        target_id: KindId,
        opts: &UnifyKindsOpts,
    ) -> TcResult<KindSub> {
        let src = self.storage.kind_store().get(src_id);
        let target = self.storage.kind_store().get(target_id);
        let cannot_unify = || -> TcResult<KindSub> { Err(TcError::CannotUnify(src_id, target_id)) };

        // Basically, can src be used where a target is required?
        match (src, target) {
            // First, type functions:
            (Kind::AppTyFn(_), Kind::AppTyFn(_)) => {
                // Check if same subject and unify, otherwise evaluate and unify
                todo!()
            }
            (_, Kind::AppTyFn(_)) => {
                // Try to apply the RHS, if it works then try to unify again, else error:
                let simplified_target = self.simplify_kind(target_id)?;
                match simplified_target {
                    Some(simplified_target_id) => {
                        self.unify_kinds(src_id, simplified_target_id, opts)
                    }
                    None => cannot_unify(),
                }
            }
            (Kind::AppTyFn(_), _) => {
                // Try to apply the LHS, if it works then try to unify again, else error:
                let simplified_src = self.simplify_kind(src_id)?;
                match simplified_src {
                    Some(simplified_src_id) => {
                        self.unify_kinds(simplified_src_id, target_id, opts)
                    }
                    None => cannot_unify(),
                }
            }

            // Merging:
            (Kind::Merge(_), Kind::Merge(inner_target)) => {
                // Try to merge source with each individual type in target. If all succeed,
                // then the whole thing should succeed.
                let mut subs = KindSub::empty();
                for inner_target_id in inner_target {
                    match self.unify_kinds(src_id, *inner_target_id, opts) {
                        Ok(result) => {
                            subs.merge_with(&result);
                            continue;
                        }
                        Err(e) => return Err(e),
                    }
                }
                Ok(subs)
            }
            (_, Kind::Merge(inner_target)) => {
                // This is only valid if the merge has one element and unifies with source
                match inner_target.as_slice() {
                    [inner_target_id] => self.unify_kinds(src_id, *inner_target_id, opts),
                    _ => cannot_unify(),
                }
            }
            (Kind::Merge(inner_src), _) => {
                // Try to merge each individual type in source, with target. If any one succeeds,
                // then the whole thing should succeed.
                let mut first_error = None;
                for inner_src_id in inner_src {
                    match self.unify_kinds(*inner_src_id, target_id, opts) {
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
            (Kind::Trt, Kind::Trt) => Ok(KindSub::empty()),
            (Kind::Trt, Kind::Unresolved(unresolved)) => Ok(KindSub::from_pairs([(
                KindSubSubject::Unresolved(*unresolved),
                src_id,
            )])),
            (Kind::Trt, _) => cannot_unify(),
            (Kind::Ty(_), Kind::Unresolved(unresolved)) => Ok(KindSub::from_pairs([(
                KindSubSubject::Unresolved(*unresolved),
                src_id,
            )])),

            // Types:
            (Kind::Ty(src_bound), Kind::Ty(target_bound)) => {
                match target_bound {
                    Some(target_bound) => {
                        match src_bound {
                            // Trait bounds are the same
                            Some(src_bound) if src_bound == target_bound => Ok(KindSub::empty()),
                            Some(_) | None => {
                                // Missing bound on source required by target
                                cannot_unify()
                            }
                        }
                    }
                    // No bounds on target
                    None => Ok(KindSub::empty()),
                }
            }
            (Kind::Ty(_), _) => cannot_unify(),

            // Runtime
            (Kind::Rt(_), Kind::Rt(_)) => todo!(),
            (Kind::Rt(_), Kind::Unresolved(_)) => todo!(),
            (Kind::Rt(_), _) => cannot_unify(),

            // TyFns
            (Kind::TyFn(_), Kind::TyFn(_)) => todo!(),
            (Kind::TyFn(_), Kind::Unresolved(_)) => todo!(),
            (Kind::TyFn(_), _) => cannot_unify(),

            // Unresolved
            (Kind::Unresolved(_), Kind::Trt) => todo!(),
            (Kind::Unresolved(_), Kind::Ty(_)) => todo!(),
            (Kind::Unresolved(_), Kind::Rt(_)) => todo!(),
            (Kind::Unresolved(_), Kind::TyFn(_)) => todo!(),
            (Kind::Unresolved(_), Kind::Unresolved(_)) => todo!(),
        }
    }
}
