//! All rights reserved 2022 (c) The Hash Language authors
use crate::{
    error::{TypecheckError, TypecheckResult},
    storage::{GlobalStorage, SourceStorage},
    types::{TypeId, TypeStorage, TypeValue, UnknownType},
    writer::{print_type, TypeWithStorage},
};
use core::fmt;
use hash_alloc::collections::row::Row;
use std::{borrow::Borrow, collections::HashSet, iter};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnifyStrategy {
    ModifyBoth,
    ModifyTarget,
    CheckOnly,
}

#[derive(Debug, Clone)]
pub struct Substitution {
    pub subs: Vec<(TypeId, TypeId)>,
}

pub struct SubstitutionWithStorage<'s, 'c, 'w, 'gs>(&'s Substitution, &'gs GlobalStorage<'c, 'w>);

impl<'s, 'c, 'w, 'gs> SubstitutionWithStorage<'s, 'c, 'w, 'gs> {
    pub fn new(sub: &'s Substitution, storage: &'gs GlobalStorage<'c, 'w>) -> Self {
        Self(sub, storage)
    }
}

impl<'s, 'c, 'w, 'gs> fmt::Display for SubstitutionWithStorage<'s, 'c, 'w, 'gs> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for sub in &self.0.subs {
            writeln!(
                f,
                "{} -> {}",
                TypeWithStorage::new(sub.0, self.1,),
                TypeWithStorage::new(sub.1, self.1,),
            )?;
        }
        Ok(())
    }
}

impl<'c> Substitution {
    pub fn empty() -> Self {
        Self { subs: Vec::new() }
    }

    #[must_use]
    pub fn merge(mut self, other: impl Borrow<Substitution>) -> Self {
        self.subs.extend(other.borrow().subs.iter().copied());
        self
    }

    pub fn add(&mut self, from: TypeId, to: TypeId) {
        self.subs.push((from, to));
    }

    pub fn from_pairs(
        pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
    ) -> Self {
        Self {
            subs: pairs.map(|(x, y)| (*x.borrow(), *y.borrow())).collect(),
        }
    }
}

pub struct Unifier<'c, 'w, 'ms, 'gs> {
    module_storage: &'ms mut SourceStorage,
    global_storage: &'gs mut GlobalStorage<'c, 'w>,
}

fn _extract_type_var_set(ty: TypeId, types: &TypeStorage) -> HashSet<TypeId> {
    types
        .get(ty)
        .fold_type_ids(HashSet::new(), |mut vars, inner_ty| {
            match types.get(inner_ty) {
                TypeValue::Var(_) => {
                    vars.insert(inner_ty);
                    vars
                }
                _ => vars,
            }
        })
}

fn _extract_type_var_set_from_list(tys: &[TypeId], types: &TypeStorage) -> HashSet<TypeId> {
    tys.iter().fold(HashSet::new(), |mut type_vars, &ty| {
        type_vars.extend(_extract_type_var_set(ty, types));
        type_vars
    })
}

impl<'c, 'w, 'ms, 'gs> Unifier<'c, 'w, 'ms, 'gs> {
    pub fn new(
        module_storage: &'ms mut SourceStorage,
        global_storage: &'gs mut GlobalStorage<'c, 'w>,
    ) -> Self {
        Self {
            module_storage,
            global_storage,
        }
    }

    pub fn unify_pairs(
        &mut self,
        pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
        strategy: UnifyStrategy,
    ) -> TypecheckResult<()> {
        for (a, b) in pairs {
            let a_ty = *a.borrow();
            let b_ty = *b.borrow();
            self.unify(a_ty, b_ty, strategy)?;
        }

        Ok(())
    }

    pub fn unify_many(
        &mut self,
        mut type_list: impl Iterator<Item = TypeId>,
        strategy: UnifyStrategy,
    ) -> TypecheckResult<TypeId> {
        let first = type_list
            .next()
            .unwrap_or_else(|| self.global_storage.types.create_unknown_type());
        for curr in type_list {
            self.unify(curr, first, strategy)?;
        }
        Ok(first)
    }

    pub fn instantiate_vars_list(&mut self, vars: &[TypeId]) -> TypecheckResult<Substitution> {
        self.instantiate_vars_for_list(vars, vars)
    }

    pub fn instantiate_vars_for_list(
        &mut self,
        tys: &[TypeId],
        vars: &[TypeId],
    ) -> TypecheckResult<Substitution> {
        tys.iter()
            .map(|&arg| self.instantiate_vars(arg, vars))
            .fold(Ok(Substitution::empty()), |acc, x| Ok(acc?.merge(x?)))
    }

    pub fn instantiate_vars(
        &mut self,
        ty: TypeId,
        vars: &[TypeId],
    ) -> TypecheckResult<Substitution> {
        let ty_val = self.global_storage.types.get(ty);

        let maybe_get_ty_sub = |ty: TypeId, unifier: &mut Unifier| {
            if matches!(unifier.global_storage.types.get(ty), TypeValue::Var(_)) {
                for &var_ty in vars {
                    let unify_result = unifier.unify(ty, var_ty, UnifyStrategy::CheckOnly);
                    if unify_result.is_ok() {
                        return Some((ty, unifier.global_storage.types.create_unknown_type()));
                    }
                }
            }
            None
        };

        // Edge case where ty is a type variable.
        if let Some(sub) = maybe_get_ty_sub(ty, self) {
            return Ok(Substitution::from_pairs(iter::once(sub)));
        }

        ty_val.fold_type_ids(Ok(Substitution::empty()), |acc, ty| {
            if let Some(sub) = maybe_get_ty_sub(ty, self) {
                let mut acc = acc?;
                acc.add(sub.0, sub.1);
                Ok(acc)
            } else {
                Ok(acc?.merge(self.instantiate_vars(ty, vars)?))
            }
        })
    }

    pub fn apply_sub_to_list_make_row(
        &mut self,
        sub: &Substitution,
        tys: &[TypeId],
    ) -> TypecheckResult<Row<'c, TypeId>> {
        let wall = self.global_storage.wall();
        Row::try_from_iter(tys.iter().map(|&ty| self.apply_sub(sub, ty)), wall)
    }

    pub fn apply_sub_to_list_make_vec(
        &mut self,
        sub: &Substitution,
        tys: &[TypeId],
    ) -> TypecheckResult<Vec<TypeId>> {
        tys.iter().map(|&ty| self.apply_sub(sub, ty)).collect()
    }

    pub fn apply_sub(&mut self, sub: &Substitution, ty: TypeId) -> TypecheckResult<TypeId> {
        let mut curr_ty = ty;
        for &(from, to) in &sub.subs {
            let unify_result = self.unify(from, ty, UnifyStrategy::CheckOnly);
            if unify_result.is_ok() {
                curr_ty = to;
            }
        }

        let wall = self.global_storage.wall();
        let new_ty_value = self
            .global_storage
            .types
            .get(curr_ty)
            .try_map_type_ids(|ty_id| self.apply_sub(sub, ty_id), wall)?;

        let created = self.global_storage.types.create(new_ty_value, None);
        Ok(created)
    }

    pub fn unify(
        &mut self,
        target: TypeId,
        source: TypeId,
        strategy: UnifyStrategy,
    ) -> TypecheckResult<()> {
        // Already the same type
        if target == source {
            return Ok(());
        }

        // @@TODO: Figure out covariance, contravariance, and invariance rules.
        // Right now, there are no sub/super types, so these variance rules aren't applicable. In
        // other words, unify is symmetric over target/source. However it is not foreseeable that
        // this will continue to be the case in the future.

        let target_ty = self.global_storage.types.get(target);
        let source_ty = self.global_storage.types.get(source);

        use TypeValue::*;
        match (target_ty, source_ty) {
            (Ref(ref_target), Ref(ref_source)) => {
                self.unify(ref_target.inner, ref_source.inner, strategy)?;

                Ok(())
            }
            (RawRef(raw_target), RawRef(raw_source)) => {
                self.unify(raw_target.inner, raw_source.inner, strategy)?;

                Ok(())
            }
            (Fn(fn_target), Fn(fn_source)) => {
                // Ensure that the target and source arguments are the same length
                if fn_target.args.len() != fn_source.args.len() {
                    return Err(TypecheckError::FunctionArgumentLengthMismatch {
                        source,
                        target,
                        received: fn_target.args.len(),
                        expected: fn_source.args.len(),
                    });
                }

                self.unify_pairs(fn_target.args.iter().zip(fn_source.args.iter()), strategy)?;
                // Maybe this should be flipped (see variance comment above)
                self.unify(fn_target.ret, fn_source.ret, strategy)?;

                // let merged_sub = args_sub.merge(self, &ret_sub);

                // let unified_ty = Fn(FnType {
                //     args: unified_args,
                //     ret: Box::new(unified_ret),
                // });

                Ok(())
            }
            (Unknown(_), Unknown(_)) => {
                // @@TODO: Ensure that trait bounds are compatible

                Ok(())
            }
            (Unknown(UnknownType { unknown_id }), _) => {
                // @@TODO: Ensure that trait bounds are compatible
                match strategy {
                    UnifyStrategy::ModifyBoth | UnifyStrategy::ModifyTarget => {
                        self.global_storage.types.set_unknown(*unknown_id, source);
                        self.unify(target, source, strategy)?;
                    }
                    UnifyStrategy::CheckOnly => {}
                }
                Ok(())
            }
            (_, Unknown(UnknownType { unknown_id })) => {
                // @@TODO: Ensure that trait bounds are compatible
                match strategy {
                    UnifyStrategy::ModifyBoth => {
                        self.global_storage.types.set_unknown(*unknown_id, target);
                        self.unify(target, source, strategy)?;
                    }
                    UnifyStrategy::ModifyTarget | UnifyStrategy::CheckOnly => {}
                }
                Ok(())
            }
            (Var(var_a), Var(var_b)) if var_a == var_b => Ok(()),
            (Var(var), _) => match self.module_storage.type_vars.potentially_resolve(*var) {
                Some(var_res) => self.unify(var_res, source, strategy),
                None => Err(TypecheckError::TypeMismatch(target, source)),
            },
            (_, Var(var)) => match self.module_storage.type_vars.potentially_resolve(*var) {
                Some(var_res) => self.unify(target, var_res, strategy),
                None => Err(TypecheckError::TypeMismatch(target, source)),
            },
            (User(user_target), User(user_source)) if user_target.def_id == user_source.def_id => {
                // Make sure we got same number of type arguments
                assert_eq!(user_target.args.len(), user_source.args.len());

                // Unify type arguments.
                self.unify_pairs(
                    (user_target.args.iter()).zip(user_source.args.iter()),
                    strategy,
                )?;

                // let unified_ty_id = self.create(User(UserType {
                //     def_id: user_target.def_id,
                //     args: unified_args,
                // }));

                Ok(())
            }
            (Prim(prim_target), Prim(prim_source)) if prim_target == prim_source => Ok(()),
            // (Namespace(ns_target), Namespace(ns_source))
            //     if ns_target.module_idx == ns_source.module_idx =>
            // {
            //     Ok(())
            // }
            _ => Err(TypecheckError::TypeMismatch(target, source)),
        }
    }
}
