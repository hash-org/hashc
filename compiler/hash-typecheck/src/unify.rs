use hash_alloc::collections::row::Row;

use crate::{
    error::{TypecheckError, TypecheckResult},
    storage::{GlobalStorage, ModuleStorage},
    types::{self, RawRefType, RefType, TupleType, TypeId, TypeValue, UserType},
    writer::TypeWithStorage,
};
use core::fmt;
use std::{borrow::Borrow, slice::SliceIndex};

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

pub struct SubstitutionWithStorage<'s, 'c, 'w, 'm, 'gs>(
    &'s Substitution,
    &'gs GlobalStorage<'c, 'w, 'm>,
);

impl<'s, 'c, 'w, 'm, 'gs> SubstitutionWithStorage<'s, 'c, 'w, 'm, 'gs> {
    pub fn new(sub: &'s Substitution, storage: &'gs GlobalStorage<'c, 'w, 'm>) -> Self {
        Self(sub, storage)
    }
}

impl<'s, 'c, 'w, 'm, 'gs> fmt::Display for SubstitutionWithStorage<'s, 'c, 'w, 'm, 'gs> {
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

    pub fn merge(mut self, other: impl Borrow<Substitution>) -> Self {
        self.subs.extend(other.borrow().subs.iter().map(|x| *x));
        self
    }

    pub fn from_pairs(
        pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
    ) -> Self {
        Self {
            subs: pairs.map(|(x, y)| (*x.borrow(), *y.borrow())).collect(),
        }
    }
}

pub struct Unifier<'c, 'w, 'm, 'ms, 'gs> {
    module_storage: &'ms mut ModuleStorage,
    global_storage: &'gs mut GlobalStorage<'c, 'w, 'm>,
}

impl<'c, 'w, 'm, 'ms, 'gs> Unifier<'c, 'w, 'm, 'ms, 'gs> {
    pub fn new(
        module_storage: &'ms mut ModuleStorage,
        global_storage: &'gs mut GlobalStorage<'c, 'w, 'm>,
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
        match ty_val {
            TypeValue::Ref(RefType { inner }) => self.instantiate_vars(*inner, vars),
            TypeValue::RawRef(RawRefType { inner }) => self.instantiate_vars(*inner, vars),
            TypeValue::Fn(types::FnType { args, ret }) => Ok(args
                .iter()
                .map(|&arg| self.instantiate_vars(arg, vars))
                .fold(Ok(Substitution::empty()), |acc, x| Ok(acc?.merge(x?)))?
                .merge(self.instantiate_vars(*ret, vars)?)),
            TypeValue::Var(_) => Ok(Substitution::from_pairs(
                vars.iter()
                    .find_map(|&target_var| {
                        let unify_result = self.unify(target_var, ty, UnifyStrategy::CheckOnly);
                        if unify_result.is_ok() {
                            let unknown_ty = self.global_storage.types.create_unknown_type();
                            Some((ty, unknown_ty))
                        } else {
                            None
                        }
                    })
                    .into_iter(),
            )),
            TypeValue::User(UserType { args, .. }) => args
                .iter()
                .map(|&arg| self.instantiate_vars(arg, vars))
                .fold(Ok(Substitution::empty()), |acc, x| Ok(acc?.merge(x?))),
            TypeValue::Prim(_) => Ok(Substitution::empty()),
            TypeValue::Tuple(TupleType { types: args }) => args
                .iter()
                .map(|&arg| self.instantiate_vars(arg, vars))
                .fold(Ok(Substitution::empty()), |acc, x| Ok(acc?.merge(x?))),
            TypeValue::Unknown(_) => Ok(Substitution::empty()),
            TypeValue::Namespace(_) => Ok(Substitution::empty()),
        }
    }

    pub fn apply_sub_to_list_make_row(
        &mut self,
        sub: &Substitution,
        tys: &[TypeId],
    ) -> TypecheckResult<Row<'c, TypeId>> {
        let wall = self.global_storage.wall();
        Ok(Row::try_from_iter(
            tys.iter().map(|&ty| self.apply_sub(sub, ty)),
            wall,
        )?)
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
        // @@Broken: here new unknown types will get created, will lose identity. We need a
        // different way to keep track of unknown types, basically a mapping like GenTypeVar in haskell. OR, we prevent loss of identity somehow

        let created = self.global_storage.types.create(new_ty_value);
        // self.unify(created, curr_ty, UnifyStrategy::ModifyTarget)?;
        Ok(curr_ty)
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
            (Unknown(_), _) => {
                // @@TODO: Ensure that trait bounds are compatible
                match strategy {
                    UnifyStrategy::ModifyBoth | UnifyStrategy::ModifyTarget => {
                        self.global_storage.types.set(target, source);
                        self.unify(target, source, strategy)?;
                    }
                    UnifyStrategy::CheckOnly => {}
                }
                Ok(())
            }
            (_, Unknown(_)) => {
                // @@TODO: Ensure that trait bounds are compatible
                match strategy {
                    UnifyStrategy::ModifyBoth => {
                        self.global_storage.types.set(source, target);
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
