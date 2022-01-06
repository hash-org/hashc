use crate::{
    error::{TypecheckError, TypecheckResult},
    storage::{GlobalStorage, ModuleStorage},
    types::{self, RawRefType, RefType, TupleType, TypeId, TypeList, TypeValue, Types, UserType},
};
use std::{borrow::Borrow, slice::SliceIndex};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnifyStrategy {
    ModifyBoth,
    ModifyTarget,
    CheckOnly,
}

// pub struct Substitution<'c> {
//     data: HashMap<&'c TypeValue<'c>, &'c TypeValue<'c>>,
// }

// impl<'c> Substitution<'c> {
//     pub fn new(
//         subs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
//         types: &Types<'c, '_>,
//     ) -> Self {
//         Self {
//             data: subs
//                 .map(|(x, y)| (types.get(*x.borrow()), types.get(*y.borrow())))
//                 .collect(),
//         }
//     }

//     pub fn apply(&self, dest: TypeId, types: &Types<'c, '_>) {
//         let dest = types.get(dest);
//         if let Some(&src) = self.data.get(&dest) {
//             types.set(dest, src);
//         } else {
//             match types.get(dest) {
//                 TypeValue::Ref(RefType { inner }) => self.apply(*inner, types),
//                 TypeValue::RawRef(RawRefType { inner }) => self.apply(*inner, types),
//                 TypeValue::Fn(FnType { args, ret }) => {
//                     args.iter().for_each(|&arg| self.apply(arg, types));
//                     self.apply(*ret, types);
//                 }
//                 TypeValue::Var(_) => {}
//                 TypeValue::User(UserType { args, .. }) => {
//                     args.iter().for_each(|&arg| self.apply(arg, types))
//                 }
//                 TypeValue::Prim(_) => {}
//                 TypeValue::Tuple(TupleType { types: args }) => {
//                     args.iter().for_each(|&arg| self.apply(arg, types))
//                 }
//                 TypeValue::Unknown(_) => {}
//                 TypeValue::Namespace(_) => {}
//             }
//         }
//     }

//     pub fn merge(&self, other: &Substitution, types: &Types) -> TypecheckResult<()> {
//         for (&from, &to) in self.data.iter() {
//             other.apply(to, types);
//         }

//         for (&from, &to) in other.data.iter() {
//             if let Some(&this_to) = self.data.get(&from) {
//                 unifier.unify(this_to, to)?;
//             } else if let Some(&next_to) = self.data.get(&to) {
//             }
//         }

//         Ok(())
//     }
// }
#[derive(Debug, Clone)]
pub struct Substitution {
    subs: Vec<(TypeId, TypeId)>,
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

    // pub fn from_vars(type_vars: &[TypeId], types: &mut Types) -> Self {
    //     Self {
    //         subs: type_vars
    //             .iter()
    //             .map(|&ty| {
    //                 let ty_value = types.get(ty);
    //                 if matches!(ty_value, TypeValue::Var(_)) {
    //                     let unknown_ty = types.create_unknown_type();
    //                     (ty, unknown_ty)
    //                 } else {
    //                     panic!(
    //                         "Got type list with other types than type variables: {:?}",
    //                         type_vars
    //                     )
    //                 }
    //             })
    //             .collect(),
    //     }
    // }
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
        let strategy = strategy.into();
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

    pub fn apply_sub_to_list(&mut self, sub: &Substitution, tys: &[TypeId]) -> Vec<TypeId> {
        tys.iter().map(|&ty| self.apply_sub(sub, ty)).collect()
    }

    pub fn apply_sub(&mut self, sub: &Substitution, ty: TypeId) -> TypeId {
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
            .map_type_ids(|ty_id| self.apply_sub(sub, ty_id), wall);

        self.global_storage.types.create(new_ty_value)
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
                    }
                    UnifyStrategy::ModifyTarget | UnifyStrategy::CheckOnly => {}
                }

                Ok(())
            }
            (Var(var_target), Var(var_source)) if var_target == var_source => Ok(()),
            (_, Var(var_source)) => match self.module_storage.type_vars.resolve(*var_source) {
                Some(resolved) => self.unify(target, resolved, strategy),
                None => Err(TypecheckError::TypeMismatch(target, source)),
            },
            (Var(var_target), _) => match self.module_storage.type_vars.resolve(*var_target) {
                Some(resolved) => self.unify(resolved, source, strategy),
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
