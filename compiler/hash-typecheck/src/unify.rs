use std::borrow::Borrow;

use hash_ast::ast::TypeId;

use crate::{
    error::{TypecheckError, TypecheckResult},
    storage::{GlobalStorage, ModuleStorage},
    types::TypeValue,
};

pub fn unify_pairs(
    module_storage: &mut ModuleStorage,
    global_storage: &GlobalStorage,
    pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
) -> TypecheckResult<()> {
    for (a, b) in pairs {
        let a_ty = *a.borrow();
        let b_ty = *b.borrow();
        unify(module_storage, global_storage, a_ty, b_ty)?;
    }

    Ok(())
}

pub fn unify_many(
    module_storage: &mut ModuleStorage,
    global_storage: &GlobalStorage,
    type_list: impl Iterator<Item = TypeId>,
    default: TypeId,
) -> TypecheckResult<TypeId> {
    let first = default;
    for curr in type_list {
        unify(module_storage, global_storage, curr, first)?;
    }
    Ok(first)
}

pub fn unify(
    module_storage: &mut ModuleStorage,
    global_storage: &GlobalStorage,
    target: TypeId,
    source: TypeId,
) -> TypecheckResult<()> {
    // Already the same type
    if target == source {
        return Ok(());
    }

    // @@TODO: Figure out covariance, contravariance, and invariance rules.
    // Right now, there are no sub/super types, so these variance rules aren't applicable. In
    // other words, unify is symmetric over target/source. However it is not foreseeable that
    // this will continue to be the case in the future.

    let target_ty = global_storage.types.get(target);
    let source_ty = global_storage.types.get(source);

    use TypeValue::*;
    match (target_ty, source_ty) {
        (Ref(ref_target), Ref(ref_source)) => {
            unify(
                module_storage,
                global_storage,
                ref_target.inner,
                ref_source.inner,
            )?;

            Ok(())
        }
        (RawRef(raw_target), RawRef(raw_source)) => {
            unify(
                module_storage,
                global_storage,
                raw_target.inner,
                raw_source.inner,
            )?;

            Ok(())
        }
        (Fn(fn_target), Fn(fn_source)) => {
            unify_pairs(
                module_storage,
                global_storage,
                fn_target.args.iter().zip(fn_source.args.iter()),
            )?;
            // Maybe this should be flipped (see variance comment above)
            unify(module_storage, global_storage, fn_target.ret, fn_source.ret)?;

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
            global_storage.types.set(target, source);

            Ok(())
        }
        (_, Unknown(_)) => {
            // @@TODO: Ensure that trait bounds are compatible
            global_storage.types.set(source, target);

            Ok(())
        }
        (Var(var_target), Var(var_source)) if var_target == var_source => Ok(()),
        (_, Var(var_source)) => match module_storage.type_vars.resolve(*var_source) {
            Some(resolved) => unify(module_storage, global_storage, target, resolved),
            None => Err(TypecheckError::TypeMismatch(target, source)),
        },
        (Var(var_target), _) => match module_storage.type_vars.resolve(*var_target) {
            Some(resolved) => unify(module_storage, global_storage, resolved, source),
            None => Err(TypecheckError::TypeMismatch(target, source)),
        },
        (User(user_target), User(user_source)) if user_target.def_id == user_source.def_id => {
            // Make sure we got same number of type arguments
            assert_eq!(user_target.args.len(), user_source.args.len());

            // Unify type arguments.
            unify_pairs(
                module_storage,
                global_storage,
                (user_target.args.iter()).zip(user_source.args.iter()),
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
