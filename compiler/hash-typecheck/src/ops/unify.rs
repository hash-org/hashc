//! Utilities related to type unification and substitution.
//!
//! @@Incomplete(kontheocharis): this module is currently under construction.

// @@Remove
#![allow(unused)]

use crate::{
    error::{TcError, TcResult},
    storage::{
        primitives::{
            AppTyFn, Arg, Args, Param, Params, Ty, TyId, UnresolvedTy, Value, ValueId, Var,
        },
        GlobalStorage,
    },
};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut},
};

use super::building::PrimitiveBuilder;

/// A substitution containing pairs of `(TySubSubject, TyId)` to be applied to a type or types.
#[derive(Debug, Default, Clone)]
pub struct TySub {
    data: HashMap<TySubSubject, TyId>,
}

impl TySub {
    /// Create an empty substitution.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Create a substitution from pairs of `(TySubSubject, TyId)`.
    pub fn from_pairs(pairs: impl IntoIterator<Item = (TySubSubject, TyId)>) -> Self {
        Self {
            data: pairs.into_iter().collect(),
        }
    }

    /// Get the substitution for the given [TySubSubject], if any.
    pub fn get_sub_for(&self, subject: TySubSubject) -> Option<TyId> {
        self.data.get(&subject).copied()
    }

    /// Merge the substitution with another.
    ///
    /// Modifies `self`.
    pub fn merge_with(&mut self, _other: &TySub) {
        todo!()
    }
}

/// Implements equality of substitutions in terms of functional equality---will applying A produce
/// the same type as B?
///
/// @@Volatile: This might require having access to the storage to check equality of some things..
impl PartialEq for TySub {
    fn eq(&self, other: &Self) -> bool {
        // @@Todo: more sophisticated substitution equivalence
        self.data == other.data
    }
}

/// A judgement as to whether two values are equal, which also might be unclear (for example if
/// higher order type variables are involved).
pub enum ValuesAreEqual {
    Yes,
    No,
    Unsure,
}

/// Performs type unification and other related operations.
pub struct Unifier<'gs> {
    gs: &'gs mut GlobalStorage,
}

/// Options that are received by the unifier when unifying types.
pub struct UnifyTysOpts {}

/// The subject of a substitution, either a type variable or an unresolved type.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TySubSubject {
    Var(Var),
    Unresolved(UnresolvedTy),
}

impl<'gs> Unifier<'gs> {
    pub fn new(gs: &'gs mut GlobalStorage) -> Self {
        Self { gs }
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
        params: &Params,
        args: &Args,
        unify_opts: &UnifyTysOpts,
    ) -> TcResult<TySub> {
        let pairs = self.pair_args_with_params(params, args)?;
        let mut subs = TySub::empty();

        for (param, arg) in pairs {
            // Unify each argument's type with the type of the parameter
            let arg_ty = self.ty_of_value(arg.value)?;
            let sub = self.unify_tys(arg_ty, param.ty, unify_opts)?;
            subs.merge_with(&sub);
        }

        Ok(subs)
    }

    fn apply_ty_fn(&mut self, apply_ty_fn: &AppTyFn) -> TcResult<Option<ValueId>> {
        let subject_id = self
            .simplify_value(apply_ty_fn.ty_fn_value)?
            .unwrap_or(apply_ty_fn.ty_fn_value);
        let subject = self.gs.value_store.get(subject_id);
        match subject {
            Value::TyFn(_) => {
                todo!()
            }
            Value::AppTyFn(inner_apply_ty_fn) => {
                let inner_apply_ty_fn = inner_apply_ty_fn.clone();
                // Recurse
                let inner_apply_ty_fn_result_id = self.apply_ty_fn(&inner_apply_ty_fn)?;
                match inner_apply_ty_fn_result_id {
                    Some(inner_apply_ty_fn_result_id) => {
                        match self.gs.value_store.get(inner_apply_ty_fn_result_id) {
                            Value::TyFn(_) => self.apply_ty_fn(&AppTyFn {
                                ty_fn_value: inner_apply_ty_fn_result_id,
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

    /// Simplify the given type.
    ///
    /// This basically evaluates any [Ty::AppTyFn], and if this is done it returns
    /// `Some(evaluated_ty)`, otherwise returns `None` if no simplification occured.
    pub fn simplify_ty(&mut self, ty_id: TyId) -> TcResult<Option<TyId>> {
        let ty = self.gs.ty_store.get(ty_id);
        match ty {
            Ty::AppTyFn(apply_ty_fn) => {
                let apply_ty_fn = apply_ty_fn.clone();
                let result = self.apply_ty_fn(&apply_ty_fn)?;
                match result {
                    Some(result) => Some(self.value_as_ty(result)).transpose(),
                    None => Ok(None),
                }
            }
            Ty::Merge(inner) => {
                let inner = inner.clone();
                let inner_tys = inner
                    .iter()
                    .map(|&ty| self.simplify_ty(ty))
                    .collect::<Result<Vec<_>, _>>()?;
                let builder = PrimitiveBuilder::new(self.gs);
                if inner_tys.iter().any(|x| x.is_some()) {
                    Ok(Some(
                        builder.create_merge_ty(
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

    /// Simplify the given value.
    ///
    /// Same technicality applies as for [Self::simplify_ty].
    pub fn simplify_value(&mut self, value_id: ValueId) -> TcResult<Option<ValueId>> {
        let value = self.gs.value_store.get(value_id);
        match value {
            Value::AppTyFn(apply_ty_fn) => {
                let apply_ty_fn = apply_ty_fn.clone();
                let result = self.apply_ty_fn(&apply_ty_fn)?;
                match result {
                    Some(result) => Ok(Some(result)),
                    None => Ok(None),
                }
            }
            Value::Merge(inner) => {
                let inner = inner.clone();
                let inner_tys = inner
                    .iter()
                    .map(|&ty| self.simplify_value(ty))
                    .collect::<Result<Vec<_>, _>>()?;
                let builder = PrimitiveBuilder::new(self.gs);
                if inner_tys.iter().any(|x| x.is_some()) {
                    Ok(Some(
                        builder.create_merge_value(
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

    /// Get the type of the given value.
    pub fn ty_of_value(&mut self, value_id: ValueId) -> TcResult<TyId> {
        let value = self.gs.value_store.get(value_id).clone();
        let builder = PrimitiveBuilder::new(self.gs);
        Ok(match value {
            Value::Trt(_) => builder.create_ty_of_trt(),
            Value::Ty(ty_id) => builder.create_ty_of_ty(),
            Value::Rt(rt_ty_id) => rt_ty_id,
            Value::TyFn(ty_fn) => builder.create_ty_fn_ty(
                ty_fn.general_params.positional().iter().cloned(),
                ty_fn.general_return_ty,
            ),
            // @@Incomplete:
            Value::AppTyFn(_) => todo!(),
            Value::ModDef(mod_def_id) => builder.create_mod_def_ty(mod_def_id),
            Value::NominalDef(nominal_def_id) => builder.create_nominal_ty(nominal_def_id),
            // @@Incomplete: We need scopes for this:
            Value::Var(_) => todo!(),
            Value::Merge(values) => {
                drop(builder);
                let inner_tys = values
                    .iter()
                    .map(|&value| self.ty_of_value(value))
                    .collect::<Result<Vec<_>, _>>()?;

                let builder = PrimitiveBuilder::new(self.gs);
                builder.create_merge_ty(inner_tys)
            }
            Value::Unset(ty_id) => ty_id,
        })
    }

    /// Try to use the value as a type. Only works if the value is
    /// [Value::Ty](crate::storage::primitives::Value) or resolves to such a thing (for example
    /// applied type functions).
    pub fn value_as_ty(&mut self, value_id: ValueId) -> TcResult<TyId> {
        let value = self.gs.value_store.get(value_id).clone();
        let builder = PrimitiveBuilder::new(self.gs);
        match value {
            Value::Ty(ty_id) => Ok(ty_id),
            Value::AppTyFn(_) => match self.simplify_value(value_id)? {
                Some(simplified_value_id) => self.value_as_ty(simplified_value_id),
                None => Err(TcError::CannotUseValueAsTy(value_id)),
            },
            Value::Merge(values) => {
                drop(builder);
                let inner_tys = values
                    .iter()
                    .map(|&value| self.value_as_ty(value))
                    .collect::<Result<Vec<_>, _>>()?;
                let builder = PrimitiveBuilder::new(self.gs);
                Ok(builder.create_merge_ty(inner_tys))
            }
            Value::ModDef(mod_def_id) => Ok(builder.create_mod_def_ty(mod_def_id)),
            Value::NominalDef(nominal_def_id) => Ok(builder.create_nominal_ty(nominal_def_id)),
            Value::Trt(trt_def_id) => Ok(builder.create_ty_of_ty_with_bound(trt_def_id)),
            Value::TyFn(ty_fn) => todo!(),
            Value::Rt(_) => Err(TcError::CannotUseValueAsTy(value_id)),
            Value::Var(var) => {
                // @@Correctness What if the variable is not a type?
                Ok(builder.create_var_ty(var.name))
            }
            Value::Unset(_) => {
                // @@Correctness is this right?
                Err(TcError::CannotUseValueAsTy(value_id))
            }
        }
    }

    // Check whether two values are equal.
    //
    // This might not always work, depending on the complexity of the values, in which case
    // [ValuesAreEqual::Unsure] is returned.
    pub fn values_are_equal(&self, a_id: ValueId, b_id: ValueId) -> ValuesAreEqual {
        let a = self.gs.value_store.get(a_id);
        let b = self.gs.value_store.get(b_id);

        match (a, b) {
            (Value::AppTyFn(_), _) => todo!(),
            (_, Value::AppTyFn(_)) => todo!(),
            (Value::Unset(_), _) | (_, Value::Unset(_)) => {
                panic!("Trying to compare one or two unset values!")
            }
            (Value::Rt(_), Value::Rt(_)) => todo!(),
            (Value::Rt(_), _) | (_, Value::Rt(_)) => ValuesAreEqual::No,
            (Value::Trt(id_a), Value::Trt(id_b)) => {
                if id_a == id_b {
                    ValuesAreEqual::Yes
                } else {
                    ValuesAreEqual::No
                }
            }
            (Value::Trt(_), Value::Ty(_)) => todo!(),
            (Value::Trt(_), Value::TyFn(_)) => todo!(),
            (Value::Trt(_), Value::ModDef(_)) => todo!(),
            (Value::Trt(_), Value::NominalDef(_)) => todo!(),
            (Value::Trt(_), Value::Var(_)) => todo!(),
            (Value::Trt(_), Value::Merge(_)) => todo!(),
            (Value::Ty(_), Value::Trt(_)) => todo!(),
            (Value::Ty(_), Value::Ty(_)) => todo!(),
            (Value::Ty(_), Value::TyFn(_)) => todo!(),
            (Value::Ty(_), Value::ModDef(_)) => todo!(),
            (Value::Ty(_), Value::NominalDef(_)) => todo!(),
            (Value::Ty(_), Value::Var(_)) => todo!(),
            (Value::Ty(_), Value::Merge(_)) => todo!(),
            (Value::TyFn(_), Value::Trt(_)) => todo!(),
            (Value::TyFn(_), Value::Ty(_)) => todo!(),
            (Value::TyFn(_), Value::TyFn(_)) => todo!(),
            (Value::TyFn(_), Value::ModDef(_)) => todo!(),
            (Value::TyFn(_), Value::NominalDef(_)) => todo!(),
            (Value::TyFn(_), Value::Var(_)) => todo!(),
            (Value::TyFn(_), Value::Merge(_)) => todo!(),
            (Value::ModDef(_), Value::Trt(_)) => todo!(),
            (Value::ModDef(_), Value::Ty(_)) => todo!(),
            (Value::ModDef(_), Value::TyFn(_)) => todo!(),
            (Value::ModDef(_), Value::ModDef(_)) => todo!(),
            (Value::ModDef(_), Value::NominalDef(_)) => todo!(),
            (Value::ModDef(_), Value::Var(_)) => todo!(),
            (Value::ModDef(_), Value::Merge(_)) => todo!(),
            (Value::NominalDef(_), Value::Trt(_)) => todo!(),
            (Value::NominalDef(_), Value::Ty(_)) => todo!(),
            (Value::NominalDef(_), Value::TyFn(_)) => todo!(),
            (Value::NominalDef(_), Value::ModDef(_)) => todo!(),
            (Value::NominalDef(_), Value::NominalDef(_)) => todo!(),
            (Value::NominalDef(_), Value::Var(_)) => todo!(),
            (Value::NominalDef(_), Value::Merge(_)) => todo!(),
            (Value::Var(_), Value::Trt(_)) => todo!(),
            (Value::Var(_), Value::Ty(_)) => todo!(),
            (Value::Var(_), Value::TyFn(_)) => todo!(),
            (Value::Var(_), Value::ModDef(_)) => todo!(),
            (Value::Var(_), Value::NominalDef(_)) => todo!(),
            (Value::Var(_), Value::Var(_)) => todo!(),
            (Value::Var(_), Value::Merge(_)) => todo!(),
            (Value::Merge(_), Value::Trt(_)) => todo!(),
            (Value::Merge(_), Value::Ty(_)) => todo!(),
            (Value::Merge(_), Value::TyFn(_)) => todo!(),
            (Value::Merge(_), Value::ModDef(_)) => todo!(),
            (Value::Merge(_), Value::NominalDef(_)) => todo!(),
            (Value::Merge(_), Value::Var(_)) => todo!(),
            (Value::Merge(_), Value::Merge(_)) => todo!(),
        }
    }

    // pub fn unify_args(&self, src_args: &Args, target_args: &Args) -> TcResult<TySub> {}

    pub fn unify_tys(
        &mut self,
        src_id: TyId,
        target_id: TyId,
        opts: &UnifyTysOpts,
    ) -> TcResult<TySub> {
        let src = self.gs.ty_store.get(src_id).clone();
        let target = self.gs.ty_store.get(target_id).clone();
        let cannot_unify = || -> TcResult<TySub> { Err(TcError::CannotUnify(src_id, target_id)) };

        // Basically, can src be used where a target is required?
        match (src, target) {
            // First, type functions:
            (Ty::AppTyFn(_), Ty::AppTyFn(_)) => {
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
                todo!()
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
                    match self.unify_tys(src_id, inner_target_id, opts) {
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
                    match self.unify_tys(inner_src_id, target_id, opts) {
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
                TySubSubject::Unresolved(unresolved),
                src_id,
            )])),
            (Ty::Trt, _) => cannot_unify(),
            (Ty::Ty(_), Ty::Unresolved(unresolved)) => Ok(TySub::from_pairs([(
                TySubSubject::Unresolved(unresolved),
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

            // Nominals
            (Ty::NominalDef(_), Ty::NominalDef(_)) => todo!(),
            (Ty::NominalDef(_), Ty::Unresolved(_)) => todo!(),
            (Ty::NominalDef(_), _) => cannot_unify(),

            // TyFns
            (Ty::TyFn(_), Ty::TyFn(_)) => todo!(),
            (Ty::TyFn(_), Ty::Unresolved(_)) => todo!(),
            (Ty::TyFn(_), _) => cannot_unify(),

            // Unresolved source
            (Ty::Unresolved(_), Ty::Trt) => todo!(),
            (Ty::Unresolved(_), Ty::Ty(_)) => todo!(),
            (Ty::Unresolved(_), Ty::TyFn(_)) => todo!(),
            (Ty::Unresolved(_), Ty::Unresolved(_)) => todo!(),
            (Ty::Unresolved(_), _) => todo!(),

            // Modules
            (Ty::ModDef(_), Ty::ModDef(_)) => todo!(),
            (Ty::ModDef(_), Ty::Unresolved(_)) => todo!(),
            (Ty::ModDef(_), _) => todo!(),

            // Tuples
            (Ty::Tuple(_), Ty::Tuple(_)) => todo!(),
            (Ty::Tuple(_), Ty::Unresolved(_)) => todo!(),
            (Ty::Tuple(_), _) => cannot_unify(),

            // Functions
            (Ty::Fn(_), Ty::Fn(_)) => todo!(),
            (Ty::Fn(_), Ty::TyFn(_)) => todo!(), // Should type functions unify? we infer type args anyway...
            (Ty::Fn(_), Ty::Unresolved(_)) => todo!(),
            (Ty::Fn(_), _) => cannot_unify(),

            // Type variables
            (Ty::Var(_), Ty::Var(_)) => todo!(),
            (Ty::Var(_), Ty::Unresolved(_)) => todo!(),
            (Ty::Var(_), _) => todo!(),
        }
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
        let mut gs = GlobalStorage::new();
        let core_defs = CoreDefs::new(&mut gs);
        let builder = PrimitiveBuilder::new(&mut gs);

        let hash_ty_1 = builder.create_ty_of_ty_with_bound(core_defs.hash_trt);
        let hash_ty_2 = builder.create_ty_of_ty_with_bound(core_defs.eq_trt);

        drop(builder);

        let mut unifier = Unifier::new(&mut gs);
        let unify_result = unifier.unify_tys(hash_ty_1, hash_ty_2, &UnifyTysOpts {});
        println!("{:?}", unify_result);
    }
}
