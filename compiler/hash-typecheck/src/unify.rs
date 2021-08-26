use std::{
    borrow::Borrow,
    collections::HashMap,
    iter::{self, FromIterator},
};

use hash_ast::ast::TypeId;
use smallvec::SmallVec;

use crate::types::{
    GenTypeVarId, TypeValue, TypecheckCtx, TypecheckError, TypecheckResult, Types,
};

pub struct Substitutions {
    data: HashMap<GenTypeVarId, TypeId>,
}

impl Substitutions {
    pub fn empty() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    pub fn single(from: GenTypeVarId, to: TypeId) -> Self {
        Self {
            data: HashMap::from_iter(iter::once((from, to))),
        }
    }

    pub fn try_merge(
        types: &Types,
        mut subs: impl Iterator<Item = TypecheckResult<Substitutions>>,
    ) -> TypecheckResult<Substitutions> {
        match subs.next() {
            Some(accumulating_sub) => {
                let mut accumulating_sub = accumulating_sub?;
                for sub in subs {
                    accumulating_sub.update(types, &sub?);
                }

                Ok(accumulating_sub)
            }
            // No elements means empty substitution
            None => Ok(Substitutions::empty()),
        }
    }

    pub fn merge(types: &Types, mut subs: impl Iterator<Item = Substitutions>) -> Substitutions {
        match subs.next() {
            Some(mut accumulating_sub) => {
                for sub in subs {
                    accumulating_sub.update(types, &sub);
                }

                accumulating_sub
            }
            // No elements means empty substitution
            None => Substitutions::empty(),
        }
    }

    pub fn update(&mut self, types: &Types, other: &Substitutions) {
        // Update current values with substitutions.
        for v in self.data.values_mut() {
            if let TypeValue::GenVar(gen_var) = *types.get(*v) {
                if let Some(resolved_type_id) = other.data.get(&gen_var.id) {
                    *v = *resolved_type_id;
                }
            }
        }

        // Update with other values
        for (k, v) in &other.data {
            // If it fails, do nothing (key already present).
            let _ = self.data.try_insert(*k, *v);
        }
    }
}

pub fn unify(
    ctx: &TypecheckCtx,
    a: TypeId,
    b: TypeId,
) -> TypecheckResult<(TypeId, Substitutions)> {
    let ty_a = ctx.types.get(a);
    let ty_b = ctx.types.get(b);

    // @@TODO: Figure out covariance, contravariance, and invariance rules.

    use TypeValue::*;
    match (ty_a, ty_b) {
        (Ref(ref_a), Ref(ref_b)) => unify(ctx, ref_a.id, ref_b.id),
        (RawRef(raw_a), RawRef(raw_b)) => unify(ctx, raw_a.id, raw_b.id),
        (Fn(fn_a), Fn(fn_b)) => {
            // Unify args
            // let unify_pairs(ctx, fn_a.args.iter().zip(fn_b.args.iter()));
            // Unify return type
            todo!()
        }
        (GenVar(gen_a), GenVar(gen_b)) => {
            // Ensure that trait bounds are compatible
            // Copy over each bound (?)
            // Substitute. (?)
            todo!()
        }
        (GenVar(gen_a), _) => {
            // Ensure that trait bounds are compatible
            // Substitute.
            todo!()
        }
        (Var(var_a), Var(var_b)) if var_a == var_b => Ok((a, Substitutions::empty())),
        (User(user_a), User(user_b)) if user_a.def_id == user_b.def_id => {
            // Unify type arguments.
            let (ty, sub) = unify_pairs::<SmallVec<[TypeId; 6]>, _, _>(
                ctx,
                (user_a.args.iter()).zip(user_b.args.iter()),
            )?;

            Ok((a, sub))
        }
        (Prim(prim_a), Prim(prim_b)) if prim_a == prim_b => Ok((a, Substitutions::empty())),
        _ => Err(TypecheckError::TypeMismatch(a, b)),
    }
}
