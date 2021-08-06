use std::collections::HashMap;

use crate::types::{TypecheckCtx, TypecheckError, TypecheckResult};

struct Substitutions {
    data: HashMap<GenTypeVarId, TypeId>,
}

impl Substitutions {
    pub fn empty() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    pub fn try_merge(
        subs: impl Iterator<Item = TypecheckResult<Substitutions>>,
    ) -> TypecheckResult<Substitutions> {
        todo!()
    }

    pub fn combine(&mut self, other: Substitutions) {
        todo!()
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

    match (ty_a, ty_b) {
        (Ref(ref_a), Ref(ref_b)) => unify(ctx, ref_a, ref_b),
        (RawRef(raw_a), RawRef(raw_b)) => unify(ctx, raw_a, raw_b),
        (Fn(fn_a), Fn(fn_b)) => {
            // Unify args
            // Unify return type
            todo!()
        }
        (GenVar(gen_a), _) => {
            // Ensure that trait bounds are compatible
            // Substitute.
            todo!()
        }
        (GenVar(gen_a), GenVar(gen_b)) => {
            // Ensure that trait bounds are compatible
            // Copy over each bound (?)
            // Substitute. (?)
            todo!()
        }
        (Var(var_a), Var(var_b)) if var_a == var_b => Ok(a, Substitutions::empty()),
        (User(user_a), User(user_b)) if user_a.def == user_b.def => {
            // Ensure same type def IDs
            Substitutions::try_merge((user_a.args.iter()).zip(user_b.args.iter()).map(
                |(arg_a, arg_b)| {
                    // Don't care about the unified types, only the
                    // substitutions
                    let (_, sub) = unify(ctx, arg_a, arg_b)?;
                    sub
                },
            ))
        }
        (Prim(prim_a), Prim(prim_b)) if prim_a == prim_b => Ok((a, Substitutions::empty())),
        _ => Err(TypecheckError::TypeMismatch(a, b)),
    }
}
