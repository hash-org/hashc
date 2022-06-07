pub struct Substitution {
    // from_args: (TyArgs) -> Substitution
}

pub struct TyOps {}

pub struct TyBuilder {}

// TyOps
//
// - unify: (TyId, TyId) -> Result<Substitution>
// - unify_.. helpers for lists, params, args etc
//
// - apply_sub: (TyId, Substitution) -> Result<TyId>
// - apply_sub_.. helpers for lists, params, args etc
//
// - bound_unresolved: (TyId) -> Result<TyId> // result is a type function
//
// - has_unresolved: (TyId) -> bool
// - has_unresolved.. helpers for lists, params, args etc
//
// - find_unresolved: (TyId) -> Vec<ResolutionId>
// - find_unresolved.. helpers for lists, params, args etc
//
//
// - apply_ty_func: (TyFnTyId, TyArgs) -> Result<Substitution>
//
// - closest_supertype: (TyId, TyId) -> Result<TyId>
// - closest_supertype_.. helpers for lists, params, args, etc
