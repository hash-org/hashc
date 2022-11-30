//! Definitions related to functions.

use core::fmt;
use std::fmt::Display;

use hash_utils::{new_store_key, store::DefaultStore};
use utility_types::omit;

use super::environment::env::{Env, WithEnv};
use crate::new::{args::ArgsId, params::ParamsId, symbols::Symbol, terms::TermId, tys::TyId};

/// A function type.
///
/// In their most general form, function types are written like
/// `pure? unsafe? (a_1:A_1,...,a_n:B_n) where (p_1:P_1,...,p_n:P_n)
/// -> R(a_1,...,a_n,p_1,...,p_n)`, or `impure? unsafe? <a_1:A_1,...,a_n:B_n>
/// where (p_1:P_1,...,p_n:P_n) -> R(a_1,...,a_n,p_1,...,p_n)` for implicit
/// function types.
#[derive(Debug, Clone, Copy)]
pub struct FnTy {
    // @@MemoryUsage: use bitflags here?
    /// Whether the function is implicit.
    ///
    /// Implicit functions look like `<A> -> B`, where as explicit
    /// functions look like `(A) -> B`.
    pub is_implicit: bool,
    /// Whether the function is pure.
    ///
    /// A function is pure if:
    /// - it only calls *pure* functions
    /// - it does not take any mutable references as parameters or captured
    ///   variables.
    // - @@Future: It is guaranteed to terminate
    pub is_pure: bool,
    /// Whether the function is unsafe.
    ///
    /// Unsafe functions can only be called from within unsafe blocks. Certain
    /// functions that violate Hash's type system and/or memory rules should be
    /// marked as unsafe.
    pub is_unsafe: bool,
    /// The parameters of the function.
    pub params: ParamsId,
    /// Any implicit conditions to the function.
    ///
    /// These are to be inferred from the call site context. They might depend
    /// on `params`.
    pub conditions: ParamsId,
    /// The return type of the function.
    ///
    /// This might depend on `params` and `conditions`.
    pub return_type: TyId,
}

/// Intrinsics live in a store.
///
/// Each intrinsic is essentially a function pointer that takes some arguments
#[derive(Clone, Copy)]
pub struct Intrinsic {
    pub name: Symbol,
    pub fn_def: FnDefId,
    pub call: fn(&Env, ArgsId) -> TermId,
}
new_store_key!(pub IntrinsicId);
pub type IntrinsicStore = DefaultStore<IntrinsicId, Intrinsic>;

// Debug for intrinsics needs to be explicit to omit `call`, otherwise rust
// complains.
impl fmt::Debug for Intrinsic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Intrinsic").field("name", &self.name).finish()
    }
}

/// A function body.
#[derive(Debug, Clone, Copy)]
pub enum FnBody {
    /// A function that is defined in Hash.
    ///
    /// This is the most common type of function.
    /// Contains the term of the body.
    Defined(TermId),
    /// A function that is defined in Rust.
    ///
    /// This is used for intrinsics.
    Intrinsic(IntrinsicId),
    /// A function that is an axiom.
    ///
    /// This can never be simplified further than an function call on some
    /// arguments, like constructors.
    Axiom,
}

/// A function definition.
///
/// Every function literal `(x) => y` is a function definition. Function
/// definitions follow the syntax of function types, but followed by `=>
/// r(a_1,...,a_n,p_1,...,p_n)`.
#[derive(Debug, Clone, Copy)]
#[omit(FnDefData, [id], [Debug, Clone, Copy])]
pub struct FnDef {
    /// The ID of the function definition.
    pub id: FnDefId,
    /// The symbolic name of the function, which resolves to its definition name
    /// if given by the user, by querying the data of the symbol.
    pub name: Symbol,
    /// The underlying function type, which is partially or fully annotated on
    /// the function literal (if some aspects of the type are not given, then
    /// they will be type holes).
    pub ty: FnTy,
    /// The return value of the function.
    ///
    /// This depends on `ty.params` and `ty.conditions`.
    pub body: FnBody,
}
new_store_key!(pub FnDefId);

/// Function definitions live in a store
pub type FnDefStore = DefaultStore<FnDefId, FnDef>;

/// A function call.
#[derive(Debug, Clone, Copy)]
pub struct FnCallTerm {
    /// The function being called
    ///
    /// This could be a function definition, a value of a function type, or a
    /// trait method.
    pub subject: TermId,
    // The arguments to the function, sorted by the parameters of the function
    pub args: ArgsId,
    /// Whether the function call is implicit.
    ///
    /// Implicit function calls look like `A<B>`, where as explicit function
    /// calls look like `A(B)`.
    pub is_implicit: bool,
    // @@Design: optional conditions
}

impl Display for WithEnv<'_, FnDefId> {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Display for WithEnv<'_, &FnDef> {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
