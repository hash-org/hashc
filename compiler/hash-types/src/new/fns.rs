//! Definitions related to functions.

use hash_utils::{new_store_key, store::DefaultStore};

use crate::new::{args::ArgsId, params::ParamsId, symbols::Symbol, terms::TermId, types::TyId};

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

/// A function definition.
///
/// Every function literal `(x) => y` is a function definition. Function
/// definitions follow the syntax of function types, but followed by `=>
/// r(a_1,...,a_n,p_1,...,p_n)`.
#[derive(Debug, Clone, Copy)]
pub struct FnDef {
    /// The symbolic name of the function, which resolves to its definition name
    /// if given by the user, by querying the data of the symbol.
    pub name: Symbol,
    /// The underlying function type, which is partially or fully annotated on
    /// the function literal (if some aspects of the type are not given, then
    /// they will be type holes).
    pub ty: FnTy,
    /// The return type of the function.
    ///
    /// This might depend on `ty.params` and `ty.conditions`.
    pub return_term: TermId,
    // @@Todo: captured variables
}
new_store_key!(pub FnDefId);

/// Function definitions live in a store
pub type FnDefStore = DefaultStore<FnDefId, FnDef>;

/// A function call.
#[derive(Debug, Clone, Copy)]
pub struct FnCallTerm {
    /// The function being called
    pub subject: FnDefId,
    // The arguments to the function, sorted by the parameters of the function
    pub args: ArgsId,
    /// Whether the function call is implicit.
    ///
    /// Implicit function calls look like `A<B>`, where as explicit function
    /// calls look like `A(B)`.
    pub is_implicit: bool,
    // @@Design: optional conditions
}
