//! Definitions related to functions.

use std::fmt::Display;

use hash_utils::{
    new_store_key,
    store::{DefaultStore, Store},
};
use typed_builder::TypedBuilder;
use utility_types::omit;

use super::{
    environment::env::{AccessToEnv, WithEnv},
    intrinsics::IntrinsicId,
    tys::Ty,
    utils::common::CommonUtils,
};
use crate::new::{args::ArgsId, params::ParamsId, symbols::Symbol, terms::TermId, tys::TyId};

/// A function type.
///
/// In their most general form, function types are written like
/// `pure? unsafe? (a_1:A_1,...,a_n:B_n) -> R(a_1,...,a_n,p_1,...,p_n)`, or
/// `impure? unsafe? <a_1:A_1,...,a_n:B_n> -> R(a_1,...,a_n,p_1,...,p_n)` for
/// implicit function types.
#[derive(Debug, Clone, Copy, TypedBuilder)]
pub struct FnTy {
    // @@MemoryUsage: use bitflags here?
    /// Whether the function is implicit.
    ///
    /// Implicit functions look like `<A> -> B`, where as explicit
    /// functions look like `(A) -> B`.
    #[builder(default = false)]
    pub implicit: bool,
    /// Whether the function is pure.
    ///
    /// A function is pure if:
    /// - it only calls *pure* functions
    /// - it does not take any mutable references as parameters or captured
    ///   variables.
    // - @@Future: It is guaranteed to terminate
    #[builder(default = false)]
    pub pure: bool,
    /// Whether the function is unsafe.
    ///
    /// Unsafe functions can only be called from within unsafe blocks. Certain
    /// functions that violate Hash's type system and/or memory rules should be
    /// marked as unsafe.
    #[builder(default = false)]
    pub is_unsafe: bool,
    /// The parameters of the function.
    pub params: ParamsId,
    /// The return type of the function.
    ///
    /// This might depend on `params` and `conditions`.
    pub return_ty: TyId,
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
#[derive(Debug, Clone, Copy, TypedBuilder)]
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
    pub implicit: bool,
    // @@Design: optional conditions
}

impl Display for WithEnv<'_, &FnTy> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.value.is_unsafe {
            write!(f, "unsafe ")?;
        }
        if self.value.pure && !self.value.implicit {
            write!(f, "pure ")?;
        }
        if !self.value.pure && self.value.implicit {
            write!(f, "impure ")?;
        }

        if self.value.implicit {
            write!(f, "<")?;
        } else {
            write!(f, "(")?;
        }

        write!(f, "{}", self.env().with(self.value.params))?;

        if self.value.implicit {
            write!(f, ">")?;
        } else {
            write!(f, ")")?;
        }

        write!(f, " -> {}", self.env().with(self.value.return_ty))?;

        Ok(())
    }
}

impl Display for WithEnv<'_, &FnDef> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if matches!(self.env().get_ty(self.value.ty.return_ty), Ty::Fn(_)) {
            if self.value.ty.is_unsafe {
                write!(f, "unsafe ")?;
            }
            if self.value.ty.pure && !self.value.ty.implicit {
                write!(f, "pure ")?;
            }
            if !self.value.ty.pure && self.value.ty.implicit {
                write!(f, "impure ")?;
            }

            if self.value.ty.implicit {
                write!(f, "<")?;
            } else {
                write!(f, "(")?;
            }

            write!(f, "{}", self.env().with(self.value.ty.params))?;

            if self.value.ty.implicit {
                write!(f, ">")?;
            } else {
                write!(f, ")")?;
            }
        } else {
            write!(f, "{}", self.env().with(&self.value.ty))?;
        };
        match self.value.body {
            FnBody::Defined(term) => write!(f, " => {}", self.env().with(term)),
            FnBody::Intrinsic(intrinsic) => {
                write!(f, " => intrinsic('{}')", self.env().with(intrinsic.0))
            }
            FnBody::Axiom => write!(f, " => axiom"),
        }
    }
}

impl Display for WithEnv<'_, FnDefId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.stores()
            .fn_def()
            .map_fast(self.value, |fn_def| write!(f, "{}", self.env().with(fn_def)))
    }
}

impl Display for WithEnv<'_, &FnCallTerm> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.env().with(self.value.subject))?;

        if self.value.implicit {
            write!(f, "<")?;
        } else {
            write!(f, "(")?;
        }

        write!(f, "{}", self.env().with(self.value.args))?;

        if self.value.implicit {
            write!(f, ">")?;
        } else {
            write!(f, ")")?;
        }

        Ok(())
    }
}
