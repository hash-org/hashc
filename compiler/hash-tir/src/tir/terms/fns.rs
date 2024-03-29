//! Definitions related to functions.

use std::fmt::Display;

use hash_storage::store::statics::StoreId;
use typed_builder::TypedBuilder;

use crate::{
    stores::tir_stores,
    tir::{ArgsId, ParamsId, SymbolId, TermId, Ty, TyId},
    tir_node_single_store,
};

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

/// A function definition.
///
/// Every function literal `(x) => y` is a function definition. Function
/// definitions follow the syntax of function types, but followed by `=>
/// r(a_1,...,a_n,p_1,...,p_n)`.
#[derive(Debug, Clone, Copy)]
pub struct FnDef {
    /// The symbolic name of the function, which resolves to its definition name
    /// if given by the user, by querying the data of the symbol.
    pub name: SymbolId,

    /// The underlying function type, which is partially or fully annotated on
    /// the function literal (if some aspects of the type are not given, then
    /// they will be type holes).
    pub ty: FnTy,

    /// The return value of the function.
    ///
    /// This depends on `ty.params` and `ty.conditions`.
    pub body: TermId,
}

tir_node_single_store!(FnDef);

/// A function call.
#[derive(Debug, Clone, Copy)]
pub struct CallTerm {
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

impl Display for FnTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_unsafe {
            write!(f, "unsafe ")?;
        }
        if self.pure && !self.implicit {
            write!(f, "pure ")?;
        }
        if !self.pure && self.implicit {
            write!(f, "impure ")?;
        }

        if self.implicit {
            write!(f, "<")?;
        } else {
            write!(f, "(")?;
        }

        write!(f, "{}", self.params)?;

        if self.implicit {
            write!(f, ">")?;
        } else {
            write!(f, ")")?;
        }

        write!(f, " -> {}", self.return_ty)?;

        Ok(())
    }
}

impl Display for FnDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if matches!(*self.ty.return_ty.value(), Ty::FnTy(_)) {
            if self.ty.is_unsafe {
                write!(f, "unsafe ")?;
            }
            if self.ty.pure && !self.ty.implicit {
                write!(f, "pure ")?;
            }
            if !self.ty.pure && self.ty.implicit {
                write!(f, "impure ")?;
            }

            if self.ty.implicit {
                write!(f, "<")?;
            } else {
                write!(f, "(")?;
            }

            write!(f, "{}", self.ty.params)?;

            if self.ty.implicit {
                write!(f, ">")?;
            } else {
                write!(f, ")")?;
            }
        } else {
            write!(f, "{}", &self.ty)?;
        };
        write!(f, " => {}", self.body)
    }
}

impl Display for FnDefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", *self.value())
    }
}

impl Display for CallTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.subject)?;

        if self.implicit {
            write!(f, "<")?;
        } else {
            write!(f, "(")?;
        }

        write!(f, "{}", self.args)?;

        if self.implicit {
            write!(f, ">")?;
        } else {
            write!(f, ")")?;
        }

        Ok(())
    }
}
