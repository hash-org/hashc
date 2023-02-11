use hash_ast::ast::{self};
use hash_source::constant::{IntConstant, IntTy, CONSTANT_MAP};
use hash_tir::new::{
    data::{CtorDefId, CtorPat, CtorTerm, DataTy},
    environment::env::AccessToEnv,
    lits::{CharLit, FloatLit, IntLit, Lit, PrimTerm},
    pats::{Pat, PatId},
    terms::{Term, TermId},
    tys::{Ty, TyId},
    utils::common::CommonUtils,
};
use hash_utils::store::Store;
use num_bigint::BigInt;

use crate::primitives::AccessToPrimitives;

pub enum LitTy {
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    U128,
    I128,
    IBig,
    UBig,
    F32,
    F64,
    Bool,
    Char,
}

/// Utilities relating to creating and inspecting primitive types.
pub trait PrimitiveUtils: AccessToPrimitives {
    /// Get the bool constructor for the given value.
    ///
    /// Both constructors do not take arguments.
    fn get_bool_ctor(&self, value: bool) -> CtorDefId {
        let ctor_defs =
            self.stores().data_def().map_fast(self.primitives().bool(), |bool_def| bool_def.ctors);
        match ctor_defs {
            hash_tir::new::data::DataDefCtors::Defined(ctors) => {
                // Index 0 is true, 1 is false, see BootstrapOps
                let idx = if value { 0 } else { 1 };
                (ctors, idx)
            }
            hash_tir::new::data::DataDefCtors::Primitive(_) => {
                panic!("Found primitive data definition for bool")
            }
        }
    }

    /// Create a boolean term of the given value.
    fn new_bool_term(&self, value: bool) -> TermId {
        self.new_term(Term::Ctor(CtorTerm {
            ctor: self.get_bool_ctor(value),
            ctor_args: self.new_empty_args(),
            data_args: self.new_empty_args(),
        }))
    }

    /// Create a boolean pattern of the given value.
    fn bool_pat(&self, value: bool) -> PatId {
        self.new_pat(Pat::Ctor(CtorPat {
            ctor: self.get_bool_ctor(value),
            ctor_pat_args: self.new_empty_pat_args(),
            data_args: self.new_empty_args(),
            ctor_pat_args_spread: None,
        }))
    }

    /// Create a new `never` type.
    fn new_never_ty(&self) -> TyId {
        self.new_ty(DataTy { args: self.new_empty_args(), data_def: self.primitives().never() })
    }

    /// Get the given type as a literal type if possible.
    fn try_use_ty_as_lit_ty(&self, ty: TyId) -> Option<LitTy> {
        match self.get_ty(ty) {
            Ty::Data(data) => match data.data_def {
                d if d == self.primitives().i8() => Some(LitTy::I8),
                d if d == self.primitives().u8() => Some(LitTy::U8),
                d if d == self.primitives().i16() => Some(LitTy::I16),
                d if d == self.primitives().u16() => Some(LitTy::U16),
                d if d == self.primitives().i32() => Some(LitTy::I32),
                d if d == self.primitives().u32() => Some(LitTy::U32),
                d if d == self.primitives().i64() => Some(LitTy::I64),
                d if d == self.primitives().u64() => Some(LitTy::U64),
                d if d == self.primitives().u128() => Some(LitTy::U128),
                d if d == self.primitives().i128() => Some(LitTy::I128),
                d if d == self.primitives().ibig() => Some(LitTy::IBig),
                d if d == self.primitives().ubig() => Some(LitTy::UBig),
                d if d == self.primitives().f32() => Some(LitTy::F32),
                d if d == self.primitives().f64() => Some(LitTy::F64),
                d if d == self.primitives().bool() => Some(LitTy::Bool),
                d if d == self.primitives().char() => Some(LitTy::Char),
                _ => None,
            },
            _ => None,
        }
    }

    /// Get the given term as a float literal if possible.
    fn create_term_from_float_lit<L: Into<f64>>(&self, lit: L) -> TermId {
        self.new_term(Term::Prim(PrimTerm::Lit(Lit::Float(FloatLit {
            underlying: ast::FloatLit {
                kind: ast::FloatLitKind::Unsuffixed,
                value: CONSTANT_MAP.create_f64_float_constant(lit.into(), None),
            },
        }))))
    }

    /// Get the given term as a float literal if possible.
    fn try_use_term_as_float_lit<L: TryFrom<f64>>(&self, term: TermId) -> Option<L> {
        match self.get_term(term) {
            Term::Prim(PrimTerm::Lit(Lit::Float(i))) => i.value().try_into().ok(),
            _ => None,
        }
    }

    /// Get the given term as a float literal if possible.
    fn create_term_from_integer_lit<L: Into<BigInt>>(&self, lit: L, int_ty: IntTy) -> TermId {
        self.new_term(Term::Prim(PrimTerm::Lit(Lit::Int(IntLit {
            underlying: ast::IntLit {
                kind: ast::IntLitKind::Unsuffixed,
                value: CONSTANT_MAP.create_int_constant(IntConstant::from_big_int(
                    lit.into(),
                    int_ty,
                    None,
                )),
            },
        }))))
    }

    /// Get the given term as a float literal if possible.
    fn try_use_term_as_char_lit(&self, term: TermId) -> Option<char> {
        match self.get_term(term) {
            Term::Prim(PrimTerm::Lit(Lit::Char(c))) => Some(c.underlying.data),
            _ => None,
        }
    }

    /// Get the given term as a character literal if possible.
    fn create_term_from_char_lit(&self, lit: char) -> TermId {
        self.new_term(Term::Prim(PrimTerm::Lit(Lit::Char(CharLit {
            underlying: ast::CharLit { data: lit },
        }))))
    }

    /// Get the given term as an integer literal if possible.
    fn try_use_term_as_integer_lit<L: TryFrom<BigInt>>(&self, term: TermId) -> Option<L> {
        match self.get_term(term) {
            Term::Prim(PrimTerm::Lit(Lit::Int(i))) => i.value().try_into().ok(),
            _ => None,
        }
    }

    /// Get the given term as a float literal if possible.
    fn try_use_term_as_bool(&self, term: TermId) -> Option<bool> {
        match self.get_term(term) {
            Term::Ctor(CtorTerm { ctor, .. }) if ctor == self.get_bool_ctor(true) => Some(true),
            Term::Ctor(CtorTerm { ctor, .. }) if ctor == self.get_bool_ctor(false) => Some(false),
            _ => None,
        }
    }
}

impl<T: AccessToEnv + AccessToPrimitives + ?Sized> PrimitiveUtils for T {}
