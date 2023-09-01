use hash_ast::ast::{self};
use hash_source::constant::{
    FloatConstant, FloatConstantValue, FloatTy, IntConstant, IntConstantValue, IntTy,
    InternedFloat, InternedInt, SIntTy, UIntTy,
};
use hash_storage::store::statics::{SequenceStoreValue, StoreId};
use hash_tir::{
    args::{Arg, PatArg},
    data::{ArrayCtorInfo, CtorDefId, CtorPat, CtorTerm, DataDefCtors, DataTy, PrimitiveCtorInfo},
    environment::env::AccessToEnv,
    lits::{CharLit, Lit},
    node::{Node, NodeOrigin},
    pats::{Pat, PatId},
    primitives::primitives,
    refs::{RefKind, RefTy},
    terms::{Term, TermId},
    tys::{Ty, TyId},
};
use num_bigint::BigInt;

/// Primitive literal types.
///
/// @@Future: maybe use `IntTy` and `FloatTy` for integer and float types
/// instead?
#[derive(Clone, Copy)]
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

impl LitTy {
    /// Check if the type is an integer type.
    pub fn is_int(&self) -> bool {
        matches!(
            self,
            LitTy::I8
                | LitTy::U8
                | LitTy::I16
                | LitTy::U16
                | LitTy::I32
                | LitTy::U32
                | LitTy::I64
                | LitTy::U64
                | LitTy::U128
                | LitTy::I128
                | LitTy::IBig
                | LitTy::UBig
        )
    }
}

impl From<LitTy> for IntTy {
    fn from(value: LitTy) -> Self {
        match value {
            LitTy::U8 => IntTy::UInt(UIntTy::U8),
            LitTy::U16 => IntTy::UInt(UIntTy::U16),
            LitTy::U32 => IntTy::UInt(UIntTy::U32),
            LitTy::U64 => IntTy::UInt(UIntTy::U64),
            LitTy::U128 => IntTy::UInt(UIntTy::U128),
            LitTy::UBig => IntTy::UInt(UIntTy::UBig),
            LitTy::I8 => IntTy::Int(SIntTy::I8),
            LitTy::I16 => IntTy::Int(SIntTy::I16),
            LitTy::I32 => IntTy::Int(SIntTy::I32),
            LitTy::I64 => IntTy::Int(SIntTy::I64),
            LitTy::I128 => IntTy::Int(SIntTy::I128),
            LitTy::IBig => IntTy::Int(SIntTy::IBig),
            _ => unreachable!(),
        }
    }
}

impl From<LitTy> for FloatTy {
    fn from(value: LitTy) -> Self {
        match value {
            LitTy::F32 => FloatTy::F32,
            LitTy::F64 => FloatTy::F64,
            _ => unreachable!(),
        }
    }
}

/// Utilities relating to creating and inspecting primitive types.
pub trait PrimitiveUtils: AccessToEnv {
    /// Get the bool constructor for the given value.
    ///
    /// Both constructors do not take arguments.
    fn get_bool_ctor(&self, value: bool) -> CtorDefId {
        let ctor_defs = primitives().bool().borrow().ctors;
        match ctor_defs {
            hash_tir::data::DataDefCtors::Defined(ctors) => {
                // Index 0 is true, 1 is false, see BootstrapOps
                let idx = if value { 0 } else { 1 };
                CtorDefId(ctors.elements(), idx)
            }
            hash_tir::data::DataDefCtors::Primitive(_) => {
                panic!("Found primitive data definition for bool")
            }
        }
    }

    /// Create a boolean term of the given value.
    fn new_bool_term(&self, value: bool) -> TermId {
        Node::create_at(
            Term::Ctor(CtorTerm {
                ctor: self.get_bool_ctor(value),
                ctor_args: Node::create_at(Node::<Arg>::empty_seq(), NodeOrigin::Generated),
                data_args: Node::create_at(Node::<Arg>::empty_seq(), NodeOrigin::Generated),
            }),
            NodeOrigin::Generated,
        )
    }

    /// Create a boolean pattern of the given value.
    fn new_bool_pat(&self, value: bool) -> PatId {
        Node::create_at(
            Pat::Ctor(CtorPat {
                ctor: self.get_bool_ctor(value),
                ctor_pat_args: Node::create_at(Node::<PatArg>::empty_seq(), NodeOrigin::Generated),
                data_args: Node::create_at(Node::<Arg>::empty_seq(), NodeOrigin::Generated),
                ctor_pat_args_spread: None,
            }),
            NodeOrigin::Generated,
        )
    }

    /// Create a new `never` type.
    fn new_never_ty(&self) -> TyId {
        Ty::from(DataTy {
            args: Node::create_at(Node::<Arg>::empty_seq(), NodeOrigin::Generated),
            data_def: primitives().never(),
        })
    }

    /// Create a new reference type.
    fn new_ref_ty(&self, ty: TyId, kind: RefKind, mutable: bool) -> TyId {
        Ty::from(RefTy { ty, kind, mutable })
    }

    /// Get the given type as a primitive integer type if possible.
    fn try_use_ty_as_int_ty(&self, ty: TyId) -> Option<IntTy> {
        match *ty.value() {
            Ty::Data(data) => match data.data_def {
                d if d == primitives().i8() => Some(IntTy::Int(SIntTy::I8)),
                d if d == primitives().u8() => Some(IntTy::UInt(UIntTy::U8)),
                d if d == primitives().i16() => Some(IntTy::Int(SIntTy::I16)),
                d if d == primitives().u16() => Some(IntTy::UInt(UIntTy::U16)),
                d if d == primitives().i32() => Some(IntTy::Int(SIntTy::I32)),
                d if d == primitives().u32() => Some(IntTy::UInt(UIntTy::U32)),
                d if d == primitives().i64() => Some(IntTy::Int(SIntTy::I64)),
                d if d == primitives().u64() => Some(IntTy::UInt(UIntTy::U64)),
                d if d == primitives().i128() => Some(IntTy::Int(SIntTy::I128)),
                d if d == primitives().u128() => Some(IntTy::UInt(UIntTy::U128)),
                d if d == primitives().ibig() => Some(IntTy::Int(SIntTy::IBig)),
                d if d == primitives().ubig() => Some(IntTy::UInt(UIntTy::UBig)),
                d if d == primitives().isize() => Some(IntTy::Int(SIntTy::ISize)),
                d if d == primitives().usize() => Some(IntTy::UInt(UIntTy::USize)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Get the given type as a primitive float type if possible.
    fn try_use_ty_as_float_ty(&self, ty: TyId) -> Option<FloatTy> {
        match *ty.value() {
            Ty::Data(data) => match data.data_def {
                d if d == primitives().f32() => Some(FloatTy::F32),
                d if d == primitives().f64() => Some(FloatTy::F64),
                _ => None,
            },
            _ => None,
        }
    }

    /// Get the given type as a primitive array type if possible.
    fn try_use_ty_as_array_ty(&self, ty: TyId) -> Option<ArrayCtorInfo> {
        match *ty.value() {
            Ty::Data(data) => match data.data_def.borrow().ctors {
                DataDefCtors::Primitive(PrimitiveCtorInfo::Array(array)) => Some(array),
                _ => None,
            },
            _ => None,
        }
    }

    /// Get the given type as a literal type if possible.
    fn try_use_ty_as_lit_ty(&self, ty: TyId) -> Option<LitTy> {
        match *ty.value() {
            Ty::Data(data) => match data.data_def {
                d if d == primitives().i8() => Some(LitTy::I8),
                d if d == primitives().u8() => Some(LitTy::U8),
                d if d == primitives().i16() => Some(LitTy::I16),
                d if d == primitives().u16() => Some(LitTy::U16),
                d if d == primitives().i32() => Some(LitTy::I32),
                d if d == primitives().u32() => Some(LitTy::U32),
                d if d == primitives().i64() => Some(LitTy::I64),
                d if d == primitives().u64() => Some(LitTy::U64),
                d if d == primitives().u128() => Some(LitTy::U128),
                d if d == primitives().i128() => Some(LitTy::I128),
                d if d == primitives().ibig() => Some(LitTy::IBig),
                d if d == primitives().ubig() => Some(LitTy::UBig),
                d if d == primitives().f32() => Some(LitTy::F32),
                d if d == primitives().f64() => Some(LitTy::F64),
                d if d == primitives().bool() => Some(LitTy::Bool),
                d if d == primitives().char() => Some(LitTy::Char),
                d if d == primitives().isize() => match self.target().pointer_bit_width {
                    8 => Some(LitTy::I8),
                    16 => Some(LitTy::I16),
                    32 => Some(LitTy::I32),
                    64 => Some(LitTy::I64),
                    _ => unreachable!(),
                },
                d if d == primitives().usize() => match self.target().pointer_bit_width {
                    8 => Some(LitTy::U8),
                    16 => Some(LitTy::U16),
                    32 => Some(LitTy::U32),
                    64 => Some(LitTy::U64),
                    _ => unreachable!(),
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// Get the given term as a float literal if possible.
    fn create_term_from_float_lit<L: Into<FloatConstantValue>>(&self, lit: L) -> TermId {
        Node::create_at(
            Term::Lit(Lit::Float(InternedFloat::create(FloatConstant::new(lit.into(), None)).into())),
            NodeOrigin::Generated,
        )
    }

    /// Get the given term as a float literal if possible.
    fn try_use_term_as_float_lit<L: From<f64>>(&self, term: TermId) -> Option<L> {
        match *term.value() {
            Term::Lit(Lit::Float(i)) => i.value().try_into().ok(),
            _ => None,
        }
    }

    /// Get the given term as a float literal if possible.
    fn create_term_from_integer_lit<L: Into<IntConstantValue>>(&self, lit: L) -> TermId {
        Node::create_at(
            Term::Lit(Lit::Int(InternedInt::create(IntConstant::new(lit.into(), None)).into(),)),
            NodeOrigin::Generated,
        )
    }

    /// Get the given term as a character literal if possible.
    fn try_use_term_as_char_lit(&self, term: TermId) -> Option<char> {
        match *term.value() {
            Term::Lit(Lit::Char(c)) => Some(c.underlying.data),
            _ => None,
        }
    }

    /// Get the given term as a character literal if possible.
    fn create_term_from_char_lit(&self, lit: char) -> TermId {
        Node::create_at(
            Term::Lit(Lit::Char(CharLit { underlying: ast::CharLit { data: lit } })),
            NodeOrigin::Generated,
        )
    }

    /// Get the given term as an integer literal if possible.
    fn try_use_term_as_integer_lit<L: TryFrom<BigInt>>(&self, term: TermId) -> Option<L> {
        match *term.value() {
            Term::Lit(Lit::Int(i)) => i.value().try_into().ok(),
            Term::Var(sym) => self
                .context()
                .try_get_decl_value(sym)
                .and_then(|result| self.try_use_term_as_integer_lit(result)),

            _ => None,
        }
    }

    /// Get the given term as a float literal if possible.
    fn try_use_term_as_bool(&self, term: TermId) -> Option<bool> {
        match *term.value() {
            Term::Ctor(CtorTerm { ctor, .. }) if ctor == self.get_bool_ctor(true) => Some(true),
            Term::Ctor(CtorTerm { ctor, .. }) if ctor == self.get_bool_ctor(false) => Some(false),
            _ => None,
        }
    }

    /// Function used to compute the maximum value of a numeric pattern. This is
    /// useful when normalising numeric patterns in various contexts where
    /// we need to know the maximum value of a pattern. Specifically, if a
    /// range pattern is provided with an open end, we need to know the
    /// maximum value of the pattern in order to know what the open end
    /// should be.
    fn numeric_max_val_of_lit(&self, ty: TyId) -> Option<u128> {
        match self.try_use_ty_as_lit_ty(ty)? {
            // There is no maximum value for big integers.
            LitTy::UBig | LitTy::IBig => None,
            ty if ty.is_int() => {
                let int_ty: IntTy = ty.into();
                Some(int_ty.numeric_max(self.target().ptr_size()))
            }
            LitTy::Char => Some(std::char::MAX as u128),
            // @@Todo: if we implement float ranges, we would need to return `Infinity` here
            _ => None,
        }
    }

    /// Function used to compute the minimum value of a numeric pattern. This is
    /// a mirror of the [`Self::numeric_max_val`] function.
    fn numeric_min_val_of_lit(&self, ty: TyId) -> Option<u128> {
        match self.try_use_ty_as_lit_ty(ty)? {
            // There is no minimum value for big integers.
            LitTy::UBig | LitTy::IBig => None,
            ty if ty.is_int() => {
                let int_ty: IntTy = ty.into();
                Some(int_ty.numeric_min(self.target().ptr_size()))
            }
            LitTy::Char => Some(0),
            // @@Todo: if we implement float ranges, we would need to return `-Infinity` here
            _ => None,
        }
    }
}

impl<T: AccessToEnv + ?Sized> PrimitiveUtils for T {}
