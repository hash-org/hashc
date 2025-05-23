//! Various utility functions for working with intrinsics and primitives.

use derive_more::From;
use hash_const_eval::Const;
use hash_source::constant::{FloatTy, IntTy, SIntTy, UIntTy};
use hash_storage::store::statics::{SequenceStoreValue, StoreId};
use hash_target::{HasTarget, data_layout::HasDataLayout, primitives::BigIntTy};

use super::{
    definitions::{BoolCtor, Primitive},
    make::IsPrimitiveCtor,
};
use crate::{
    context::HasContext,
    tir::{
        Arg, ArrayCtorInfo, CtorDefId, CtorPat, CtorTerm, DataDefCtors, Lit, Node, NodeOrigin, Pat,
        PatArg, PatId, PrimitiveCtorInfo, Term, TermId, Ty, TyId,
    },
};

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
            LitTy::I8 => IntTy::Int(SIntTy::I8),
            LitTy::I16 => IntTy::Int(SIntTy::I16),
            LitTy::I32 => IntTy::Int(SIntTy::I32),
            LitTy::I64 => IntTy::Int(SIntTy::I64),
            LitTy::I128 => IntTy::Int(SIntTy::I128),
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

/// Get the bool constructor for the given value.
///
/// Both constructors do not take arguments.
pub fn get_bool_ctor(value: bool) -> CtorDefId {
    if value { BoolCtor::True.def() } else { BoolCtor::False.def() }
}

/// Check if the given term is the `true` constructor.
pub fn is_true_bool_ctor(term: TermId) -> bool {
    match *term.value() {
        Term::Ctor(ctor_term) => ctor_term.ctor == get_bool_ctor(true),
        _ => false,
    }
}

/// Create a boolean term of the given value.
pub fn bool_term(value: bool, origin: NodeOrigin) -> TermId {
    Node::create_at(
        Term::Ctor(CtorTerm {
            ctor: get_bool_ctor(value),
            ctor_args: Node::create_at(Node::<Arg>::empty_seq(), origin),
            data_args: Node::create_at(Node::<Arg>::empty_seq(), origin),
        }),
        origin,
    )
}

/// Create a boolean pattern of the given value.
pub fn bool_pat(value: bool, origin: NodeOrigin) -> PatId {
    Node::create_at(
        Pat::Ctor(CtorPat {
            ctor: get_bool_ctor(value),
            ctor_pat_args: Node::create_at(Node::<PatArg>::empty_seq(), origin),
            data_args: Node::create_at(Node::<Arg>::empty_seq(), origin),
            ctor_pat_args_spread: None,
        }),
        origin,
    )
}

/// Get the given type as a primitive integer type if possible.
pub fn try_use_ty_as_int_ty(ty: TyId) -> Option<IntTy> {
    match *ty.value() {
        Ty::DataTy(data) => match Primitive::try_from_def(data.data_def) {
            Some(Primitive::I8) => Some(IntTy::Int(SIntTy::I8)),
            Some(Primitive::U8) => Some(IntTy::UInt(UIntTy::U8)),
            Some(Primitive::I16) => Some(IntTy::Int(SIntTy::I16)),
            Some(Primitive::U16) => Some(IntTy::UInt(UIntTy::U16)),
            Some(Primitive::I32) => Some(IntTy::Int(SIntTy::I32)),
            Some(Primitive::U32) => Some(IntTy::UInt(UIntTy::U32)),
            Some(Primitive::I64) => Some(IntTy::Int(SIntTy::I64)),
            Some(Primitive::U64) => Some(IntTy::UInt(UIntTy::U64)),
            Some(Primitive::I128) => Some(IntTy::Int(SIntTy::I128)),
            Some(Primitive::U128) => Some(IntTy::UInt(UIntTy::U128)),
            Some(Primitive::Ibig) => Some(IntTy::Big(BigIntTy::IBig)),
            Some(Primitive::Ubig) => Some(IntTy::Big(BigIntTy::UBig)),
            Some(Primitive::Isize) => Some(IntTy::Int(SIntTy::ISize)),
            Some(Primitive::Usize) => Some(IntTy::UInt(UIntTy::USize)),
            _ => None,
        },
        _ => None,
    }
}

/// Get the given type as a primitive float type if possible.
pub fn try_use_ty_as_float_ty(ty: TyId) -> Option<FloatTy> {
    match *ty.value() {
        Ty::DataTy(data) => match Primitive::try_from_def(data.data_def) {
            Some(Primitive::F32) => Some(FloatTy::F32),
            Some(Primitive::F64) => Some(FloatTy::F64),
            _ => None,
        },
        _ => None,
    }
}

/// Get the given type as a primitive array type if possible.
pub fn try_use_ty_as_array_ty(ty: TyId) -> Option<ArrayCtorInfo> {
    match *ty.value() {
        Ty::DataTy(data) => match data.data_def.borrow().ctors {
            DataDefCtors::Primitive(PrimitiveCtorInfo::Array(array)) => Some(array),
            _ => None,
        },
        _ => None,
    }
}

/// Get the given type as a literal type if possible.
pub fn try_use_ty_as_lit_ty<T: HasTarget>(env: &T, ty: TyId) -> Option<LitTy> {
    match *ty.value() {
        Ty::DataTy(data) => match Primitive::try_from_def(data.data_def) {
            Some(Primitive::I8) => Some(LitTy::I8),
            Some(Primitive::U8) => Some(LitTy::U8),
            Some(Primitive::I16) => Some(LitTy::I16),
            Some(Primitive::U16) => Some(LitTy::U16),
            Some(Primitive::I32) => Some(LitTy::I32),
            Some(Primitive::U32) => Some(LitTy::U32),
            Some(Primitive::I64) => Some(LitTy::I64),
            Some(Primitive::U64) => Some(LitTy::U64),
            Some(Primitive::U128) => Some(LitTy::U128),
            Some(Primitive::I128) => Some(LitTy::I128),
            Some(Primitive::F32) => Some(LitTy::F32),
            Some(Primitive::F64) => Some(LitTy::F64),
            Some(Primitive::Bool) => Some(LitTy::Bool),
            Some(Primitive::Char) => Some(LitTy::Char),
            Some(Primitive::Isize) => match env.target().pointer_bit_width {
                8 => Some(LitTy::I8),
                16 => Some(LitTy::I16),
                32 => Some(LitTy::I32),
                64 => Some(LitTy::I64),
                _ => unreachable!(),
            },
            Some(Primitive::Usize) => match env.target().pointer_bit_width {
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

/// Helper struct to represent a float value which can be freely converted
/// between `f32` and `f64`.
#[derive(Clone, Copy, PartialEq, PartialOrd, From)]
pub enum Float {
    F32(f32),
    F64(f64),
}

impl From<Float> for f32 {
    fn from(value: Float) -> Self {
        match value {
            Float::F32(value) => value,
            Float::F64(value) => value as f32,
        }
    }
}

impl From<Float> for f64 {
    fn from(value: Float) -> Self {
        match value {
            Float::F32(value) => value as f64,
            Float::F64(value) => value,
        }
    }
}

/// Create a term from the given usize integer literal.
pub fn create_term_from_usize_lit<C: HasDataLayout>(
    ctx: &C,
    lit: usize,
    origin: NodeOrigin,
) -> TermId {
    let lit = Const::usize(lit.try_into().unwrap(), ctx);
    Node::create_at(Term::Lit(Node::create_at(Lit::Const(lit), origin)), origin)
}

/// Create a term from the given integer literal.
pub fn create_term_from_const<L: Into<Const>>(lit: L, origin: NodeOrigin) -> TermId {
    let lit = Lit::Const(lit.into());
    Node::create_at(Term::Lit(Node::create_at(lit, origin)), origin)
}

/// Get the given term as a character literal if possible.
pub fn try_use_term_as_char_lit(term: TermId) -> Option<char> {
    match *term.value() {
        Term::Lit(lit) => match *lit.value() {
            Lit::Const(c) => c.as_scalar().try_into().ok(),
            _ => None,
        },
        _ => None,
    }
}

/// Try to use a term as an integer literal, but returning the [IntConstant]
/// instead of specifically casting to a type.
pub fn try_use_term_as_const<T: HasContext + HasTarget>(env: &T, term: TermId) -> Option<Const> {
    match *term.value() {
        Term::Lit(lit) => match *lit.value() {
            Lit::Const(val) => Some(val),
            _ => None,
        },
        Term::Var(var) => env
            .context()
            .try_get_decl_value(var.symbol)
            .and_then(|result| try_use_term_as_const(env, result)),
        _ => None,
    }
}

/// Get the given term as an integer literal if possible.
pub fn try_use_term_as_integer_lit<T: HasContext + HasTarget, L: for<'a> TryFrom<&'a Const>>(
    env: &T,
    term: TermId,
) -> Option<L> {
    try_use_term_as_const(env, term).and_then(|val| (&val).try_into().ok())
}

/// Special case for machine sized integers, we have to first normalise
/// the type based on the compilation [Target] and then we can convert
/// the [Term] into that value.
pub fn try_use_term_as_machine_integer<T: HasContext + HasTarget>(
    env: &T,
    term: TermId,
) -> Option<usize> {
    try_use_term_as_const(env, term).and_then(|val| val.try_to_target_usize(env))
}

/// Get the given term as a float literal if possible.
pub fn try_use_term_as_bool(term: TermId) -> Option<bool> {
    match *term.value() {
        Term::Ctor(CtorTerm { ctor, .. }) if ctor == get_bool_ctor(true) => Some(true),
        Term::Ctor(CtorTerm { ctor, .. }) if ctor == get_bool_ctor(false) => Some(false),
        _ => None,
    }
}

/// Function used to compute the maximum value of a numeric pattern. This is
/// useful when normalising numeric patterns in various contexts where
/// we need to know the maximum value of a pattern. Specifically, if a
/// range pattern is provided with an open end, we need to know the
/// maximum value of the pattern in order to know what the open end
/// should be.
pub fn numeric_max_val_of_lit<T: HasTarget>(env: &T, ty: TyId) -> Option<u128> {
    match try_use_ty_as_lit_ty(env, ty)? {
        // There is no maximum value for big integers.
        ty if ty.is_int() => {
            let int_ty: IntTy = ty.into();
            Some(int_ty.numeric_max(env.target().ptr_size()))
        }
        LitTy::Char => Some(std::char::MAX as u128),
        // @@Todo: if we implement float ranges, we would need to return `Infinity` here
        _ => None,
    }
}

/// Function used to compute the minimum value of a numeric pattern. This is
/// a mirror of the [`Self::numeric_max_val`] function.
pub fn numeric_min_val_of_lit<T: HasTarget>(env: &T, ty: TyId) -> Option<u128> {
    match try_use_ty_as_lit_ty(env, ty)? {
        // There is no minimum value for big integers.
        ty if ty.is_int() => {
            let int_ty: IntTy = ty.into();
            Some(int_ty.numeric_min(env.target().ptr_size()))
        }
        LitTy::Char => Some(0),
        // @@Todo: if we implement float ranges, we would need to return `-Infinity` here
        _ => None,
    }
}
