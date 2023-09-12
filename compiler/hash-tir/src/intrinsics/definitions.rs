use std::process;

use hash_source::identifier::Identifier;
use hash_storage::store::statics::StoreId;
use hash_utils::stream_less_writeln;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use paste::paste;

use crate::{
    building::gen::{
        args, indexed_enum_def, params, primitive_with_params, sym, term, ty, unit_term,
        Type,
    },
    data::{
        numeric_ctors, ArrayCtorInfo, CtorDefId, DataDefId,
        PrimitiveCtorInfo,
    },
    fns::FnTy,
    intrinsics::make::{IntrinsicAbilities, IsIntrinsic, IsPrimitive},
    lits::Lit,
    make_intrinsics, make_primitives,
    node::NodeOrigin,
    terms::{Term, TermId, TyId},
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum UnOp {
    /// Logical negation (!)
    Not,
    /// Bitwise negation (~)
    BitNot,
    /// Negation (-)
    Neg,
}

/// A boolean-valued binary operator.
#[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum BoolBinOp {
    /// '=='
    EqEq,
    /// '!='
    NotEq,
    /// '>'
    Gt,
    /// '>='
    GtEq,
    /// '<'
    Lt,
    /// '<='
    LtEq,
}

/// This represents the result of a short-circuiting binary operators
/// that can occur as intrinsics.
#[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum ShortCircuitBinOp {
    /// '||'
    Or,
    /// '&&'
    And,
}

/// A binary operator whose result is the same type as its arguments.
#[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
pub enum EndoBinOp {
    /// '|'
    BitOr,
    /// '&'
    BitAnd,
    /// '^'
    BitXor,
    /// '**'
    Exp,
    /// '>>'
    Shr,
    /// '<<'
    Shl,
    /// '+'
    Add,
    /// '-'
    Sub,
    /// '*'
    Mul,
    /// '/'
    Div,
    /// '%'
    Mod,
}

make_intrinsics! {
    size_of := (T: Type()) -> usize_gen_ty() => |env| {
        // @@Todo: actually return the size
        Ok(None)
    };

    eval := (T: Type(), a: ty(T)) -> ty(T) => |env| {
        env.normalise_term(a)
    };

    transmute := (T: Type(), U: Type(), a: ty(T)) -> ty(U) => |env| {
        // Warning: highly unsafe!
        Ok(Some(a))
    };

    cast := (T: Type(), U: Type(), a: ty(T)) -> ty(T) => |env| {
        // @@Todo: actually cast
        Ok(None)
    };

    abort := () -> never_gen_ty() => |env| {
        process::exit(1)
    };

    panic := (message: str_gen_ty()) -> never_gen_ty() => |env| {
        stream_less_writeln!("{}", message);
        process::exit(1)
    };

    user_error := (message: str_gen_ty()) -> never_gen_ty() => |env| {
        if let Term::Lit(lit) = *message.value() && let Lit::Str(str_lit) = *lit.value() {
            Err(str_lit.value().to_string())
        } else {
            Err("`user_error` expects a string literal as argument".to_string())
        }
    };

    debug_print := (T: Type(), a: ty(T)) -> never_gen_ty() => |env| {
        stream_less_writeln!("{}", a);
        Ok(Some(unit_term()))
    };

    // Unary operations
    un_op := (T: Type(), op: u8_gen_ty(), a: ty(T)) -> ty(T) => |env| {
        Ok(None)
    };
}

make_primitives! {
    bool := data (true: bool, false: bool);

    never := data ();

    Option := data <(T: Type())> (
        None: Option<(ty(T))>,
        Some(x: ty(T)): Option<(ty(T))>
    );

    Result := data <(T: Type(), E: Type())> (
        Ok(value: ty(T)): Result<(ty(T), ty(E))>,
        Err(error: ty(E)): Result<(ty(T), ty(E))>
    );

    Equal := data <(T: Type(), a: ty(T), b: ty(T))> (
        Refl(x: ty(T)): Equal<(ty(T), term(x), term(x))>
    );

    str := primitive (PrimitiveCtorInfo::Str);

    char := primitive (PrimitiveCtorInfo::Char);

    List := primitive <(T: Type())> (PrimitiveCtorInfo::Array(ArrayCtorInfo {
        element_ty: ty(T),
        length: None
    }));

    Array := primitive <(T: Type(), n: usize_gen_ty())> (
        PrimitiveCtorInfo::Array(ArrayCtorInfo {
            element_ty: ty(T),
            length: Some(term(n))
        })
    );

    i8 := primitive (numeric_ctors(8, true, false));
    i16 := primitive (numeric_ctors(16, true, false));
    i32 := primitive (numeric_ctors(32, true, false));
    i64 := primitive (numeric_ctors(64, true, false));
    i128 := primitive (numeric_ctors(128, true, false));
    isize := primitive (numeric_ctors(64, true, false));
    ibig := primitive (numeric_ctors(0, true, false));

    u8 := primitive (numeric_ctors(8, false, false));
    u16 := primitive (numeric_ctors(16, false, false));
    u32 := primitive (numeric_ctors(32, false, false));
    u64 := primitive (numeric_ctors(64, false, false));
    u128 := primitive (numeric_ctors(128, false, false));
    ubig := primitive (numeric_ctors(0, false, false));
    usize := primitive (numeric_ctors(64, false, false));

    f32 := primitive (numeric_ctors(32, false, true));
    f64 := primitive (numeric_ctors(64, false, true));
}
