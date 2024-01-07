/// Declaratively defines all the primitives and intrinsics of the language at
/// the TIR level.
use std::process;

use hash_const_eval::{
    eval::ConstFolder,
    op::{BinOp, UnOp},
};
use hash_source::identifier::Identifier;
use hash_storage::store::statics::StoreId;
use hash_utils::stream_less_writeln;
use paste::paste;

use crate::{
    building::gen::{
        args, indexed_enum_def, params, primitive_with_params, ref_ty, sym, term, ty, unit_term,
        Type,
    },
    intrinsics::{
        make::{IntrinsicAbilities, IsIntrinsic, IsPrimitive},
        utils::{try_use_term_as_const, try_use_term_as_integer_lit},
    },
    make_intrinsics, make_primitives,
    tir::{
        numeric_ctors, ArrayCtorInfo, CtorDefId, DataDefId, FnTy, Lit, ModMember, NodeOrigin,
        NumericCtorFlags, PrimitiveCtorInfo, RefKind, Term, TermId, TyId,
    },
};

// #[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
// #[repr(u8)]
// pub enum UnOp {
//     /// Logical negation (!)
//     Not,
//     /// Bitwise negation (~)
//     BitNot,
//     /// Negation (-)
//     Neg,
// }

// /// A boolean-valued binary operator.
// #[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
// #[repr(u8)]
// pub enum CondBinOp {
//     /// '=='
//     EqEq,
//     /// '!='
//     NotEq,
//     /// '>'
//     Gt,
//     /// '>='
//     GtEq,
//     /// '<'
//     Lt,
//     /// '<='
//     LtEq,
// }

// /// This represents the result of a short-circuiting binary operators
// /// that can occur as intrinsics.
// #[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
// #[repr(u8)]
// pub enum ShortCircuitingBoolOp {
//     /// '||'
//     Or,
//     /// '&&'
//     And,
// }

// /// A binary operator whose result is the same type as its arguments.
// #[derive(Copy, Clone, Debug, PartialEq, Eq, IntoPrimitive, TryFromPrimitive)]
// #[repr(u8)]
// pub enum BinOp {
//     /// '|'
//     BitOr,
//     /// '&'
//     BitAnd,
//     /// '^'
//     BitXor,
//     /// '**'
//     Exp,
//     /// '>>'
//     Shr,
//     /// '<<'
//     Shl,
//     /// '+'
//     Add,
//     /// '-'
//     Sub,
//     /// '*'
//     Mul,
//     /// '/'
//     Div,
//     /// '%'
//     Mod,
// }

make_intrinsics! {
    size_of := (T: Type()) -> usize_gen_ty() => |env| {
        // @@Todo: actually return the size.
        Ok(None)
    };

    align_of := (T: Type()) -> usize_gen_ty() => |env| {
        // @@Todo: actually return the alignment.
        Ok(None)
    };

    ptr_offset := (bytes: ref_ty(u8_gen_ty(), RefKind::Raw, false), len: usize_gen_ty()) -> ref_ty(u8_gen_ty(), RefKind::Raw, false) => |env| {
        // @@Todo: actually calculate the offset.
        Ok(None)
    };

    memcpy := (dest: ref_ty(u8_gen_ty(), RefKind::Raw, false), src: ref_ty(u8_gen_ty(), RefKind::Raw, false), len: usize_gen_ty()) -> ref_ty(u8_gen_ty(), RefKind::Raw, false) => |env| {
        // @@Todo: actually perform memcpy (Probably on an `AllocId`).
        Ok(None)
    };

    memcmp := (a: ref_ty(u8_gen_ty(), RefKind::Raw, false), b: ref_ty(u8_gen_ty(), RefKind::Raw, false), len: usize_gen_ty()) -> i32_gen_ty() => |env| {
        // @@Todo: actually perform memcmp (Probably on an `AllocId`).
        Ok(None)
    };

    eval := (T: Type(), a: ty(T)) -> ty(T) => |env| {
        env.normalise_term(a)
    };

    transmute := (T: Type(), U: Type(), a: ty(T)) -> ty(U) => |env| {
        // Warning: highly unsafe!
        Ok(Some(a))
    };

    cast := (T: Type(), U: Type(), a: ty(T)) -> ty(U) => |env| {
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
        if let Term::Lit(lit) = *message.value() && let Lit::Const(value) = *lit.value() {
            Err(value.as_alloc().coerce_into_str())
        } else {
            Err("`user_error` expects a string literal as argument".to_string())
        }
    };

    debug_print := (T: Type(), a: ty(T)) -> never_gen_ty() => |env| {
        stream_less_writeln!("{}", a);
        Ok(Some(unit_term()))
    };

    // Condition binary operations (i.e. returning booleans)
    cond_bin_op := (T: Type(), op: u8_gen_ty(), a: ty(T), b: ty(T)) -> bool_gen_ty() => |env| {
        const INVALID_OP: &str = "Invalid cond-binary operation parameters";

        // Parse the operator.
        let parsed_op = BinOp::try_from(
            try_use_term_as_integer_lit::<_, u8>(&env, op).ok_or(INVALID_OP)?,
        )
        .map_err(|_| INVALID_OP)?;

        let lhs_expr = try_use_term_as_const(&env, a);
        let rhs_expr = try_use_term_as_const(&env, b);

        // Use the constant evaluator to perform the operation.
        let eval = ConstFolder::new(env.layout_computer());
        Ok(None)

        // // Valid operations on big-ints
        // macro_rules! operate_bool {
        //     ($op:expr, $lhs:expr, $rhs:expr) => {
        //         match $op {
        //             CondBinOp::EqEq => $lhs == $rhs,
        //             CondBinOp::NotEq => $lhs != $rhs,
        //             _ => return Err(INVALID_OP.to_string()),
        //         }
        //     };
        // }

        // // Valid operations on floats
        // macro_rules! operate_float {
        //     ($op:expr, $lhs:expr, $rhs:expr) => {
        //         match $op {
        //             CondBinOp::EqEq => $lhs == $rhs,
        //             CondBinOp::NotEq => $lhs != $rhs,
        //             CondBinOp::Gt => $lhs > $rhs,
        //             CondBinOp::GtEq => $lhs >= $rhs,
        //             CondBinOp::Lt => $lhs < $rhs,
        //             CondBinOp::LtEq => $lhs <= $rhs,
        //         }
        //     };
        // }

        // // Valid operations on integers
        // macro_rules! operate_int {
        //     ($op:expr, $lhs:expr, $rhs:expr) => {
        //         match $op {
        //             CondBinOp::EqEq => $lhs == $rhs,
        //             CondBinOp::NotEq => $lhs != $rhs,
        //             CondBinOp::Gt => $lhs > $rhs,
        //             CondBinOp::GtEq => $lhs >= $rhs,
        //             CondBinOp::Lt => $lhs < $rhs,
        //             CondBinOp::LtEq => $lhs <= $rhs,
        //         }
        //     };
        // }

        // // Valid operations on characters
        // macro_rules! operate_char {
        //     ($op:expr, $lhs:expr, $rhs:expr) => {
        //         match $op {
        //             CondBinOp::EqEq => $lhs == $rhs,
        //             CondBinOp::NotEq => $lhs != $rhs,
        //             CondBinOp::Gt => $lhs > $rhs,
        //             CondBinOp::GtEq => $lhs >= $rhs,
        //             CondBinOp::Lt => $lhs < $rhs,
        //             CondBinOp::LtEq => $lhs <= $rhs,
        //         }
        //     };
        // }

        // macro_rules! handle_integer {
        //     ($rust_ty:ty) => {{
        //         match (try_use_term_as_integer_lit::<_, $rust_ty>(&env, a), try_use_term_as_integer_lit::<_, $rust_ty>(&env, b)) {
        //             (Some(lhs), Some(rhs)) => {
        //                 Ok(Some(bool_term(operate_int!(parsed_op, lhs, rhs), a.origin().computed())))
        //             },
        //             _ => Ok(None),
        //         }
        //     }};
        // }

        // macro_rules! handle_float {
        //     ($rust_ty:ty) => {{
        //         match (try_use_term_as_float_lit::<$rust_ty>(a), try_use_term_as_float_lit::<$rust_ty>(b)) {
        //             (Some(lhs), Some(rhs)) => {
        //                 Ok(Some(bool_term(operate_float!(parsed_op, lhs, rhs), a.origin().computed())))
        //             },
        //             _ => Ok(None),
        //         }
        //     }};
        // }

        // // Handle each `T` parameter:
        // match try_use_ty_as_lit_ty(&env, T) {
        //     Some(lit_ty) => match lit_ty {
        //         LitTy::U8 => handle_integer!(u8),
        //         LitTy::U16 => handle_integer!(u16),
        //         LitTy::U32 => handle_integer!(u32),
        //         LitTy::U64 => handle_integer!(u64),
        //         LitTy::U128 => handle_integer!(u128),
        //         LitTy::I8 => handle_integer!(i8),
        //         LitTy::I16 => handle_integer!(i16),
        //         LitTy::I32 => handle_integer!(i32),
        //         LitTy::I64 => handle_integer!(i64),
        //         LitTy::I128 => handle_integer!(i128),
        //         LitTy::F32 => handle_float!(f32),
        //         LitTy::F64 =>  handle_float!(f64),
        //         LitTy::Bool => {
        //             match (try_use_term_as_bool(a), try_use_term_as_bool(b)) {
        //                 (Some(lhs), Some(rhs)) => {
        //                     Ok(Some(bool_term(operate_bool!(parsed_op, lhs, rhs), a.origin().computed())))
        //                 },
        //                 _ => Ok(None),
        //             }
        //         }
        //         LitTy::Char => {
        //             match (try_use_term_as_char_lit(a), try_use_term_as_char_lit(b)) {
        //                 (Some(lhs), Some(rhs)) => {
        //                     Ok(Some(bool_term(operate_char!(parsed_op, lhs, rhs), a.origin().computed())))
        //                 },
        //                 _ => Ok(None),
        //             }
        //         }
        //     },
        //     None => Err(INVALID_OP.to_string()),
        // }
    };

    // Short-circuiting boolean binary operations
    short_circuiting_bool_op := (T: Type(), op: u8_gen_ty(), a: bool_gen_ty(), b: bool_gen_ty()) -> bool_gen_ty() => |env| {
        const INVALID_OP: &str = "Invalid cond-binary operation parameters";

        // Parse the operator.
        let parsed_op = BinOp::try_from(
            try_use_term_as_integer_lit::<_, u8>(&env, op).ok_or(INVALID_OP)?,
        )
        .map_err(|_| INVALID_OP)?;

        let lhs_expr = try_use_term_as_const(&env, a);
        let rhs_expr = try_use_term_as_const(&env, b);

        // Use the constant evaluator to perform the operation.
        let eval = ConstFolder::new(env.layout_computer());
        Ok(None)

        // // Valid operations on booleans
        // macro_rules! operate_bool {
        //     ($op:expr, $lhs:expr, $rhs:expr) => {
        //         match $op {
        //             ShortCircuitingBoolOp::And => $lhs && $rhs,
        //             ShortCircuitingBoolOp::Or => $lhs || $rhs,
        //         }
        //     };
        // }

        // match (try_use_term_as_bool(a), try_use_term_as_bool(b)) {
        //     (Some(lhs), Some(rhs)) => {
        //         Ok(Some(bool_term(operate_bool!(parsed_op, lhs, rhs), a.origin().computed())))
        //     },
        //     _ => Ok(None),
        // }
    };

    // Binary operations (returning the same type as the arguments)
    bin_op := (T: Type(), op: u8_gen_ty(), a: ty(T), b: ty(T)) -> ty(T) => |env| {
        const INVALID_OP: &str = "Invalid endo-binary operation parameters";

        // Parse the operator.
        let parsed_op = BinOp::try_from(
            try_use_term_as_integer_lit::<_, u8>(&env, op).ok_or(INVALID_OP)?,
        )
        .map_err(|_| INVALID_OP)?;

        let lhs_const = try_use_term_as_const(&env, a);
        let rhs_const = try_use_term_as_const(&env, b);

        // Use the constant evaluator to perform the operation.
        let eval = ConstFolder::new(env.layout_computer());

        Ok(None)


        // Valid operations on floats
        // macro_rules! operate_float {
        //     ($op:expr, $lhs:expr, $rhs:expr) => {
        //         match $op {
        //             BinOp::Exp => $lhs.powf($rhs),
        //             BinOp::Add => $lhs + $rhs,
        //             BinOp::Sub => $lhs - $rhs,
        //             BinOp::Mul => $lhs * $rhs,
        //             BinOp::Div => $lhs / $rhs,
        //             BinOp::Mod => $lhs % $rhs,
        //             _ => return Err(INVALID_OP.to_string()),
        //         }
        //     };
        // }

        // // Valid operations on integers
        // macro_rules! operate_int {
        //     ($op:expr, $lhs:expr, $rhs:expr) => {
        //         match $op {
        //             BinOp::BitOr => $lhs | $rhs,
        //             BinOp::BitAnd => $lhs & $rhs,
        //             BinOp::BitXor => $lhs ^ $rhs,
        //             BinOp::Shr => $lhs >> $rhs,
        //             BinOp::Shl => $lhs << $rhs,
        //             BinOp::Add => $lhs + $rhs,
        //             BinOp::Sub => $lhs - $rhs,
        //             BinOp::Mul => $lhs * $rhs,
        //             BinOp::Div => $lhs / $rhs,
        //             BinOp::Mod => $lhs % $rhs,
        //             _ => return Err(INVALID_OP.to_string()),
        //         }
        //     };
        // }

        // macro_rules! handle_integer {
        //     ($rust_ty:ty) => {{
        //         match (try_use_term_as_integer_lit::<_, $rust_ty>(&env, a), try_use_term_as_integer_lit::<_, $rust_ty>(&env, b)) {
        //             (Some(lhs), Some(rhs)) => {
        //                 Ok(Some(create_term_from_const(operate_int!(parsed_op, lhs, rhs), a.origin().computed())))
        //             },
        //             _ => Ok(None),
        //         }
        //     }};
        // }

        // macro_rules! handle_float {
        //     ($rust_ty:ty) => {{
        //         match (try_use_term_as_float_lit::<$rust_ty>(a), try_use_term_as_float_lit::<$rust_ty>(b)) {
        //             (Some(lhs), Some(rhs)) => {
        //                 Ok(Some(create_term_from_const(operate_float!(parsed_op, lhs, rhs), a.origin().computed())))
        //             },
        //             _ => Ok(None),
        //         }
        //     }};
        // }

        // // Handle each `T` parameter:
        // match try_use_ty_as_lit_ty(&env, T) {
        //     Some(lit_ty) => match lit_ty {
        //         LitTy::U8 => handle_integer!(u8),
        //         LitTy::U16 => handle_integer!(u16),
        //         LitTy::U32 => handle_integer!(u32),
        //         LitTy::U64 => handle_integer!(u64),
        //         LitTy::U128 => handle_integer!(u128),
        //         LitTy::I8 => handle_integer!(i8),
        //         LitTy::I16 => handle_integer!(i16),
        //         LitTy::I32 => handle_integer!(i32),
        //         LitTy::I64 => handle_integer!(i64),
        //         LitTy::I128 => handle_integer!(i128),
        //         LitTy::F32 => handle_float!(f32),
        //         LitTy::F64 => handle_float!(f64),
        //         LitTy::Bool => Err(INVALID_OP.to_string()),
        //         LitTy::Char => Err(INVALID_OP.to_string()),
        //     },
        //     None => Err(INVALID_OP.to_string()),
        // }
    };

    // Unary operations
    un_op := (T: Type(), op: u8_gen_ty(), a: ty(T)) -> ty(T) => |env| {
        const INVALID_OP: &str = "Invalid unary operation parameters";

        // Parse the operator.
        let parsed_op =
            UnOp::try_from(try_use_term_as_integer_lit::<_, u8>(&env, op).ok_or(INVALID_OP)?)
                .map_err(|_| INVALID_OP)?;

        let lhs_const = try_use_term_as_const(&env, a);

        // Use the constant evaluator to perform the operation.
        let eval = ConstFolder::new(env.layout_computer());

        Ok(None)

        // // Valid operations on booleans
        // macro_rules! operate_bool {
        //     ($op:expr, $a:expr) => {
        //         match $op {
        //             UnOp::Not => !$a,
        //             _ => return Err(INVALID_OP.to_string()),
        //         }
        //     };
        // }

        // // Valid operations on floats
        // macro_rules! operate_float {
        //     ($op:expr, $a:expr) => {
        //         match $op {
        //             UnOp::Neg => -($a),
        //             _ => return Err(INVALID_OP.to_string()),
        //         }
        //     };
        // }

        // // Valid operations on integers
        // macro_rules! operate_integer {
        //     ($op:expr, $a:expr) => {
        //         match $op {
        //             UnOp::Neg => -($a),
        //             UnOp::BitNot => !($a),
        //             _ => return Err(INVALID_OP.to_string()),
        //         }
        //     };
        // }

        // macro_rules! handle_integer {
        //     ($rust_ty:ty) => {
        //         match try_use_term_as_integer_lit::<_, $rust_ty>(&env, a) {
        //             Some(a_lit) => Ok(Some(create_term_from_const(operate_integer!(parsed_op, a_lit), a.origin().computed()))),
        //             None => Ok(None),
        //         }
        //     };
        // }

        // macro_rules! handle_float {
        //     ($rust_ty:ty) => {
        //         match try_use_term_as_float_lit::<$rust_ty>(a) {
        //             Some(a_lit) => Ok(Some(create_term_from_const(operate_float!(parsed_op, a_lit), a.origin().computed()))),
        //             None => Ok(None),
        //         }
        //     };
        // }

        // // Handle each `T` parameter:
        // match try_use_ty_as_lit_ty(&env, T) {
        //     Some(lit_ty) => match lit_ty {
        //         LitTy::I8 => handle_integer!(i8),
        //         LitTy::I16 => handle_integer!(i16),
        //         LitTy::I32 => handle_integer!(i32),
        //         LitTy::I64 => handle_integer!(i64),
        //         LitTy::I128 => handle_integer!(i128),
        //         LitTy::F32 => handle_float!(f32),
        //         LitTy::F64 => handle_float!(f64),
        //         LitTy::Bool => {
        //             match try_use_term_as_bool(a) {
        //                 Some(a_bool) => Ok(Some(bool_term(operate_bool!(parsed_op, a_bool), a.origin().computed()))),
        //                 None => Ok(None),
        //             }
        //         }
        //         _ => Err(INVALID_OP.to_string()),
        //     },
        //     None => Err(INVALID_OP.to_string()),
        // }
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

    i8 := primitive (numeric_ctors(8, NumericCtorFlags::IS_SIGNED));
    i16 := primitive (numeric_ctors(16, NumericCtorFlags::IS_SIGNED));
    i32 := primitive (numeric_ctors(32, NumericCtorFlags::IS_SIGNED));
    i64 := primitive (numeric_ctors(64, NumericCtorFlags::IS_SIGNED));
    i128 := primitive (numeric_ctors(128, NumericCtorFlags::IS_SIGNED));
    isize := primitive (numeric_ctors(64, NumericCtorFlags::IS_SIGNED & NumericCtorFlags::IS_PLATFORM));
    ibig := primitive (numeric_ctors(0, NumericCtorFlags::IS_SIGNED));

    u8 := primitive (numeric_ctors(8, NumericCtorFlags::empty()));
    u16 := primitive (numeric_ctors(16, NumericCtorFlags::empty()));
    u32 := primitive (numeric_ctors(32, NumericCtorFlags::empty()));
    u64 := primitive (numeric_ctors(64, NumericCtorFlags::empty()));
    u128 := primitive (numeric_ctors(128, NumericCtorFlags::empty()));
    ubig := primitive (numeric_ctors(0, NumericCtorFlags::empty()));
    usize := primitive (numeric_ctors(64, NumericCtorFlags::IS_PLATFORM));

    f32 := primitive (numeric_ctors(32, NumericCtorFlags::IS_FLOAT));
    f64 := primitive (numeric_ctors(64, NumericCtorFlags::IS_FLOAT));
}
