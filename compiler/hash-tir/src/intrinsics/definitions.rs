//! Declaratively defines all the primitives and intrinsics of the language at
//! the TIR level.
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
    intrinsics::utils::{try_use_term_as_const, try_use_term_as_integer_lit},
    make_intrinsics, make_primitives,
    tir::{
        numeric_ctors, ArrayCtorInfo, CtorDefId, DataDefId, FnTy, Lit, ModMember, Node, NodeOrigin,
        NumericCtorFlags, PrimitiveCtorInfo, RefKind, Term, TermId, TyId,
    },
};

const INVALID_OP: &str = "Invalid cond-binary operation parameters";

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
            Err(value.as_alloc().to_str())
        } else {
            Err("`user_error` expects a string literal as argument".to_string())
        }
    };

    debug_print := (T: Type(), item: ty(T)) -> never_gen_ty() => |env| {
        stream_less_writeln!("{}", item);
        Ok(Some(unit_term()))
    };

    // Condition binary operations (i.e. returning booleans)
    cond_bin_op := (T: Type(), op: u8_gen_ty(), a: ty(T), b: ty(T)) -> bool_gen_ty() => |env| {
        // Parse the operator.
        let parsed_op = BinOp::try_from(
            try_use_term_as_integer_lit::<_, u8>(&env, op).ok_or(INVALID_OP)?,
        )
        .map_err(|_| INVALID_OP)?;

        match (try_use_term_as_const(&env, a), try_use_term_as_const(&env, b)) {
            (Some(lhs_const), Some(rhs_const)) => {
                // Use the constant evaluator to perform the operation.
                let eval = ConstFolder::new(env.layout_computer());
                Ok(eval.try_fold_bin_op(parsed_op, &lhs_const, &rhs_const).map(|result| {
                    term(Node::create_gen(Lit::Const(result)))
                }))
            }
            _ => Ok(None),
        }
    };

    // Short-circuiting boolean binary operations
    short_circuiting_bool_op := (op: u8_gen_ty(), a: bool_gen_ty(), b: bool_gen_ty()) -> bool_gen_ty() => |env| {

        // Parse the operator.
        let parsed_op = BinOp::try_from(
            try_use_term_as_integer_lit::<_, u8>(&env, op).ok_or(INVALID_OP)?,
        )
        .map_err(|_| INVALID_OP)?;

        match (try_use_term_as_const(&env, a), try_use_term_as_const(&env, b)) {
            (Some(lhs_const), Some(rhs_const)) => {
                let eval = ConstFolder::new(env.layout_computer());
                Ok(eval.try_fold_bin_op(parsed_op, &lhs_const, &rhs_const).map(|result| {
                    term(Node::create_gen(Lit::Const(result)))
                }))
            }
            _ => Ok(None),
        }
    };

    // Binary operations (returning the same type as the arguments)
    bin_op := (T: Type(), op: u8_gen_ty(), a: ty(T), b: ty(T)) -> ty(T) => |env| {
        const INVALID_OP: &str = "Invalid endo-binary operation parameters";

        // Parse the operator.
        let parsed_op = BinOp::try_from(
            try_use_term_as_integer_lit::<_, u8>(&env, op).ok_or(INVALID_OP)?,
        )
        .map_err(|_| INVALID_OP)?;

        match (try_use_term_as_const(&env, a), try_use_term_as_const(&env, b)) {
            (Some(lhs_const), Some(rhs_const)) => {
                let eval = ConstFolder::new(env.layout_computer());
                Ok(eval.try_fold_bin_op(parsed_op, &lhs_const, &rhs_const).map(|result| {
                    term(Node::create_gen(Lit::Const(result)))
                }))
            }
            _ => Ok(None),
        }
    };

    // Unary operations
    un_op := (T: Type(), op: u8_gen_ty(), a: ty(T)) -> ty(T) => |env| {
        const INVALID_OP: &str = "Invalid unary operation parameters";
        // Parse the operator.
        let parsed_op =
            UnOp::try_from(try_use_term_as_integer_lit::<_, u8>(&env, op).ok_or(INVALID_OP)?)
                .map_err(|_| INVALID_OP)?;

        match try_use_term_as_const(&env, a) {
            Some(c)  => {
                // Use the constant evaluator to perform the operation.
                let eval = ConstFolder::new(env.layout_computer());
                Ok(eval.try_fold_un_op(parsed_op, &c).map(|result| {
                    term(Node::create_gen(Lit::Const(result)))
                }))
            }
            None => Ok(None),
        }
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
