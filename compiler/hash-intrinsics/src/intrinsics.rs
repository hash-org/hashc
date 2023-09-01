//! Definition and lookup of intrinsics.
use std::{fmt::Debug, process};

use hash_attrs::attr::attr_store;
use hash_source::identifier::Identifier;
use hash_storage::store::{
    statics::CoreStoreId, DefaultPartialStore, PartialStore, SequenceStoreKey,
};
use hash_tir::{
    self,
    ast_info::HasNodeId,
    building::gen::{params, sym},
    environment::env::{AccessToEnv, Env},
    fns::{FnBody, FnDef, FnDefId, FnTy},
    intrinsics::IntrinsicId,
    lits::Lit,
    mods::{ModMember, ModMemberValue},
    node::Node,
    params::Param,
    primitives::primitives,
    refs::RefKind,
    terms::{Term, TermId},
    tys::Ty,
};
use hash_utils::stream_less_writeln;
use num_bigint::{BigInt, BigUint};
use num_enum::{IntoPrimitive, TryFromPrimitive};

use crate::utils::{LitTy, PrimitiveUtils};

/// Information about an intrinsic.
///
/// An intrinsic contains an ID which is just a symbol internally, a
/// corresponding function definition (in order to be able to call it from the
/// code), and an implementation which is a Rust function that is called when
/// the intrinsic is called.
pub struct Intrinsic {
    /// The ID of the intrinsic.
    pub id: IntrinsicId,
    /// The function definition of the intrinsic.
    pub fn_def: FnDefId,
    /// The implementation of the intrinsic.
    ///
    /// This will be used by the compile-time evaluation part of typechecking,
    /// and as a reference for the behaviour of the intrinsic.
    pub implementation: IntrinsicImpl,
}

pub trait IntrinsicAbilities {
    /// Normalise a term fully.
    fn normalise_term(&self, term: TermId) -> Result<TermId, String>;

    /// Get the current environment.
    fn env(&self) -> &Env;
}

impl AccessToEnv for dyn IntrinsicAbilities + '_ {
    fn env(&self) -> &Env {
        <Self as IntrinsicAbilities>::env(self)
    }
}

pub type IntrinsicImpl = fn(&(dyn IntrinsicAbilities), &[TermId]) -> Result<TermId, String>;

macro_rules! defined_intrinsics {
    ($($name:ident),* $(,)?) => {
        pub struct DefinedIntrinsics {
            pub implementations: DefaultPartialStore<IntrinsicId, Intrinsic>,

            $($name: FnDefId),*
        }

        impl DefinedIntrinsics {
            $(
                pub fn $name(&self) -> FnDefId {
                    self.$name
                }
            )*
        }

        impl DefinedIntrinsics {
            /// Create a list of [`ModMemberData`] that corresponds to the defined intrinsics.
            ///
            /// This can be used to make a module and enter its scope.
            pub fn as_mod_members(&self) -> Vec<ModMember> {
                vec![
                    $(
                        ModMember {
                            name: self.$name.borrow().name,
                            value: ModMemberValue::Fn(self.$name)
                        },
                    )*
                ]
            }
        }
    };

}

// Contains all the defined intrinsics
defined_intrinsics! {
    bool_bin_op,
    short_circuiting_op,
    endo_bin_op,
    prim_type_eq_op,
    un_op,
    abort,
    panic,
    user_error,
    eval,
    debug_print,
    print_fn_directives,

    align_of,
    size_of,

    ptr_offset,
    transmute,

    // Casting is used to represent a conversion between two types. For example,
    // converting a `char` to an `u32` but without necessarily going through
    // transmuting the types and hoping it will be ok. Cast may imply a runtime
    // operation to convert the value to the desired type whilst the transmute
    // is more of a type marker to the compiler.
    cast,
}

impl Debug for DefinedIntrinsics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DefinedIntrinsics").finish()
    }
}

/// A unary operator.
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

impl DefinedIntrinsics {
    /// Add the `un_op` intrinsic.
    ///
    /// This intrinsic has signature
    /// `un_op: (T: Type, op: u8, a: T) -> T`
    ///
    /// The `op` parameter is an integer which represents the operation to
    /// perform, which is one of the `UnOp` variants. The `a` is the operand
    fn add_un_op_intrinsic(
        implementations: &DefaultPartialStore<IntrinsicId, Intrinsic>,
    ) -> FnDefId {
        let t_sym = sym("T");
        let op_sym = sym("op");
        let a_sym = sym("a");
        let params = params([
            (t_sym, Ty::flexible_universe(), None),
            (op_sym, Ty::data(primitives().u8()), None),
            (a_sym, Ty::from(t_sym), None),
        ]);
        let ret = Ty::from(t_sym);

        Self::add_intrinsic(
            implementations,
            "un_op",
            FnTy::builder().params(params).return_ty(ret).build(),
            move |env, args| {
                const INVALID_OP: &str = "Invalid unary operation parameters";

                // Parse the arguments
                let (t, op, a) = (args[0], args[1], args[2]);

                // Parse the operator.
                let parsed_op =
                    UnOp::try_from(env.try_use_term_as_integer_lit::<u8>(op).ok_or(INVALID_OP)?)
                        .map_err(|_| INVALID_OP)?;

                // Valid operations on booleans
                macro_rules! operate_bool {
                    ($op:expr, $a:expr) => {
                        match $op {
                            UnOp::Not => !$a,
                            _ => return Err(INVALID_OP.to_string()),
                        }
                    };
                }

                // Valid operations on floats
                macro_rules! operate_float {
                    ($op:expr, $a:expr) => {
                        match $op {
                            UnOp::Neg => -($a),
                            _ => return Err(INVALID_OP.to_string()),
                        }
                    };
                }

                // Valid operations on integers
                macro_rules! operate_integer {
                    ($op:expr, $a:expr) => {
                        match $op {
                            UnOp::Neg => -($a),
                            UnOp::BitNot => !($a),
                            _ => return Err(INVALID_OP.to_string()),
                        }
                    };
                }

                macro_rules! handle_integer {
                    ($rust_ty:ty) => {{
                        let a: $rust_ty = env.try_use_term_as_integer_lit(a).unwrap();
                        Ok(env.create_term_from_integer_lit(operate_integer!(parsed_op, a)))
                    }};
                }

                // Handle each `T` parameter:
                match env.try_use_ty_as_lit_ty(t.as_ty()) {
                    Some(lit_ty) => match lit_ty {
                        LitTy::I8 => handle_integer!(i8),
                        LitTy::I16 => handle_integer!(i16),
                        LitTy::I32 => handle_integer!(i32),
                        LitTy::I64 => handle_integer!(i64),
                        LitTy::I128 => handle_integer!(i128),
                        LitTy::IBig => {
                            let a: BigInt = env.try_use_term_as_integer_lit(a).unwrap();
                            Ok(env.create_term_from_integer_lit(operate_integer!(parsed_op, a)))
                        }
                        LitTy::F32 => {
                            // @@Todo: properly handle f32
                            let a: f64 = env.try_use_term_as_float_lit(a).unwrap();
                            Ok(env.create_term_from_float_lit(operate_float!(parsed_op, a)))
                        }
                        LitTy::F64 => {
                            let a: f64 = env.try_use_term_as_float_lit(a).unwrap();
                            Ok(env.create_term_from_float_lit(operate_float!(parsed_op, a)))
                        }
                        LitTy::Bool => {
                            let a: bool = env.try_use_term_as_bool(a).unwrap();
                            Ok(env.new_bool_term(operate_bool!(parsed_op, a)))
                        }
                        _ => Err(INVALID_OP.to_string()),
                    },
                    None => Err(INVALID_OP.to_string()),
                }
            },
        )
    }

    /// Add the `short_circuiting_bin_op` intrinsics.
    ///
    /// This intrinsic has the signature:
    /// ```ignore
    /// short_circuiting_bin_op: (op: u8, a: bool, b: bool) -> bool
    /// ```
    fn add_short_circuiting_op_intrinsic(
        implementations: &DefaultPartialStore<IntrinsicId, Intrinsic>,
    ) -> FnDefId {
        let t_sym = sym("T");
        let op_sym = sym("op");
        let a_sym = sym("a");
        let b_sym = sym("b");
        let ty = Ty::data(primitives().bool());

        let params = params([
            (t_sym, Ty::flexible_universe(), None),
            (op_sym, Ty::data(primitives().u8()), None),
            (a_sym, ty, None),
            (b_sym, ty, None),
        ]);

        Self::add_intrinsic(
            implementations,
            "bool_bin_op",
            FnTy::builder().params(params).return_ty(ty).build(),
            |env, args| {
                const INVALID_OP: &str = "Invalid cond-binary operation parameters";

                // Parse the arguments
                let (op, lhs, rhs) = (args[1], args[2], args[3]);

                // Parse the operator.
                let parsed_op = ShortCircuitBinOp::try_from(
                    env.try_use_term_as_integer_lit::<u8>(op).ok_or(INVALID_OP)?,
                )
                .map_err(|_| INVALID_OP)?;

                // Valid operations on big-ints
                macro_rules! operate_bool {
                    ($op:expr, $lhs:expr, $rhs:expr) => {
                        match $op {
                            ShortCircuitBinOp::And => $lhs && $rhs,
                            ShortCircuitBinOp::Or => $lhs || $rhs,
                        }
                    };
                }

                let lhs: bool = env.try_use_term_as_bool(lhs).unwrap();
                let rhs: bool = env.try_use_term_as_bool(rhs).unwrap();
                Ok(env.new_bool_term(operate_bool!(parsed_op, lhs, rhs)))
            },
        )
    }

    /// Add the `bool_bin_op` intrinsic.
    ///
    /// This intrinsic has signature
    /// `bool_bin_op: (T: Type, op: u8, a: T, b: T) -> bool`
    ///
    /// The `op` parameter is an integer which represents the operation to
    /// perform, which is one of the `BoolBinOp` variants. The `a` and `b`
    /// parameters are the two operands, and the return value is the result
    /// of the operation.
    fn add_bool_bin_op_intrinsic(
        implementations: &DefaultPartialStore<IntrinsicId, Intrinsic>,
    ) -> FnDefId {
        let t_sym = sym("T");
        let op_sym = sym("op");
        let a_sym = sym("a");
        let b_sym = sym("b");
        let params = params([
            (t_sym, Ty::flexible_universe(), None),
            (op_sym, Ty::data(primitives().u8()), None),
            (a_sym, Ty::from(t_sym), None),
            (b_sym, Ty::from(t_sym), None),
        ]);
        let ret = Ty::data(primitives().bool());

        Self::add_intrinsic(
            implementations,
            "bool_bin_op",
            FnTy::builder().params(params).return_ty(ret).build(),
            |env, args| {
                const INVALID_OP: &str = "Invalid cond-binary operation parameters";

                // Parse the arguments
                let (t, op, lhs, rhs) = (args[0], args[1], args[2], args[3]);

                // Parse the operator.
                let parsed_op = BoolBinOp::try_from(
                    env.try_use_term_as_integer_lit::<u8>(op).ok_or(INVALID_OP)?,
                )
                .map_err(|_| INVALID_OP)?;

                // Valid operations on big-ints
                macro_rules! operate_bool {
                    ($op:expr, $lhs:expr, $rhs:expr) => {
                        match $op {
                            BoolBinOp::EqEq => $lhs == $rhs,
                            BoolBinOp::NotEq => $lhs != $rhs,
                            _ => return Err(INVALID_OP.to_string()),
                        }
                    };
                }

                // Valid operations on floats
                macro_rules! operate_float {
                    ($op:expr, $lhs:expr, $rhs:expr) => {
                        match $op {
                            BoolBinOp::EqEq => $lhs == $rhs,
                            BoolBinOp::NotEq => $lhs != $rhs,
                            BoolBinOp::Gt => $lhs > $rhs,
                            BoolBinOp::GtEq => $lhs >= $rhs,
                            BoolBinOp::Lt => $lhs < $rhs,
                            BoolBinOp::LtEq => $lhs <= $rhs,
                        }
                    };
                }

                // Valid operations on integers
                macro_rules! operate_int {
                    ($op:expr, $lhs:expr, $rhs:expr) => {
                        match $op {
                            BoolBinOp::EqEq => $lhs == $rhs,
                            BoolBinOp::NotEq => $lhs != $rhs,
                            BoolBinOp::Gt => $lhs > $rhs,
                            BoolBinOp::GtEq => $lhs >= $rhs,
                            BoolBinOp::Lt => $lhs < $rhs,
                            BoolBinOp::LtEq => $lhs <= $rhs,
                        }
                    };
                }

                // Valid operations on characters
                macro_rules! operate_char {
                    ($op:expr, $lhs:expr, $rhs:expr) => {
                        match $op {
                            BoolBinOp::EqEq => $lhs == $rhs,
                            BoolBinOp::NotEq => $lhs != $rhs,
                            BoolBinOp::Gt => $lhs > $rhs,
                            BoolBinOp::GtEq => $lhs >= $rhs,
                            BoolBinOp::Lt => $lhs < $rhs,
                            BoolBinOp::LtEq => $lhs <= $rhs,
                        }
                    };
                }

                macro_rules! handle_integer {
                    ($rust_ty:ty) => {{
                        let lhs: $rust_ty = env.try_use_term_as_integer_lit(lhs).unwrap();
                        let rhs: $rust_ty = env.try_use_term_as_integer_lit(rhs).unwrap();
                        Ok(env.new_bool_term(operate_int!(parsed_op, lhs, rhs)))
                    }};
                }

                // Handle each `T` parameter:
                match env.try_use_ty_as_lit_ty(t.as_ty()) {
                    Some(lit_ty) => match lit_ty {
                        LitTy::U8 => handle_integer!(u8),
                        LitTy::U16 => handle_integer!(u16),
                        LitTy::U32 => handle_integer!(u32),
                        LitTy::U64 => handle_integer!(u64),
                        LitTy::U128 => handle_integer!(u128),
                        LitTy::I8 => handle_integer!(i8),
                        LitTy::I16 => handle_integer!(i16),
                        LitTy::I32 => handle_integer!(i32),
                        LitTy::I64 => handle_integer!(i64),
                        LitTy::I128 => handle_integer!(i128),
                        LitTy::UBig => handle_integer!(BigUint),
                        LitTy::IBig => handle_integer!(BigInt),
                        LitTy::F32 => {
                            let lhs: f64 = env.try_use_term_as_float_lit(lhs).unwrap();
                            let rhs: f64 = env.try_use_term_as_float_lit(rhs).unwrap();
                            Ok(env.new_bool_term(operate_float!(parsed_op, lhs, rhs)))
                        }
                        LitTy::F64 => {
                            let lhs: f64 = env.try_use_term_as_float_lit(lhs).unwrap();
                            let rhs: f64 = env.try_use_term_as_float_lit(rhs).unwrap();
                            Ok(env.new_bool_term(operate_float!(parsed_op, lhs, rhs)))
                        }
                        LitTy::Bool => {
                            let lhs: bool = env.try_use_term_as_bool(lhs).unwrap();
                            let rhs: bool = env.try_use_term_as_bool(rhs).unwrap();
                            Ok(env.new_bool_term(operate_bool!(parsed_op, lhs, rhs)))
                        }
                        LitTy::Char => {
                            let lhs: char = env.try_use_term_as_char_lit(lhs).unwrap();
                            let rhs: char = env.try_use_term_as_char_lit(rhs).unwrap();
                            Ok(env.new_bool_term(operate_char!(parsed_op, lhs, rhs)))
                        }
                    },
                    None => Err(INVALID_OP.to_string()),
                }
            },
        )
    }

    /// Add the `endo_bin_op` intrinsic.
    ///
    /// This intrinsic has signature
    /// `endo_bin_op: (T: Type, op: u8, a: T, b: T) -> T`
    ///
    /// The `op` parameter is an integer which represents the operation to
    /// perform, which is one of the `EndoBinOp` variants. The `a` and `b`
    /// parameters are the two operands, and the return value is the result
    /// of the operation.
    fn add_endo_bin_op_intrinsic(
        implementations: &DefaultPartialStore<IntrinsicId, Intrinsic>,
    ) -> FnDefId {
        let t_sym = sym("T");
        let op_sym = sym("op");
        let a_sym = sym("a");
        let b_sym = sym("b");
        let params = params([
            (t_sym, Ty::flexible_universe(), None),
            (op_sym, Ty::data(primitives().u8()), None),
            (a_sym, Ty::from(t_sym), None),
            (b_sym, Ty::from(t_sym), None),
        ]);
        let ret = Ty::from(t_sym);

        Self::add_intrinsic(
            implementations,
            "endo_bin_op",
            FnTy::builder().params(params).return_ty(ret).build(),
            |env, args| {
                const INVALID_OP: &str = "Invalid endo-binary operation parameters";

                // Parse the arguments
                let (t, op, lhs, rhs) = (args[0], args[1], args[2], args[3]);

                // Parse the operator.
                let parsed_op = EndoBinOp::try_from(
                    env.try_use_term_as_integer_lit::<u8>(op).ok_or(INVALID_OP)?,
                )
                .map_err(|_| INVALID_OP)?;

                // Valid operations on big-ints
                macro_rules! operate_bigint {
                    ($op:expr, $lhs:expr, $rhs:expr) => {
                        match $op {
                            EndoBinOp::BitOr => $lhs | $rhs,
                            EndoBinOp::BitAnd => $lhs & $rhs,
                            EndoBinOp::BitXor => $lhs ^ $rhs,
                            EndoBinOp::Add => $lhs + $rhs,
                            EndoBinOp::Sub => $lhs - $rhs,
                            EndoBinOp::Mul => $lhs * $rhs,
                            EndoBinOp::Div => $lhs / $rhs,
                            EndoBinOp::Mod => $lhs % $rhs,
                            _ => return Err(INVALID_OP.to_string()),
                        }
                    };
                }

                // Valid operations on floats
                macro_rules! operate_float {
                    ($op:expr, $lhs:expr, $rhs:expr) => {
                        match $op {
                            EndoBinOp::Exp => $lhs.powf($rhs),
                            EndoBinOp::Add => $lhs + $rhs,
                            EndoBinOp::Sub => $lhs - $rhs,
                            EndoBinOp::Mul => $lhs * $rhs,
                            EndoBinOp::Div => $lhs / $rhs,
                            EndoBinOp::Mod => $lhs % $rhs,
                            _ => return Err(INVALID_OP.to_string()),
                        }
                    };
                }

                // Valid operations on integers
                macro_rules! operate_int {
                    ($op:expr, $lhs:expr, $rhs:expr) => {
                        match $op {
                            EndoBinOp::BitOr => $lhs | $rhs,
                            EndoBinOp::BitAnd => $lhs & $rhs,
                            EndoBinOp::BitXor => $lhs ^ $rhs,
                            EndoBinOp::Shr => $lhs >> $rhs,
                            EndoBinOp::Shl => $lhs << $rhs,
                            EndoBinOp::Add => $lhs + $rhs,
                            EndoBinOp::Sub => $lhs - $rhs,
                            EndoBinOp::Mul => $lhs * $rhs,
                            EndoBinOp::Div => $lhs / $rhs,
                            EndoBinOp::Mod => $lhs % $rhs,
                            _ => return Err(INVALID_OP.to_string()),
                        }
                    };
                }

                macro_rules! handle_integer {
                    ($rust_ty:ty) => {{
                        let lhs: $rust_ty = env.try_use_term_as_integer_lit(lhs).unwrap();
                        let rhs: $rust_ty = env.try_use_term_as_integer_lit(rhs).unwrap();
                        Ok(env.create_term_from_integer_lit(operate_int!(parsed_op, lhs, rhs)))
                    }};
                }

                macro_rules! handle_bigint {
                    ($rust_ty:ty) => {{
                        let lhs: $rust_ty = env.try_use_term_as_integer_lit(lhs).unwrap();
                        let rhs: $rust_ty = env.try_use_term_as_integer_lit(rhs).unwrap();
                        Ok(env.create_term_from_integer_lit(operate_bigint!(parsed_op, lhs, rhs)))
                    }};
                }

                // Handle each `T` parameter:
                match env.try_use_ty_as_lit_ty(t.as_ty()) {
                    Some(lit_ty) => match lit_ty {
                        LitTy::U8 => handle_integer!(u8),
                        LitTy::U16 => handle_integer!(u16),
                        LitTy::U32 => handle_integer!(u32),
                        LitTy::U64 => handle_integer!(u64),
                        LitTy::U128 => handle_integer!(u128),
                        LitTy::I8 => handle_integer!(i8),
                        LitTy::I16 => handle_integer!(i16),
                        LitTy::I32 => handle_integer!(i32),
                        LitTy::I64 => handle_integer!(i64),
                        LitTy::I128 => handle_integer!(i128),
                        LitTy::UBig => handle_bigint!(BigUint),
                        LitTy::IBig => handle_bigint!(BigInt),
                        LitTy::F32 => {
                            let lhs: f64 = env.try_use_term_as_float_lit(lhs).unwrap();
                            let rhs: f64 = env.try_use_term_as_float_lit(rhs).unwrap();
                            Ok(env.create_term_from_float_lit(operate_float!(parsed_op, lhs, rhs)))
                        }
                        LitTy::F64 => {
                            let lhs: f64 = env.try_use_term_as_float_lit(lhs).unwrap();
                            let rhs: f64 = env.try_use_term_as_float_lit(rhs).unwrap();
                            Ok(env.create_term_from_float_lit(operate_float!(parsed_op, lhs, rhs)))
                        }
                        LitTy::Bool => Err(INVALID_OP.to_string()),
                        LitTy::Char => Err(INVALID_OP.to_string()),
                    },
                    None => Err(INVALID_OP.to_string()),
                }
            },
        )
    }

    /// Add a primitive to check for primitive data type equality.
    fn add_prim_type_eq_op(
        implementations: &DefaultPartialStore<IntrinsicId, Intrinsic>,
    ) -> FnDefId {
        let ty = Ty::flexible_universe();
        let bool_ty = Ty::data(primitives().bool());
        let bin_op_name = "prim_type_eq".to_string();

        Self::add_intrinsic(
            implementations,
            bin_op_name,
            FnTy::builder().params(Param::seq_positional([ty, ty])).return_ty(bool_ty).build(),
            |prim, args| {
                let (lhs, rhs) = (args[0], args[1]);
                let invalid = || {
                    Err("Invalid arguments for type equality intrinsic. Only data types with no arguments can be compared".to_string())
                };

                if let (Term::Ty(lhs_ty), Term::Ty(rhs_ty)) = (*lhs.value(), *rhs.value()) {
                    if let (Ty::Data(lhs_data), Ty::Data(rhs_data)) =
                        (*lhs_ty.value(), *rhs_ty.value())
                    {
                        if lhs_data.args.value().len() == 0 && rhs_data.args.value().len() == 0 {
                            return Ok(prim.new_bool_term(lhs_data.data_def == rhs_data.data_def));
                        }
                    }
                }

                invalid()
            },
        )
    }

    /// Create the default intrinsics.
    pub fn create<T: AccessToEnv + Copy>(env: T) -> Self {
        let implementations = DefaultPartialStore::new();

        let add = |name: &'static str, fn_ty: FnTy, implementation: IntrinsicImpl| {
            Self::add_intrinsic(&implementations, name, fn_ty, implementation)
        };

        // Aborting
        let abort = add(
            "abort",
            FnTy::builder().params(params([])).return_ty(env.new_never_ty()).build(),
            |_, _| process::exit(1),
        );

        // Panicking
        let panic = add(
            "panic",
            FnTy::builder()
                .params(Param::seq_positional([Ty::data(primitives().str())]))
                .return_ty(env.new_never_ty())
                .build(),
            |_, args| {
                stream_less_writeln!("{}", args[1]);
                process::exit(1);
            },
        );

        // User errors
        let user_error = add(
            "user_error",
            FnTy::builder()
                .params(Param::seq_positional([Ty::data(primitives().str())]))
                .return_ty(env.new_never_ty())
                .build(),
            |_, args| match *args[0].value() {
                Term::Lit(Lit::Str(str_lit)) => Err(str_lit.value().to_string()),
                _ => Err("`user_error` expects a string literal as argument".to_string())?,
            },
        );

        let debug_print = {
            let t_sym = sym("T");
            let a_sym = sym("a");
            let params =
                params([(t_sym, Ty::flexible_universe(), None), (a_sym, Ty::from(t_sym), None)]);
            let ret = Ty::void();
            add("debug_print", FnTy::builder().params(params).return_ty(ret).build(), |_, args| {
                stream_less_writeln!("{}", args[1]);
                Ok(Term::void())
            })
        };

        let print_fn_directives = {
            let t_sym = sym("T");
            let a_sym = sym("a");
            let params =
                params([(t_sym, Ty::flexible_universe(), None), (a_sym, Ty::from(t_sym), None)]);
            let ret = Ty::void();
            add(
                "print_fn_directives",
                FnTy::builder().params(params).return_ty(ret).build(),
                |_, args| {
                    if let Term::FnRef(fn_def) = *args[1].value() {
                        attr_store().map_with_default(fn_def.node_id_or_default(), |attrs| {
                            stream_less_writeln!("{:?}", attrs);
                        });
                    }
                    Ok(Term::void())
                },
            )
        };

        let eval = {
            let t_sym = sym("T");
            let a_sym = sym("a");
            let params =
                params([(t_sym, Ty::flexible_universe(), None), (a_sym, Ty::from(t_sym), None)]);
            let ret = Ty::from(t_sym);
            add("eval", FnTy::builder().params(params).return_ty(ret).build(), |env, args| {
                let evaluated = env.normalise_term(args[1])?;
                Ok(evaluated)
            })
        };

        // Primitive type equality
        let prim_type_eq_op = Self::add_prim_type_eq_op(&implementations);

        // Endo bin ops
        let endo_bin_op = Self::add_endo_bin_op_intrinsic(&implementations);

        // Bool bin ops
        let bool_bin_op = Self::add_bool_bin_op_intrinsic(&implementations);

        // Short circuiting ops
        let short_circuiting_op = Self::add_short_circuiting_op_intrinsic(&implementations);

        // Unary ops
        let un_op = Self::add_un_op_intrinsic(&implementations);

        // Size of
        let size_of = {
            let t_sym = sym("T");
            let params = params([(t_sym, Ty::flexible_universe(), None)]);
            let ret = Ty::data(primitives().usize());
            add("size_of", FnTy::builder().params(params).return_ty(ret).build(), |_, _| {
                unimplemented!("`size_of` intrinsic evaluation")
            })
        };

        // Align of
        let align_of = {
            let t_sym = sym("T");
            let params = params([(t_sym, Ty::flexible_universe(), None)]);
            let ret = Ty::data(primitives().usize());
            add("align_of", FnTy::builder().params(params).return_ty(ret).build(), |_, _| {
                unimplemented!("`align_of` intrinsic evaluation")
            })
        };

        let u8 = Ty::data(primitives().u8());
        let usize = Ty::data(primitives().usize());
        let raw_ptr_ty = env.new_ref_ty(u8, RefKind::Raw, false);

        // ptr_offset
        let ptr_offset = {
            let t_sym = sym("bytes");
            let a_sym = sym("len");

            let params = params([(t_sym, raw_ptr_ty, None), (a_sym, usize, None)]);

            add(
                "ptr_offset",
                FnTy::builder().params(params).return_ty(raw_ptr_ty).build(),
                |_, _| unimplemented!("`ptr_offset` intrinsic evaluation"),
            )
        };

        let transmute = {
            let t_sym = sym("T");
            let a_sym = sym("item");
            let u_sym = sym("U");
            let params = params([
                (t_sym, Ty::flexible_universe(), None),
                (u_sym, Ty::flexible_universe(), None),
                (a_sym, Ty::from(t_sym), None),
            ]);

            let ret = Ty::from(u_sym);
            add("transmute", FnTy::builder().params(params).return_ty(ret).build(), |_, args| {
                // No-op
                Ok(args[2])
            })
        };

        let cast = {
            let t_sym = sym("T");
            let a_sym = sym("item");
            let u_sym = sym("U");
            let params = params([
                (t_sym, Ty::flexible_universe(), None),
                (u_sym, Ty::flexible_universe(), None),
                (a_sym, Ty::from(t_sym), None),
            ]);

            let ret = Ty::from(u_sym);
            add("cast", FnTy::builder().params(params).return_ty(ret).build(), |_, _| {
                unimplemented!("`cast` intrinsic evaluation")
            })
        };

        DefinedIntrinsics {
            eval,
            implementations,
            print_fn_directives,
            prim_type_eq_op,
            short_circuiting_op,
            bool_bin_op,
            endo_bin_op,
            un_op,
            abort,
            panic,
            user_error,
            debug_print,
            align_of,
            size_of,
            ptr_offset,
            transmute,
            cast,
        }
    }

    /// Add an intrinsic to the store.
    fn add_intrinsic(
        implementations: &DefaultPartialStore<IntrinsicId, Intrinsic>,
        name: impl Into<Identifier>,
        fn_ty: FnTy,
        implementation: IntrinsicImpl,
    ) -> FnDefId {
        let name = name.into();
        let intrinsic_id = IntrinsicId(sym(name));

        let fn_def = Node::create_gen(FnDef {
            name: intrinsic_id.0,
            ty: fn_ty,
            body: FnBody::Intrinsic(intrinsic_id),
        });
        let intrinsic_impl = Intrinsic { id: intrinsic_id, fn_def, implementation };
        implementations.insert(intrinsic_id, intrinsic_impl);

        fn_def
    }
}

/// Trait to be able to access intrinsics.
///
/// This should be implemented by the typechecking environment.
pub trait AccessToIntrinsics {
    fn intrinsics(&self) -> &DefinedIntrinsics;
}
