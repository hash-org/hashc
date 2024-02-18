//! This file contains utility functions for parsing Hash source
//! integer and float literals. This code is located here because
//! it could be used by various parts of the compiler, and it is
//! not specific to the parser. The reason why this is, is because
//! float and integer literal parsing is **delayed** until the type
//! of the literal is known. Since the parser does not know the type
//! of the literal, it can only attempt to parse it as a default float
//! or integer literal. Only during typechecking is the type of the
//! literal fully known (from annotation on the type itself or from
//! some other context).
//!
//! In the situation that the type is not known, such as during attribute
//! resolution/expansion, a default type is assumed (i.e. `i32` for integers
//! and `f64` for floats). This is fine because the only accepted types
//! for attributes are `i32`, `f64`, `bool`, `str` and `char`. In the
//! worst case, the interned value can always be adjusted using
//! [`InternedInt::adjust()`] and [`InternedFloat::adjust()`].

use std::num;

use hash_ast::ast::{self, AstNodeId, FloatLit, IntLit};
use hash_reporting::{hash_error_codes::error_codes::HashErrorCode, reporter::Reporter};
use hash_repr::{
    constant::{Const, ConstKind},
    ty::{ReprTyId, ToReprTy, COMMON_REPR_TYS},
};
use hash_source::constant::{
    AllocId, BigIntTy, FloatTy, IntTy, NormalisedIntTy, SIntTy, Scalar, Size, UIntTy,
};
use hash_storage::store::statics::StoreId;
pub use hash_token::{FloatLitKind, IntLitKind};
use hash_utils::num_bigint::BigInt;

/// An error that occurred when parsing a literal.
#[derive(Debug, Clone)]
pub struct LitParseError {
    /// The location of the literal, i.e. the [Hunk].
    span: AstNodeId,

    /// The kind of error that occurred when parsing the
    /// literal.
    kind: LitParseErrorKind,

    /// The contents that were parsed, used for more detailed
    /// error reporting.
    contents: String,
}

impl LitParseError {
    /// Create a new [LitParseError] from the given [Hunk] and
    /// [LitParsingErrorKind].
    pub fn new(span: AstNodeId, contents: String, kind: LitParseErrorKind) -> Self {
        Self { span, kind, contents }
    }
}

/// The kind of error that ocurred.
#[derive(Clone, Copy, Debug)]
pub enum LitParseErrorKind {
    /// Occurs when a float literal doesn't follow the language
    /// specification, or is too large.
    MalformedFloatLit,

    /// Occurs when a int literal doesn't follow the language
    /// specification, or is too large.
    MalformedIntLit,

    /// Occurs when a int literal is too large to fit in the
    /// given type.
    IntOverflow { base: u32, ty: NormalisedIntTy },

    /// When a big-int literal is not allowed in the current context.
    DisallowedBigLit,
}

pub fn int_ty_suggestion(lit: &str, base: u32, ty: IntTy) -> IntTy {
    // Get the `bigint` representation of the lit and then compute
    // the number of bits that it uses to rerpresent the type.
    let bits = BigInt::parse_bytes(lit.as_bytes(), base).unwrap().bits();
    let size = Size::from_bits(bits);

    match ty {
        IntTy::Int(_) if bits > 128 => IntTy::Big(BigIntTy::IBig),
        IntTy::UInt(_) if bits > 128 => IntTy::Big(BigIntTy::UBig),
        IntTy::Int(_) => IntTy::Int(SIntTy::from_size(size)),
        IntTy::UInt(_) => IntTy::UInt(UIntTy::from_size(size)),
        ty => ty,
    }
}

impl LitParseError {
    pub fn add_to_reporter(&self, reporter: &mut Reporter) {
        let error = reporter.error().code(HashErrorCode::InvalidLiteral);

        match self.kind {
            LitParseErrorKind::MalformedFloatLit => {
                error.title("malformed float literal").add_labelled_span(self.span.span(), "here");
            }
            LitParseErrorKind::MalformedIntLit => {
                error.title("malformed float literal").add_labelled_span(self.span.span(), "here");
            }
            LitParseErrorKind::IntOverflow { base, ty } => {
                // Compute additional note about what literal to use, if we overflow.
                let suggestion = format!(
                    " whose range is `{}..{}`, use a `{}` instead",
                    ty.normalised.signed_min(Size::ZERO),
                    ty.normalised.numeric_max(Size::ZERO),
                    int_ty_suggestion(self.contents.as_str(), base, ty.normalised)
                );

                error
                    .title(format!("literal out of range for type `{}`", ty.original))
                    .add_labelled_span(self.span.span(), "here")
                    .add_note(format!(
                        "the literal `{}` does not fit into the type `{}`{}",
                        self.contents, ty.original, suggestion
                    ));
            }
            LitParseErrorKind::DisallowedBigLit => {
                error
                    .title("big integer literals are not allowed in this context")
                    .add_labelled_span(self.span.span(), "here");
            }
        };
    }
}

impl From<num::ParseFloatError> for LitParseErrorKind {
    fn from(_: num::ParseFloatError) -> Self {
        // @@Dumbness: we can't match on what the error was
        // for some reason??? - It can either be empty or
        // invalid. Since the lexer would prevent an empty
        // float from being passed, we can assume that it
        // is "invalid".
        LitParseErrorKind::MalformedFloatLit
    }
}

/// Wrapper type to convert a [num::ParseIntError] into a
/// [LitParsingErrorKind].
struct IntError(NormalisedIntTy, u32, num::ParseIntError);

impl From<IntError> for LitParseErrorKind {
    fn from(IntError(ty, base, value): IntError) -> Self {
        match value.kind() {
            num::IntErrorKind::InvalidDigit => Self::MalformedIntLit,
            num::IntErrorKind::PosOverflow => Self::IntOverflow { base, ty },
            err => panic!("unexpected literal error: {err:?}"),
        }
    }
}

pub type LitParseResult<T> = Result<T, LitParseError>;

/// Parse a integer literal from the given [Hunk]. The integer must be
/// in the form of a decimal, binary, octal or hexadecimal literal.
///
/// @@Investigate: should we rely on stdlib for parsing integers?
pub fn parse_int_const_from_lit(
    lit: &IntLit,
    annotation: Option<IntTy>,
    ptr_size: Size,
    allow_big: bool,
) -> LitParseResult<Const> {
    let ty = NormalisedIntTy::new(annotation.unwrap_or_default(), ptr_size);
    let base: u32 = lit.base.into();

    // We have to cleanup the hunk, remove any underscores
    let mut hunk = lit.hunk.span().contents();
    hunk.retain(|c| c != '_');

    macro_rules! parse {
        ($ty:ty) => {{
            let value = <$ty>::from_str_radix(&hunk, base).map_err(|err| {
                LitParseError::new(lit.hunk, hunk, IntError(ty, base, err).into())
            })?;

            Scalar::from(value)
        }};
    }

    let lit = match ty.normalised {
        IntTy::Int(ty) => match ty {
            SIntTy::I8 => parse!(i8),
            SIntTy::I16 => parse!(i16),
            SIntTy::I32 => parse!(i32),
            SIntTy::I64 => parse!(i64),
            SIntTy::I128 => parse!(i128),
            SIntTy::ISize => unreachable!(),
        },
        IntTy::UInt(ty) => match ty {
            UIntTy::U8 => parse!(u8),
            UIntTy::U16 => parse!(u16),
            UIntTy::U32 => parse!(u32),
            UIntTy::U64 => parse!(u64),
            UIntTy::U128 => parse!(u128),
            UIntTy::USize => unreachable!(),
        },
        IntTy::Big(_) => {
            if allow_big {
                let alloc = AllocId::big_int(BigInt::parse_bytes(hunk.as_bytes(), base).unwrap());
                let constant = Const::alloc(alloc, ty.original.to_repr_ty());
                return Ok(constant);
            } else {
                return Err(LitParseError::new(
                    lit.hunk,
                    hunk,
                    LitParseErrorKind::DisallowedBigLit,
                ));
            }
        }
    };

    Ok(Const::scalar(lit, ty.original.to_repr_ty()))
}

/// Parse a float literal from the given [Hunk]. The integer must be
/// in the form of a decimal, binary, octal or hexadecimal literal.
///
/// @@Investigate: should we rely on stdlib for parsing integers?
pub fn parse_float_const_from_lit(
    lit: &FloatLit,
    annotation: Option<FloatTy>,
) -> LitParseResult<Const> {
    let ty = annotation.unwrap_or_default();

    // We have to cleanup the hunk, remove any underscores
    let mut hunk = lit.hunk.span().contents();
    hunk.retain(|c| c != '_');

    macro_rules! parse {
        ($ty:ty) => {
            hunk.parse::<$ty>().map_err(|err| LitParseError::new(lit.hunk, hunk, err.into()))?
        };
    }

    let lit = match ty {
        FloatTy::F32 => ConstKind::Scalar(parse!(f32).into()),
        FloatTy::F64 => ConstKind::Scalar(parse!(f64).into()),
    };
    Ok(Const::new(ty.to_repr_ty(), lit))
}

pub trait LitHelpers {
    /// Convert a [ast::Lit] into a [Const].
    fn to_const(&self, expected_ty: Option<ReprTyId>, ptr_size: Size) -> LitParseResult<Const>;
}

impl LitHelpers for ast::Lit {
    fn to_const(&self, expected_ty: Option<ReprTyId>, ptr_size: Size) -> LitParseResult<Const> {
        Ok(match self {
            ast::Lit::Str(ast::StrLit { data }) => Const::new(
                COMMON_REPR_TYS.str,
                ConstKind::Pair {
                    data: *data,
                    len: Scalar::try_from_uint((*data).borrow().len() as u64, ptr_size).unwrap(),
                },
            ),
            ast::Lit::Char(ast::CharLit { data }) => (*data).into(),
            ast::Lit::Int(int_lit) => {
                let annotation = expected_ty.map(IntTy::from);
                parse_int_const_from_lit(int_lit, annotation, ptr_size, false)?
            }
            ast::Lit::Float(float_lit) => {
                let annotation = expected_ty.map(FloatTy::from);
                parse_float_const_from_lit(float_lit, annotation)?
            }
            ast::Lit::Bool(value) => Const::bool(value.data),
            ast::Lit::Byte(value) => value.data.into(),
        })
    }
}
