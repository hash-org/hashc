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

use hash_reporting::{hash_error_codes::error_codes::HashErrorCode, reporter::Reporter};
use hash_source::{
    constant::{
        FloatConstant, FloatTy, IntTy, InternedFloat, InternedInt, NormalisedIntTy, SIntTy, Size,
        UIntTy,
    },
    SourceMap,
};
pub use hash_token::{FloatLitKind, IntLitKind};
use num_bigint::BigInt;

use crate::ast::{AstNodeId, FloatLit, IntLit};

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
}

pub fn int_ty_suggestion(lit: &str, base: u32, ty: IntTy) -> IntTy {
    // Get the `bigint` representation of the lit and then compute
    // the number of bits that it uses to rerpresent the type.
    let bits = BigInt::parse_bytes(lit.as_bytes(), base).unwrap().bits();
    let size = Size::from_bits(bits);

    match ty {
        IntTy::Int(_) if bits > 128 => IntTy::Int(SIntTy::IBig),
        IntTy::UInt(_) if bits > 128 => IntTy::UInt(UIntTy::UBig),
        IntTy::Int(_) => IntTy::Int(SIntTy::from_size(size)),
        IntTy::UInt(_) => IntTy::UInt(UIntTy::from_size(size)),
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
                let suggestion = if ty.original.is_bigint() {
                    format!(", use a `ibig` instead")
                } else {
                    format!(
                        "whose range is `{}..{}`, use a `{}` instead",
                        ty.normalised.numeric_min(Size::ZERO),
                        ty.normalised.numeric_max(Size::ZERO),
                        int_ty_suggestion(self.contents.as_str(), base, ty.normalised)
                    )
                };

                reporter
                    .error()
                    .title(format!("literal out of range for type `{}`", ty.original))
                    .add_labelled_span(self.span.span(), "here")
                    .add_note(format!(
                        "the literal `{}` does not fit into the type `{}`{}",
                        self.contents, ty.original, suggestion
                    ));
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
            _ => unreachable!(),
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
    sources: &SourceMap,
    ptr_size: Size,
) -> LitParseResult<InternedInt> {
    let ty = NormalisedIntTy::new(annotation.unwrap_or(IntTy::default()), ptr_size);
    let base: u32 = lit.base.into();

    // We have to cleanup the hunk, remove any underscores
    let mut hunk = sources.hunk(lit.hunk.span()).to_string();
    hunk.retain(|c| c != '_');

    macro_rules! parse {
        (@big) => {
            Box::new(BigInt::parse_bytes(hunk.as_bytes(), base).unwrap()).into()
        };
        ($ty:ty) => {
            <$ty>::from_str_radix(&hunk, base)
                .map_err(|err| LitParseError::new(lit.hunk, hunk, IntError(ty, base, err).into()))?
                .into()
        };
    }

    let lit = match ty.normalised {
        IntTy::Int(ty) => match ty {
            SIntTy::I8 => parse!(i8),
            SIntTy::I16 => parse!(i16),
            SIntTy::I32 => parse!(i32),
            SIntTy::I64 => parse!(i64),
            SIntTy::I128 => parse!(i128),
            SIntTy::IBig => parse!(@big),
            SIntTy::ISize => unreachable!(),
        },
        IntTy::UInt(ty) => match ty {
            UIntTy::U8 => parse!(u8),
            UIntTy::U16 => parse!(u16),
            UIntTy::U32 => parse!(u32),
            UIntTy::U64 => parse!(u64),
            UIntTy::U128 => parse!(u128),
            UIntTy::UBig => parse!(@big),
            UIntTy::USize => unreachable!(),
        },
    };

    Ok(InternedInt::create(lit))
}

/// Parse a float literal from the given [Hunk]. The integer must be
/// in the form of a decimal, binary, octal or hexadecimal literal.
///
/// @@Investigate: should we rely on stdlib for parsing integers?
pub fn parse_float_const_from_lit(
    lit: &FloatLit,
    annotation: Option<FloatTy>,
    sources: &SourceMap,
) -> LitParseResult<InternedFloat> {
    let ty = annotation.unwrap_or(FloatTy::default());

    // We have to cleanup the hunk, remove any underscores
    let mut hunk = sources.hunk(lit.hunk.span()).to_string();
    hunk.retain(|c| c != '_');

    macro_rules! parse {
        ($ty:ty) => {
            hunk.parse::<$ty>().map_err(|err| LitParseError::new(lit.hunk, hunk, err.into()))?
        };
    }

    let lit = match ty {
        FloatTy::F32 => FloatConstant::from(parse!(f32)),
        FloatTy::F64 => FloatConstant::from(parse!(f64)),
    };

    Ok(InternedFloat::create(lit))
}
