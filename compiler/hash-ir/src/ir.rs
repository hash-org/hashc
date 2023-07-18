//! Hash Compiler Intermediate Representation (IR) crate. This module is still
//! under construction and is subject to change.
use core::slice;
use std::{
    cmp::Ordering,
    fmt,
    iter::{self, once},
};

use hash_intrinsics::intrinsics;
use hash_source::{
    constant::{IntConstant, InternedFloat, InternedInt, InternedStr, CONSTANT_MAP},
    identifier::Identifier,
    location::{SourceLocation, Span},
    SourceId,
};
use hash_storage::{
    new_sequence_store_key_direct,
    store::{DefaultSequenceStore, SequenceStore, SequenceStoreKey, Store},
};
use hash_utils::{
    graph::dominators::Dominators,
    index_vec::{self, IndexVec},
    smallvec::{smallvec, SmallVec},
};

use crate::{
    basic_blocks::BasicBlocks,
    cast::CastKind,
    ty::{AdtId, IrTy, IrTyId, Mutability, PlaceTy, RefKind, ToIrTy, VariantIdx},
    write::WriteIr,
    IrCtx,
};

/// A specified constant value within the Hash IR. These values and their
/// shape is always known at compile-time.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Const {
    /// Nothing, it has zero size, and is associated with a particular type.
    Zero(IrTyId),

    /// Boolean constant value.
    Bool(bool),

    /// Character constant
    Char(char),

    /// Integer constant that is defined within the program source.
    Int(InternedInt),

    /// Float constant that is defined within the program source.
    Float(InternedFloat),

    /// Static strings that are to be put within the resulting binary.
    ///
    /// Dynamic strings are represented as the following struct:
    ///
    /// ```ignore
    /// str := struct(data: &raw u8, len: usize);
    /// ```
    Str(InternedStr),
}

impl From<Const> for ConstKind {
    fn from(value: Const) -> Self {
        Self::Value(value)
    }
}

impl Const {
    /// Create a [Const::Zero] with a unit type, the total zero.
    pub fn zero(ctx: &IrCtx) -> Self {
        Self::Zero(ctx.tys().common_tys.unit)
    }

    /// Check if a [Const] is "switchable", meaning that it can be used
    /// in a `match` expression and a jump table can be generated rather
    /// than emitting a equality check for each case.
    pub fn is_switchable(&self) -> bool {
        matches!(self, Self::Char(_) | Self::Int(_) | Self::Bool(_))
    }

    /// Create a new [Const] from a scalar value, with the appropriate
    /// type.
    pub fn from_scalar(value: u128, ty: IrTyId, ctx: &IrCtx) -> Self {
        ctx.map_ty(ty, |ty| match ty {
            IrTy::Int(int_ty) => {
                let value = i128::from_be_bytes(value.to_be_bytes()); // @@ByteCast.
                let interned_value = IntConstant::from_sint(value, *int_ty);
                Self::Int(CONSTANT_MAP.create_int(interned_value))
            }
            IrTy::UInt(int_ty) => {
                let interned_value = IntConstant::from_uint(value, *int_ty);
                Self::Int(CONSTANT_MAP.create_int(interned_value))
            }
            IrTy::Bool => Self::Bool(value == (true as u128)),
            IrTy::Char => unsafe { Self::Char(char::from_u32_unchecked(value as u32)) },
            _ => unreachable!(),
        })
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Zero(_) => write!(f, "()"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Char(c) => write!(f, "'{c}'"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Float(flt) => write!(f, "{flt}"),
            Self::Str(s) => write!(f, "{s:?}"),
        }
    }
}

/// Perform a value comparison between two constants.
pub fn compare_constant_values(left: Const, right: Const) -> Option<Ordering> {
    match (left, right) {
        (Const::Zero(_), Const::Zero(_)) => Some(Ordering::Equal),
        (Const::Bool(left), Const::Bool(right)) => Some(left.cmp(&right)),
        (Const::Char(left), Const::Char(right)) => Some(left.cmp(&right)),
        (Const::Int(left), Const::Int(right)) => CONSTANT_MAP
            .map_int(left, |left| CONSTANT_MAP.map_int(right, |right| left.partial_cmp(right))),
        (Const::Float(left), Const::Float(right)) => CONSTANT_MAP.map_float(left, |left| {
            CONSTANT_MAP.map_float(right, |right| left.value.partial_cmp(&right.value))
        }),
        (Const::Str(left), Const::Str(right)) => Some(left.cmp(&right)),
        _ => None,
    }
}

/// An un-evaluated constant value within the Hash IR. These values are
/// references to constant expressions that are defined outside of a
/// particular function body or are marked as `const` and will need to
/// be computed after all IR is built. A [UnevaluatedConst] refers to
/// a scope of where the value originated, and the [Identifier] that
/// is marked as `const`. However, once the new typechecking backend is
/// implemented, this is likely to change to some kind of `DefId` which
/// points to some declaration that needs to be evaluated.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct UnevaluatedConst {
    /// The name of the constant.
    pub name: Identifier,
}

/// A constant value that is used within the IR. A [ConstKind] is either
/// an actual [Const] value, or an un-evaluated reference to a constant
/// expression that comes outside of a particular function body. These
/// "unevaluated" values will be removed during IR simplification stages since
/// all of the items are inlined.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ConstKind {
    /// A constant value that is defined within the program source.
    Value(Const),
    /// A constant value that is defined within the program source, but is not
    /// evaluated yet.
    Unevaluated(UnevaluatedConst),
}

impl ConstKind {
    /// Compute the type of the [ConstKind] provided with an IR context.
    ///
    /// N.B. Computing the `ty` of a [ConstKind] will always yield a normalised
    /// type, i.e. a `usize` will be converted into a `u64` on 64-bit
    /// platforms.
    pub fn ty(&self, ctx: &IrCtx) -> IrTyId {
        match self {
            Self::Value(value) => match value {
                Const::Zero(ty) => *ty,
                Const::Bool(_) => ctx.tys().common_tys.bool,
                Const::Char(_) => ctx.tys().common_tys.char,
                Const::Int(interned_int) => {
                    CONSTANT_MAP.map_int(*interned_int, |int| int.normalised_ty().to_ir_ty(ctx))
                }
                Const::Float(interned_float) => {
                    CONSTANT_MAP.map_float(*interned_float, |float| float.ty().to_ir_ty(ctx))
                }
                Const::Str(_) => ctx.tys().common_tys.str,
            },
            Self::Unevaluated(UnevaluatedConst { .. }) => {
                // @@Todo: This will be implemented when constants are clearly
                // associated with a definition ID making it easy to look them
                // up within the context.
                todo!()
            }
        }
    }
}

impl From<ConstKind> for Operand {
    fn from(constant: ConstKind) -> Self {
        Self::Const(constant)
    }
}

impl From<ConstKind> for RValue {
    fn from(constant: ConstKind) -> Self {
        Self::Use(Operand::Const(constant))
    }
}

impl fmt::Display for ConstKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(value) => write!(f, "{value}"),
            Self::Unevaluated(UnevaluatedConst { name }) => write!(f, "<unevaluated> {name}"),
        }
    }
}

/// A collection of operations that are constant and must run during the
/// compilation stage.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ConstOp {
    /// Yields the size of the given type.
    SizeOf,
    /// Yields the word alignment of the type.
    AlignOf,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UnaryOp {
    // Bitwise logical inversion
    BitNot,
    /// Logical inversion.
    Not,
    /// The operator '-' for negation
    Neg,
}

impl From<intrinsics::UnOp> for UnaryOp {
    fn from(value: intrinsics::UnOp) -> Self {
        use intrinsics::UnOp::*;
        match value {
            BitNot => Self::BitNot,
            Not => Self::Not,
            Neg => Self::Neg,
        }
    }
}

/// Represents a binary operation that is short-circuiting. These
/// operations are only valid on boolean values.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LogicalBinOp {
    /// '||'
    Or,
    /// '&&'
    And,
}

impl From<intrinsics::ShortCircuitBinOp> for LogicalBinOp {
    fn from(value: intrinsics::ShortCircuitBinOp) -> Self {
        use intrinsics::ShortCircuitBinOp::*;

        match value {
            And => Self::And,
            Or => Self::Or,
        }
    }
}

/// Binary operations on [RValue]s that are typed as primitive, or have
/// `intrinsic` implementations defined for them. Any time that does not
/// implement these binary operations by default will create a function
/// call to the implementation of the binary operation.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BinOp {
    /// '=='
    Eq,
    /// '!='
    Neq,
    /// '|'
    BitOr,
    /// '&'
    BitAnd,
    /// '^'
    BitXor,
    /// '^^'
    Exp,
    /// '>'
    Gt,
    /// '>='
    GtEq,
    /// '<'
    Lt,
    /// '<='
    LtEq,
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

impl BinOp {
    /// Returns whether the [BinOp] can be "checked".
    pub fn is_checkable(&self) -> bool {
        matches!(self, Self::Add | Self::Sub | Self::Mul | Self::Shl | Self::Shr)
    }

    /// Check if the [BinOp] is a comparator.
    pub fn is_comparator(&self) -> bool {
        matches!(self, Self::Eq | Self::Neq | Self::Gt | Self::GtEq | Self::Lt | Self::LtEq)
    }

    /// Compute the type of [BinOp] operator when applied to
    /// a particular [IrTy].
    pub fn ty(&self, ctx: &IrCtx, lhs: IrTyId, rhs: IrTyId) -> IrTyId {
        match self {
            BinOp::BitOr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::Div
            | BinOp::Sub
            | BinOp::Mod
            | BinOp::Add
            | BinOp::Mul
            | BinOp::Exp => {
                // Both `lhs` and `rhs` should be of the same type...
                debug_assert_eq!(
                    lhs,
                    rhs,
                    "binary op types for `{:?}` should be equal, but got: lhs: `{}`, rhs: `{}`",
                    self,
                    lhs.for_fmt(ctx),
                    rhs.for_fmt(ctx)
                );
                lhs
            }

            // Always the `lhs`, but `lhs` and `rhs` can be different types.
            BinOp::Shr | BinOp::Shl => lhs,

            // Comparisons
            BinOp::Eq | BinOp::Neq | BinOp::Gt | BinOp::GtEq | BinOp::Lt | BinOp::LtEq => {
                ctx.tys().common_tys.bool
            }
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Eq => write!(f, "=="),
            BinOp::Neq => write!(f, "!="),
            BinOp::BitOr => write!(f, "|"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitXor => write!(f, "^"),
            BinOp::Exp => write!(f, "**"),
            BinOp::Gt => write!(f, ">"),
            BinOp::GtEq => write!(f, ">="),
            BinOp::Lt => write!(f, "<"),
            BinOp::LtEq => write!(f, "<="),
            BinOp::Shr => write!(f, ">>"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "%"),
        }
    }
}

impl From<intrinsics::EndoBinOp> for BinOp {
    fn from(value: intrinsics::EndoBinOp) -> Self {
        use intrinsics::EndoBinOp::*;

        match value {
            BitOr => Self::BitOr,
            BitAnd => Self::BitAnd,
            BitXor => Self::BitXor,
            Exp => Self::Exp,
            Shr => Self::Shr,
            Shl => Self::Shl,
            Add => Self::Add,
            Sub => Self::Sub,
            Mul => Self::Mul,
            Div => Self::Div,
            Mod => Self::Mod,
        }
    }
}

impl From<intrinsics::BoolBinOp> for BinOp {
    fn from(value: intrinsics::BoolBinOp) -> Self {
        use intrinsics::BoolBinOp::*;

        match value {
            EqEq => Self::Eq,
            NotEq => Self::Neq,
            Gt => Self::Gt,
            GtEq => Self::GtEq,
            Lt => Self::Lt,
            LtEq => Self::LtEq,
        }
    }
}

/// Describes what kind of [Local] something is, whether it
/// is generated by the compiler, or a user variable.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LocalKind {
    /// The return local place of a function.
    Return,

    /// An argument to the function body.
    Arg,

    /// A local variable that is defined within the function body
    /// by the user.
    Var,

    /// A local variable that is generated as a temporary variable
    /// during the lowering process.
    Temp,
}

/// Essentially a register for a value, the local declaration
/// is used to store some data within the function body, it contains
/// an associated [Mutability], and [IrTy], as well as a name if the
/// information is available.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalDecl {
    /// Mutability of the local.
    pub mutability: Mutability,

    /// The type of the local.
    pub ty: IrTyId,

    /// An optional name for the local, this is used for building the
    /// IR and for printing the IR (in order to label which local associates
    /// with which variable and scope).
    pub name: Option<Identifier>,

    /// Whether the local declaration is an auxiliary. An auxiliary local
    /// declaration is used to store a temporary result of an operation that
    /// is used to store the result of expressions that return **nothing**,
    /// or temporary variables that are needed during the lowering process to
    /// lower edge case expressions. Auxiliary local declarations will be
    /// eliminated during the lowering process, when the IR undergoes
    /// optimisations.
    auxiliary: bool,
}

impl LocalDecl {
    /// Create a new [LocalDecl].
    pub fn new(name: Identifier, mutability: Mutability, ty: IrTyId) -> Self {
        Self { mutability, ty, name: Some(name), auxiliary: false }
    }

    /// Create a new mutable [LocalDecl].
    pub fn new_mutable(name: Identifier, ty: IrTyId) -> Self {
        Self::new(name, Mutability::Mutable, ty)
    }

    /// Create a new immutable [LocalDecl].
    pub fn new_immutable(name: Identifier, ty: IrTyId) -> Self {
        Self::new(name, Mutability::Immutable, ty)
    }

    pub fn new_auxiliary(ty: IrTyId, mutability: Mutability) -> Self {
        Self { mutability, ty, name: None, auxiliary: true }
    }

    /// Returns the [IrTyId] of the local.
    pub fn ty(&self) -> IrTyId {
        self.ty
    }

    /// Returns the [Mutability] of the local.
    pub fn mutability(&self) -> Mutability {
        self.mutability
    }

    /// Returns the name of the local.
    pub fn name(&self) -> Option<Identifier> {
        self.name
    }

    /// Is the [Local] an auxiliary?
    pub fn auxiliary(&self) -> bool {
        self.auxiliary
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PlaceProjection {
    /// When we want to narrow down the union type to some specific
    /// variant.
    Downcast(VariantIdx),
    /// A reference to a specific field within the place, at this stage they
    /// are represented as indexes into the field store of the place type.
    Field(usize),
    /// Take the index of some specific place, the index does not need to be
    /// constant
    Index(Local),

    /// This kind of index is used when slice patterns are specified, we know
    /// the exact location of the offset that this is referencing. Here are
    /// some examples of where the element `A` is referenced:
    /// ```ignore
    /// [A, _, .., _, _] => { offset: 0, min_length: 4, from_end: false }
    /// [_, _, .., _, A] => { offset: 0, min_length: 4, from_end: true }
    /// [_, _, .., A, _] => { offset: 1, min_length: 4, from_end: true }
    /// [_, A, .., _, _] => { offset: 1, min_length: 4, from_end: false }
    /// ```
    ConstantIndex {
        /// The index of the constant index.
        offset: usize,

        /// If the index is referencing from the end of the slice.
        from_end: bool,

        /// The minimum length of the slice that this is referencing.
        min_length: usize,
    },

    /// A sub-slice projection references a sub-slice of the original slice.
    /// This is generated from slice patterns that associate a sub-slice with
    /// a variable, for example:
    /// ```ignore
    /// [_, _, ...x, _]
    /// [_, ...x, _, _]
    /// ```
    SubSlice {
        /// The initial offset of where the slice is referencing
        /// from.
        from: usize,

        /// To which index the slice is referencing to.
        to: usize,

        /// If this is referring to from the end of a slice. This determines
        /// from where `to` counts from, whether the start or the end of the
        /// slice/list.
        from_end: bool,
    },

    /// We want to dereference the place
    Deref,
}

/// A [Place] describes a memory location that is currently
/// within the function of the body backed by a [Local].
///
/// Additionally, [Place]s allow for projections to be applied
/// to a place in order to specify a location within the [Local],
/// i.e. an array index, a field access, etc.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Place {
    /// The original place of where this is referring to.
    pub local: Local,

    /// Any projections that are applied onto the `local` in
    /// order to specify an exact location within the local.
    pub projections: ProjectionId,
}

impl Place {
    /// Create a [Place] that points to the return `place` of a lowered  body.
    pub fn return_place(ctx: &IrCtx) -> Self {
        Self { local: RETURN_PLACE, projections: ctx.projections().create_empty() }
    }

    /// Deduce the type of the [Place] from the [IrCtx] and the local
    /// declarations.
    pub fn ty(&self, locals: &LocalDecls, ctx: &IrCtx) -> IrTyId {
        PlaceTy::from_place(*self, locals, ctx).ty
    }

    /// Create a new [Place] from a [Local] with no projections.
    pub fn from_local(local: Local, ctx: &IrCtx) -> Self {
        Self { local, projections: ctx.projections().create_empty() }
    }

    /// Create a new [Place] from an existing [Place] whilst also
    /// applying a [`PlaceProjection::Deref`] on the old one.
    pub fn deref(&self, ctx: &IrCtx) -> Self {
        let projections = ctx.projections().get_vec(self.projections);

        Self {
            local: self.local,
            projections: ctx.projections().create_from_iter_fast(
                projections.iter().copied().chain(once(PlaceProjection::Deref)),
            ),
        }
    }

    /// Create a new [Place] from an existing place whilst also
    /// applying a a [PlaceProjection::Field] on the old one.
    pub fn field(&self, field: usize, ctx: &IrCtx) -> Self {
        let projections = ctx.projections().get_vec(self.projections);

        Self {
            local: self.local,
            projections: ctx.projections().create_from_iter_fast(
                projections.iter().copied().chain(once(PlaceProjection::Field(field))),
            ),
        }
    }

    /// Examine a [Place] as a [Local] with the condition that the
    /// [Place] has no projections.
    pub fn as_local(&self) -> Option<Local> {
        if self.projections.is_empty() {
            Some(self.local)
        } else {
            None
        }
    }
}

impl From<Place> for Operand {
    fn from(value: Place) -> Self {
        Self::Place(value)
    }
}

impl From<Place> for RValue {
    fn from(value: Place) -> Self {
        Self::Use(Operand::Place(value))
    }
}

/// [AggregateKind] represent an initialisation process of a particular
/// structure be it a tuple, array, struct, etc.
///
/// @@Todo: decide whether to keep this, or to stick with just immediately
/// lowering items as setting values for each field within the aggregate
/// data structure (as it). If we stick with initially generating
/// aggregates, then we will have to de-aggregate them before lowering
/// to bytecode/llvm.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AggregateKind {
    /// A tuple value initialisation.
    Tuple(AdtId),

    /// An array aggregate kind initialisation. The type of the array
    /// is stored here. Additionally, the length of the array is recorded
    /// in [`IrTy::Array`] data, and can be derived from the type.
    ///
    /// N.B. This type is the type of the array, not the type of the
    /// elements within the array.
    Array(IrTyId),

    /// Enum aggregate kind, this is used to represent an initialisation
    /// of an enum variant with the specified variant index.
    Enum(AdtId, VariantIdx),

    /// Struct aggregate kind, this is used to represent a struct
    /// initialisation.
    Struct(AdtId),
}

impl AggregateKind {
    /// Check if the [AggregateKind] represents an ADT.
    pub fn is_adt(&self) -> bool {
        !matches!(self, AggregateKind::Array(_))
    }

    /// Get the [AdtId] of the [AggregateKind] if it is an ADT.
    ///
    /// N.B. This will panic if the [AggregateKind] is not an ADT.
    pub fn adt_id(&self) -> AdtId {
        match self {
            AggregateKind::Tuple(id) | AggregateKind::Enum(id, _) | AggregateKind::Struct(id) => {
                *id
            }
            AggregateKind::Array(_) => panic!("cannot get adt_id of non-adt aggregate kind"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Operand {
    /// A constant value.
    Const(ConstKind),

    /// A place that is being used.
    Place(Place),
}

impl Operand {
    /// Compute the type of the [Operand] based on
    /// the IrCtx.
    pub fn ty(&self, locals: &LocalDecls, ctx: &IrCtx) -> IrTyId {
        match self {
            Operand::Const(kind) => kind.ty(ctx),
            Operand::Place(place) => place.ty(locals, ctx),
        }
    }
}

impl From<Operand> for RValue {
    fn from(value: Operand) -> Self {
        Self::Use(value)
    }
}

/// The representation of values that occur on the right-hand side of an
/// assignment.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum RValue {
    /// Some value that is being used. Could be a constant or a place.
    Use(Operand),

    /// Compiler intrinsic operation, this will be computed in place and
    /// replaced by a constant.
    ///
    /// @@Future: maybe in the future this should be replaced by a compile-time
    /// API variant which will just run some kind of operation and return the
    /// constant.
    ConstOp(ConstOp, IrTyId),

    /// A unary expression with a unary operator.
    UnaryOp(UnaryOp, Operand),

    /// A binary expression with a binary operator and two inner expressions.
    BinaryOp(BinOp, Box<(Operand, Operand)>),

    /// A binary expression that is checked. The only difference between this
    /// and a normal [RValue::BinaryOp] is that this will return a boolean and
    /// the result of the operation in the form of `(T, bool)`. The boolean
    /// flag denotes whether the operation violated the check...
    CheckedBinaryOp(BinOp, Box<(Operand, Operand)>),

    /// A cast operation, this will convert the value of the operand to the
    /// specified type.
    Cast(CastKind, Operand, IrTyId),

    /// Compute the `length` of a place, yielding a `usize`.
    ///
    /// Any `place` that is not an array or slice, is not a valid [RValue].
    Len(Place),

    /// An expression which is taking the address of another expression with an
    /// mutability modifier e.g. `&mut x`.
    Ref(Mutability, Place, RefKind),
    /// Used for initialising structs, tuples and other aggregate
    /// data structures
    Aggregate(AggregateKind, Vec<Operand>),
    /// Compute the discriminant of a [Place], this is essentially checking
    /// which variant a union is. For types that don't have a discriminant
    /// (non-union types ) this will return the value as 0.
    Discriminant(Place),
}

impl RValue {
    /// Check if an [RValue] is a constant.
    pub fn is_const(&self) -> bool {
        matches!(self, RValue::Use(Operand::Const(_)))
    }

    /// Convert the RValue into a constant, having previously
    /// checked that it is a constant.
    pub fn as_const(&self) -> ConstKind {
        match self {
            RValue::Use(Operand::Const(c)) => *c,
            rvalue => unreachable!("Expected a constant, got {:?}", rvalue),
        }
    }

    /// Get the [IrTy] of the [RValue].
    pub fn ty(&self, locals: &LocalDecls, ctx: &IrCtx) -> IrTyId {
        match self {
            RValue::Use(operand) => operand.ty(locals, ctx),
            RValue::ConstOp(ConstOp::AlignOf | ConstOp::SizeOf, _) => ctx.tys().common_tys.usize,
            RValue::UnaryOp(_, operand) => operand.ty(locals, ctx),
            RValue::BinaryOp(op, box (lhs, rhs)) => {
                op.ty(ctx, lhs.ty(locals, ctx), rhs.ty(locals, ctx))
            }
            RValue::CheckedBinaryOp(op, box (lhs, rhs)) => {
                let ty = op.ty(ctx, lhs.ty(locals, ctx), rhs.ty(locals, ctx));
                ctx.tys().create(IrTy::tuple(&[ty, ctx.tys().common_tys.bool]))
            }
            RValue::Cast(_, _, ty) => *ty,
            RValue::Len(_) => ctx.tys().common_tys.usize,
            RValue::Ref(mutability, place, kind) => {
                let ty = place.ty(locals, ctx);
                ctx.tys().create(IrTy::Ref(ty, *mutability, *kind))
            }
            RValue::Aggregate(kind, _) => match kind {
                AggregateKind::Enum(id, _)
                | AggregateKind::Struct(id)
                | AggregateKind::Tuple(id) => ctx.tys().create(IrTy::Adt(*id)),
                AggregateKind::Array(ty) => *ty,
            },
            RValue::Discriminant(place) => {
                let ty = place.ty(locals, ctx);

                // @@Safety: this does not create any new types, and thus
                // we can map_fast over the types.
                ctx.map_ty(ty, |ty| ty.discriminant_ty(ctx))
            }
        }
    }
}

impl From<Const> for RValue {
    fn from(value: Const) -> Self {
        Self::Use(Operand::Const(ConstKind::Value(value)))
    }
}

/// A defined statement within the IR
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum StatementKind {
    /// Filler kind when expressions are optimised out or removed for other
    /// reasons.
    Nop,

    /// An assignment expression, a right hand-side expression is assigned to a
    /// left hand-side pattern e.g. `x = 2`
    Assign(Place, RValue),

    /// Set the discriminant on a particular place, this is used to concretely
    /// specify what the discriminant of a particular enum/union type is.
    Discriminate(Place, VariantIdx),

    /// A statement which is used to denote that a [Local] is now "live"
    /// in terms of the live interval.
    Live(Local),

    /// A statement which is used to denote that a [Local] is now "dead"
    /// in terms of live interval.
    Dead(Local),
}

/// A [Statement] is a intermediate transformation step within a [BasicBlock].
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Statement {
    /// The kind of [Statement] that it is.
    pub kind: StatementKind,

    /// The [Span] of the statement, relative to the [Body]
    /// `source-id`. This is mostly used for error reporting or
    /// generating debug information at later stages of lowering
    /// beyond the IR.
    pub span: Span,
}

/// The kind of assert terminator that it is.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AssertKind {
    /// A Division by zero assertion.
    DivisionByZero { operand: Operand },

    /// Occurs when an attempt to take the remainder of some operand with zero.
    RemainderByZero { operand: Operand },

    /// Performing an arithmetic operation has caused the operation to overflow
    Overflow {
        /// The operation that is being performed.
        op: BinOp,

        /// The left hand-side operand in the operation.
        lhs: Operand,

        /// The right hand-side operand in the operation.
        rhs: Operand,
    },

    /// Performing an arithmetic operation has caused the operation to overflow
    /// whilst subtracting or terms that are signed
    NegativeOverflow { operand: Operand },

    /// Bounds check assertion.
    BoundsCheck {
        /// The length of the array that is being checked.
        len: Operand,

        /// The index that is being checked.
        index: Operand,
    },
}

impl AssertKind {
    /// Get a general message of what the [AssertKind] is
    /// checking. This is used to generate a readable message
    /// within the executable for when the assert is triggered.
    pub fn message(&self) -> &'static str {
        match self {
            AssertKind::Overflow { op: BinOp::Add, .. } => "attempt to add with overflow\n",
            AssertKind::Overflow { op: BinOp::Sub, .. } => "attempt to subtract with overflow\n",
            AssertKind::Overflow { op: BinOp::Mul, .. } => "attempt to multiply with overflow\n",
            AssertKind::Overflow { op: BinOp::Div, .. } => "attempt to divide with overflow\n",
            AssertKind::Overflow { op: BinOp::Mod, .. } => {
                "attempt to calculate the remainder with overflow"
            }
            AssertKind::Overflow { op: BinOp::Shl, .. } => "attempt to shift left with overflow\n",
            AssertKind::Overflow { op: BinOp::Shr, .. } => "attempt to shift right with overflow\n",
            AssertKind::Overflow { op, .. } => panic!("unexpected overflow operator `{op}`\n"),
            AssertKind::DivisionByZero { .. } => "attempt to divide by zero\n",
            AssertKind::RemainderByZero { .. } => {
                "attempt to take remainder with a divisor of zero\n"
            }
            AssertKind::NegativeOverflow { .. } => "attempt to negate with overflow\n",
            AssertKind::BoundsCheck { .. } => "attempt to index array out of bounds\n",
        }
    }
}

/// [Terminator] statements are those that affect control
/// flow. All [BasicBlock]s must be terminated with a
/// [Terminator] statement that instructs where the program
/// flow is to go next.
#[derive(Debug, PartialEq, Eq)]
pub struct Terminator {
    /// The kind of [Terminator] that it is.
    pub kind: TerminatorKind,

    /// The [Span] of the statement, relative to the [Body]
    /// `source-id`. This is mostly used for error reporting or
    /// generating debug information at later stages of lowering
    /// beyond the IR.
    pub span: Span,
}

pub type Successors<'a> = impl Iterator<Item = BasicBlock> + 'a;

pub type SuccessorsMut<'a> =
    iter::Chain<std::option::IntoIter<&'a mut BasicBlock>, slice::IterMut<'a, BasicBlock>>;

impl Terminator {
    /// Get all of the successors of a [Terminator].
    pub fn successors(&self) -> Successors<'_> {
        match self.kind {
            TerminatorKind::Goto(target)
            | TerminatorKind::Call { target: Some(target), .. }
            | TerminatorKind::Assert { target, .. } => {
                Some(target).into_iter().chain([].iter().copied())
            }
            TerminatorKind::Switch { ref targets, .. } => {
                targets.otherwise.into_iter().chain(targets.targets.iter().copied())
            }
            _ => None.into_iter().chain([].iter().copied()),
        }
    }

    /// Get all of the successors of a [Terminator] as mutable references.
    pub fn successors_mut(&mut self) -> SuccessorsMut<'_> {
        match self.kind {
            TerminatorKind::Goto(ref mut target)
            | TerminatorKind::Call { target: Some(ref mut target), .. }
            | TerminatorKind::Assert { ref mut target, .. } => {
                Some(target).into_iter().chain(&mut [])
            }
            TerminatorKind::Switch { ref mut targets, .. } => {
                targets.otherwise.as_mut().into_iter().chain(targets.targets.iter_mut())
            }
            _ => None.into_iter().chain(&mut []),
        }
    }

    /// Function that replaces a specified successor with another
    /// [BasicBlock].
    pub fn replace_edge(&mut self, successor: BasicBlock, replacement: BasicBlock) {
        match self.kind {
            TerminatorKind::Goto(target) if target == successor => {
                self.kind = TerminatorKind::Goto(replacement)
            }
            TerminatorKind::Switch { ref mut targets, .. } => {
                targets.replace_edge(successor, replacement)
            }
            TerminatorKind::Call { target: Some(ref mut target), .. } if *target == successor => {
                *target = replacement;
            }
            TerminatorKind::Assert { ref mut target, .. } => {
                *target = replacement;
            }
            // All other edges cannot be replaced
            _ => {}
        }
    }
}

/// Struct that represents all of the targets that a [TerminatorKind::Switch]
/// can jump to. This also defines some useful methods on the block to iterate
/// over all the targets, etc.
#[derive(Debug, PartialEq, Eq)]
pub struct SwitchTargets {
    /// The values are stored as an [u128] because we only deal with **small**
    /// integral types, for larger integer values, we default to using `Eq`
    /// check. Since the value is stored as an [u128], this is nonsensical
    /// when it comes using these values, which is why a **bias** needs to
    /// be applied before properly reading the value which can be derived
    /// from the integral type that is being matched on.
    ///
    /// N.B. All values within the table are unique, there cannot be multiple
    /// targets for the same value.
    ///
    /// @@Todo: It would be nice to have a unified `table`, but ~~fucking~~
    /// iterators!
    pub values: SmallVec<[u128; 1]>,

    /// The jump table, contains corresponding values to *jump* on and the
    /// location of where the jump goes to. The index within `values` is the
    /// relative jump location that is used when performing the jump.
    pub targets: SmallVec<[BasicBlock; 1]>,

    /// This is the type that is used to represent the values within
    /// the jump table. This will be used to create the appropriate
    /// value when actually reading from the jump table.
    ///
    /// N.B. This must be an integral type, `int`, `bool`, `char`.
    pub ty: IrTyId,

    /// If none of the corresponding values match, then jump to this block. This
    /// is set to [None] if the switch is exhaustive.
    pub otherwise: Option<BasicBlock>,
}

impl SwitchTargets {
    /// Create a new [SwitchTargets] with the specified jump table and
    /// an optional otherwise block.
    pub fn new(
        targets: impl Iterator<Item = (u128, BasicBlock)>,
        ty: IrTyId,
        otherwise: Option<BasicBlock>,
    ) -> Self {
        let (values, targets): (SmallVec<[_; 1]>, SmallVec<[_; 1]>) = targets.unzip();

        Self { values, targets, ty, otherwise }
    }

    /// Check if there is an `otherwise` block.
    pub fn has_otherwise(&self) -> bool {
        self.otherwise.is_some()
    }

    /// Get the `otherwise` block to jump to unconditionally.
    pub fn otherwise(&self) -> BasicBlock {
        self.otherwise.unwrap()
    }

    /// Iterate all of the associated targets.
    pub fn iter_targets(&self) -> impl Iterator<Item = BasicBlock> + '_ {
        self.otherwise.into_iter().chain(self.targets.iter().copied())
    }

    /// Replace a successor with another [BasicBlock].
    pub fn replace_edge(&mut self, successor: BasicBlock, replacement: BasicBlock) {
        for target in self.targets.iter_mut() {
            if *target == successor {
                *target = replacement;
            }
        }

        if let Some(otherwise) = self.otherwise {
            if otherwise == successor {
                self.otherwise = Some(replacement);
            }
        }
    }

    pub fn iter(&self) -> SwitchTargetsIter<'_> {
        SwitchTargetsIter { inner: iter::zip(&self.values, &self.targets) }
    }

    /// Find the target for a specific value, if it exists.
    pub fn corresponding_target(&self, value: u128) -> BasicBlock {
        self.values
            .iter()
            .position(|v| *v == value)
            .map(|pos| self.targets[pos])
            .unwrap_or_else(|| self.otherwise())
    }
}

pub struct SwitchTargetsIter<'a> {
    inner: iter::Zip<slice::Iter<'a, u128>, slice::Iter<'a, BasicBlock>>,
}

impl<'a> Iterator for SwitchTargetsIter<'a> {
    type Item = (u128, BasicBlock);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(val, bb)| (*val, *bb))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl ExactSizeIterator for SwitchTargetsIter<'_> {}

/// The kind of [Terminator] that it is.
///
/// @@Future: does this need an `Intrinsic(...)` variant for substituting
/// expressions for intrinsic functions?
#[derive(Debug, PartialEq, Eq)]
pub enum TerminatorKind {
    /// A simple go to block directive.
    Goto(BasicBlock),

    /// Return from the parent function
    Return,

    /// Perform a function call
    Call {
        /// The function that is being called
        op: Operand,

        /// Arguments to the function, later we might need to distinguish
        /// whether these are move or copy arguments.
        args: Vec<Operand>,

        /// Destination of the result...
        destination: Place,

        /// Where to return after completing the call
        target: Option<BasicBlock>,
    },

    /// Denotes that this terminator should never be reached, doing so will
    /// break IR control flow invariants.
    Unreachable,

    /// Essentially a `jump if <0> to <1> else go to <2>`. The last argument is
    /// the `otherwise` condition.
    Switch {
        /// The value to use when comparing against the cases.
        value: Operand,

        /// All of the targets that are defined for the particular switch.
        targets: SwitchTargets,
    },

    /// This terminator is used to verify that the result of some operation has
    /// no violated a some condition. Usually, this is combined with operations
    /// that perform a `checked` operation and sets some flag in the form of a
    /// [Operand] and expects it to be equal to the `expected` boolean value.
    Assert {
        /// The condition that is to be checked against the `expected value
        condition: Operand,
        /// What the assert terminator expects the `condition` to be
        expected: bool,
        /// What condition is the assert verifying that it holds
        kind: AssertKind,
        /// If the `condition` was verified, this is where the program should
        /// continue to.
        target: BasicBlock,
    },
}

impl TerminatorKind {
    /// Utility to create a [TerminatorKind::Switch] which emulates the
    /// behaviour of an `if` branch where the `true` branch is the
    /// `true_block` and the `false` branch is the `false_block`.
    pub fn make_if(
        value: Operand,
        true_block: BasicBlock,
        false_block: BasicBlock,
        ctx: &IrCtx,
    ) -> Self {
        let targets = SwitchTargets::new(
            std::iter::once((false.into(), false_block)),
            ctx.tys().common_tys.bool,
            Some(true_block),
        );

        TerminatorKind::Switch { value, targets }
    }
}

/// The contents of a [BasicBlock], the statements of the block, and a
/// terminator. Initially, the `terminator` begins as [None], and will
/// be set when the lowering process is completed.
///
/// N.B. It is an invariant for a [BasicBlock] to not have a terminator
/// once it has been built.
#[derive(Debug, PartialEq, Eq)]
pub struct BasicBlockData {
    /// The statements that the block has.
    pub statements: Vec<Statement>,
    /// An optional terminating statement, where the block goes
    /// after finishing execution of these statements. When a
    /// [BasicBlock] is finalised, it must always have a terminator.
    pub terminator: Option<Terminator>,
}

impl BasicBlockData {
    /// Create a new [BasicBlockData] with no statements and a provided
    /// `terminator`. It is assumed that the statements are to be added
    /// later to the block.
    pub fn new(terminator: Option<Terminator>) -> Self {
        Self { statements: vec![], terminator }
    }

    /// Get a reference to the terminator of this [BasicBlockData].
    pub fn terminator(&self) -> &Terminator {
        self.terminator.as_ref().expect("expected terminator on block")
    }

    /// Get a mutable reference to the terminator of this [BasicBlockData].
    pub fn terminator_mut(&mut self) -> &mut Terminator {
        self.terminator.as_mut().expect("expected terminator on block")
    }

    /// Return a list of all of the successors of this [BasicBlock].
    pub fn successors(&self) -> SmallVec<[BasicBlock; 4]> {
        match &self.terminator {
            Some(terminator) => terminator.successors().collect(),
            None => smallvec![],
        }
    }

    /// Check if the [BasicBlockData] is empty, i.e. has no statements and
    /// the terminator is of kind [TerminatorKind::Unreachable].
    pub fn is_empty_and_unreachable(&self) -> bool {
        self.statements.is_empty()
            && self.terminator.as_ref().map_or(false, |t| t.kind == TerminatorKind::Unreachable)
    }
}

index_vec::define_index_type! {
    /// Index for [BasicBlockData] stores within generated [Body]s.
    pub struct BasicBlock = u32;

    MAX_INDEX = u32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "bb{}";
}

/// `0` is used as the starting block of any lowered body.
pub const START_BLOCK: BasicBlock = BasicBlock { _raw: 0 };

impl BasicBlock {
    /// Create an [IrRef] to the start of this [BasicBlock].
    pub fn ref_to_start(self) -> IrRef {
        IrRef { block: self, index: 0 }
    }
}

index_vec::define_index_type! {
    /// Index for [LocalDecl] stores within generated [Body]s.
    pub struct Local = u32;

    MAX_INDEX = u32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "_{}";
}

/// `0` is used as the return place of any lowered body.
pub const RETURN_PLACE: Local = Local { _raw: 0 };

/// The origin of a lowered function body.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BodySource {
    /// Constant block
    Const,
    /// The item is a normal function.
    Item,
}

impl fmt::Display for BodySource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BodySource::Const => write!(f, "constant block"),
            BodySource::Item => write!(f, "function"),
        }
    }
}

/// All of the [LocalDecl]s that are used within a [Body].
pub type LocalDecls = IndexVec<Local, LocalDecl>;

/// Represents a lowered IR body, which stores the created declarations,
/// blocks and various other metadata about the lowered body.
pub struct Body {
    /// The blocks that the function is represented with
    pub basic_blocks: BasicBlocks,

    /// Declarations of local variables:
    ///
    /// - The first local is used a representation of the function return value
    ///   if any.
    ///
    /// - the next `arg_count` locals are used to represent the assigning of
    ///   function arguments.
    ///
    /// - the remaining are temporaries that are used within the function.
    pub declarations: LocalDecls,

    /// Constants that need to be resolved after IR building and pre-codegen.
    pub needed_constants: Vec<UnevaluatedConst>,

    /// Information that is derived when the body in being
    /// lowered.
    pub info: BodyInfo,

    /// Number of arguments to the function
    pub arg_count: usize,

    /// The location of the function
    span: Span,

    /// The id of the source of where this body originates from.
    pub source_id: SourceId,

    /// Whether the IR Body that is generated should be printed
    /// when the generation process is finalised.
    dump: bool,
}

impl Body {
    /// Create a new [Body] with the given `name`, `arg_count`, `source_id` and
    /// `span`.
    pub fn new(
        blocks: IndexVec<BasicBlock, BasicBlockData>,
        declarations: IndexVec<Local, LocalDecl>,
        info: BodyInfo,
        arg_count: usize,
        span: Span,
        source_id: SourceId,
    ) -> Self {
        Self {
            needed_constants: vec![],
            basic_blocks: BasicBlocks::new(blocks),
            info,
            declarations,
            arg_count,
            span,
            source_id,
            dump: false,
        }
    }

    /// Get a reference to the stored basic blocks of this
    /// [Body].
    pub fn blocks(&self) -> &IndexVec<BasicBlock, BasicBlockData> {
        &self.basic_blocks.blocks
    }

    /// Compute the [LocalKind] of a [Local] in this [Body].
    pub fn local_kind(&self, local: Local) -> LocalKind {
        if local == RETURN_PLACE {
            LocalKind::Return
        } else if local.index() < self.arg_count + 1 {
            LocalKind::Arg
        } else if self.declarations[local].auxiliary || self.declarations[local].name.is_none() {
            LocalKind::Temp
        } else {
            LocalKind::Var
        }
    }

    /// Returns an iterator over all function arguments.
    #[inline]
    pub fn args_iter(&self) -> impl Iterator<Item = Local> + ExactSizeIterator {
        (1..self.arg_count + 1).map(Local::new)
    }

    /// Returns an iterator over all variables and temporaries. This
    /// excludes the return place and function arguments.
    #[inline]
    pub fn vars_iter(&self) -> impl Iterator<Item = Local> + ExactSizeIterator {
        (self.arg_count + 1..self.declarations.len()).map(Local::new)
    }

    /// Set the `dump` flag to `true` so that the IR Body that is generated
    /// will be printed when the generation process is finalised.
    pub fn mark_to_dump(&mut self) {
        self.dump = true;
    }

    /// Check if the [Body] needs to be dumped.
    pub fn needs_dumping(&self) -> bool {
        self.dump
    }

    /// Get the [SourceLocation] for the [Body]
    pub fn location(&self) -> SourceLocation {
        SourceLocation { id: self.source_id, span: self.span }
    }

    /// Get the [BodyInfo] for the [Body]
    pub fn info(&self) -> &BodyInfo {
        &self.info
    }
}

/// This struct contains additional metadata about the body that was lowered,
/// namely the associated name with the body that is derived from the
/// declaration that it was lowered from, the type of the body that is computed
/// during lowering, etc.
///
/// This type exists since it is expected that this information is constructed
/// during lowering and might not be initially available, so most of the fields
/// are wrapped in a [Option], however any access method on the field
/// **expects** that the value was computed.
pub struct BodyInfo {
    /// The name of the body that was lowered. This is determined from the
    /// beginning of the lowering process.
    pub name: Identifier,

    /// The source of the body that was lowered, either an item, or a constant.
    pub source: BodySource,

    /// The type of the body that was lowered
    ty: Option<IrTyId>,
}

impl BodyInfo {
    /// Create a new [BodyInfo] with the given `name`.
    pub fn new(name: Identifier, source: BodySource) -> Self {
        Self { name, ty: None, source }
    }

    /// Set the type of the body that was lowered.
    pub fn set_ty(&mut self, ty: IrTyId) {
        self.ty = Some(ty);
    }

    /// Get the type of the body that was lowered.
    pub fn ty(&self) -> IrTyId {
        self.ty.expect("body type was not computed")
    }

    /// Get the name of the body that was lowered.
    pub fn name(&self) -> Identifier {
        self.name
    }

    /// Get the [BodySource] for [Body] that was lowered.
    pub fn source(&self) -> BodySource {
        self.source
    }
}

new_sequence_store_key_direct!(pub ProjectionId, ProjectionElementId, derives = [Debug], el_derives = [Debug]);

/// Stores all collections of projections that can occur on a place.
///
/// This is used to efficiently represent [Place]s that might have many
/// projections, and to easily copy them when duplicating places.
pub type ProjectionStore = DefaultSequenceStore<ProjectionId, PlaceProjection>;

/// An [IrRef] is a reference to where a particular item occurs within
/// the [Body]. The [IrRef] stores an associated [BasicBlock] and an
/// index into the statements of that [BasicBlock].
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct IrRef {
    /// The block that the reference points to.
    pub block: BasicBlock,

    /// The nth statement that the reference points to.
    pub index: usize,
}

impl Default for IrRef {
    fn default() -> Self {
        Self { block: START_BLOCK, index: Default::default() }
    }
}

impl fmt::Debug for IrRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}[{}]", self.block, self.index)
    }
}

impl IrRef {
    /// Create a new [IrRef] with the given `block` and `index`.
    pub fn new(block: BasicBlock, index: usize) -> Self {
        Self { block, index }
    }

    /// Check if this [IrRef] dominates the given `other` [IrRef]
    /// with the set of dominators. If the two [IrRef]s are in the
    /// same block, then the index of the [IrRef] is checked to see
    /// if it is less than or equal to the other [IrRef].
    pub fn dominates(&self, other: IrRef, dominators: &Dominators<BasicBlock>) -> bool {
        if self.block == other.block {
            self.index <= other.index
        } else {
            dominators.is_dominated_by(self.block, other.block)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{ir::*, write::WriteIr};

    #[test]
    fn test_place_display() {
        let storage = IrCtx::new();

        let place = Place {
            local: Local::new(0),
            projections: storage.projections().create_from_slice(&[
                PlaceProjection::Deref,
                PlaceProjection::Field(0),
                PlaceProjection::Index(Local::new(1)),
                PlaceProjection::Downcast(VariantIdx::from_usize(0)),
            ]),
        };

        assert_eq!(format!("{}", place.for_fmt(&storage)), "(((*_0).0)[_1] as variant#0)");

        let place = Place {
            local: Local::new(0),
            projections: storage.projections().create_from_slice(&[
                PlaceProjection::Deref,
                PlaceProjection::Deref,
                PlaceProjection::Deref,
            ]),
        };

        assert_eq!(format!("{}", place.for_fmt(&storage)), "(*(*(*_0)))");
    }
}
