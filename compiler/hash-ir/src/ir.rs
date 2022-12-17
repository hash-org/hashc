//! Hash Compiler Intermediate Representation (IR) crate. This module is still
//! under construction and is subject to change.
use core::slice;
use std::{cmp::Ordering, fmt, iter::once};

use hash_ast::ast;
use hash_source::{
    constant::{IntConstant, InternedFloat, InternedInt, InternedStr, CONSTANT_MAP},
    identifier::Identifier,
    location::{SourceLocation, Span},
    SourceId,
};
use hash_types::terms::TermId;
use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore, SequenceStore, Store},
};
use index_vec::IndexVec;
use smallvec::SmallVec;

use crate::{
    ty::{AdtId, IrTy, IrTyId, Mutability, VariantIdx},
    IrStorage,
};

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

impl Const {
    /// Create a [Const::Zero] with a unit type, the total zero.
    pub fn zero(storage: &IrStorage) -> Self {
        let unit = storage.ty_store().create(IrTy::unit(storage));
        Self::Zero(unit)
    }

    /// Check if a [Const] is of integral kind.
    pub fn is_integral(&self) -> bool {
        matches!(self, Self::Char(_) | Self::Int(_) | Self::Bool(_))
    }

    /// Create a new [Const] from a scalar value, with the appropriate
    /// type.
    pub fn from_scalar(value: u128, ty: IrTyId, storage: &IrStorage) -> Self {
        storage.ty_store().map_fast(ty, |ty| match ty {
            IrTy::Int(int_ty) => {
                let interned_value = IntConstant::from_uint(value, (*int_ty).into());
                Self::Int(CONSTANT_MAP.create_int_constant(interned_value))
            }
            IrTy::UInt(int_ty) => {
                let interned_value = IntConstant::from_uint(value, (*int_ty).into());
                Self::Int(CONSTANT_MAP.create_int_constant(interned_value))
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
            Self::Char(c) => write!(f, "{c}"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Float(flt) => write!(f, "{flt}"),
            Self::Str(s) => write!(f, "{s}"),
        }
    }
}

/// Perform a value comparison between two constants.
pub fn compare_constant_values(left: Const, right: Const) -> Option<Ordering> {
    match (left, right) {
        (Const::Zero(_), Const::Zero(_)) => Some(Ordering::Equal),
        (Const::Bool(left), Const::Bool(right)) => Some(left.cmp(&right)),
        (Const::Char(left), Const::Char(right)) => Some(left.cmp(&right)),
        (Const::Int(left), Const::Int(right)) => CONSTANT_MAP.map_int_constant(left, |left| {
            CONSTANT_MAP.map_int_constant(right, |right| left.partial_cmp(right))
        }),
        (Const::Float(left), Const::Float(right)) => {
            CONSTANT_MAP.map_float_constant(left, |left| {
                CONSTANT_MAP.map_float_constant(right, |right| left.value.partial_cmp(&right.value))
            })
        }
        (Const::Str(left), Const::Str(right)) => Some(left.cmp(&right)),
        _ => None,
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

impl From<ast::UnOp> for UnaryOp {
    fn from(value: ast::UnOp) -> Self {
        match value {
            ast::UnOp::BitNot => Self::BitNot,
            ast::UnOp::Not => Self::Not,
            ast::UnOp::Neg => Self::Neg,
            _ => unreachable!(),
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
    /// '||'
    Or,
    /// '&'
    BitAnd,
    /// '&&'
    And,
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
    /// Returns whether the binary operator can be "checked".
    pub fn is_checkable(&self) -> bool {
        matches!(self, Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Shl | Self::Shr)
    }

    /// Check if the [BinOP] is a comparitor.
    pub fn is_comparator(&self) -> bool {
        matches!(self, Self::Eq | Self::Neq | Self::Gt | Self::GtEq | Self::Lt | Self::LtEq)
    }
}

impl From<ast::BinOp> for BinOp {
    fn from(value: ast::BinOp) -> Self {
        match value {
            ast::BinOp::EqEq => Self::Eq,
            ast::BinOp::NotEq => Self::Neq,
            ast::BinOp::BitOr => Self::BitOr,
            ast::BinOp::Or => Self::Or,
            ast::BinOp::BitAnd => Self::BitAnd,
            ast::BinOp::And => Self::And,
            ast::BinOp::BitXor => Self::BitXor,
            ast::BinOp::Exp => Self::Exp,
            ast::BinOp::Gt => Self::Gt,
            ast::BinOp::GtEq => Self::GtEq,
            ast::BinOp::Lt => Self::Lt,
            ast::BinOp::LtEq => Self::LtEq,
            ast::BinOp::Shr => Self::Shr,
            ast::BinOp::Shl => Self::Shl,
            ast::BinOp::Add => Self::Add,
            ast::BinOp::Sub => Self::Sub,
            ast::BinOp::Mul => Self::Mul,
            ast::BinOp::Div => Self::Div,
            ast::BinOp::Mod => Self::Mod,
            // `As` and `Merge` are dealt with before this ever reached
            // this point.
            _ => unreachable!(),
        }
    }
}

/// Essentially a register for a value
#[derive(Debug, PartialEq, Eq)]
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

/// The addressing mode of the [RValue::Ref].
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AddressMode {
    /// Take the `&raw` reference of something.
    Raw,
    /// Take the `&` reference of something, meaning that it is reference
    /// counted.
    Smart,
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
    Subslice {
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
    pub fn return_place(storage: &IrStorage) -> Self {
        Self { local: RETURN_PLACE, projections: storage.projection_store.create_empty() }
    }

    pub fn from_local(local: Local, storage: &IrStorage) -> Self {
        Self { local, projections: storage.projection_store.create_empty() }
    }

    /// Create a new [Place] from an existing place whilst also
    /// applying a a [PlaceProjection::Field] on the old one.
    pub fn field(&self, field: usize, storage: &IrStorage) -> Self {
        let projections = storage.projection_store.get_vec(self.projections);

        Self {
            local: self.local,
            projections: storage.projection_store.create_from_iter_fast(
                projections.iter().copied().chain(once(PlaceProjection::Field(field))),
            ),
        }
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
    Tuple,

    /// An array aggregate kind initialisation.
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
}

/// The representation of values that occur on the right-hand side of an
/// assignment.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum RValue {
    /// A constant value.
    Const(Const),

    /// A local variable value, do we need to denote whether this is a
    /// copy/move?
    Use(Place),

    /// Compiler intrinsic operation, this will be computed in place and
    /// replaced by a constant.
    ///
    /// @@Future: maybe in the future this should be replaced by a compile-time
    /// API variant which will just run some kind of operation and return the
    /// constant.
    ConstOp(ConstOp, TermId),

    /// A unary expression with a unary operator.
    UnaryOp(UnaryOp, RValueId),

    /// A binary expression with a binary operator and two inner expressions.
    BinaryOp(BinOp, RValueId, RValueId),

    /// A binary expression that is checked. The only difference between this
    /// and a normal [RValue::BinaryOp] is that this will return a boolean and
    /// the result of the operation in the form of `(T, bool)`. The boolean
    /// flag denotes whether the operation violated the check...
    CheckedBinaryOp(BinOp, RValueId, RValueId),

    /// Compute the `length` of a place, yielding a `usize`.
    ///
    /// Any `place` that is not an array or slice, is not a valid [RValue].
    Len(Place),

    /// An expression which is taking the address of another expression with an
    /// mutability modifier e.g. `&mut x`.
    Ref(Mutability, Place, AddressMode),
    /// Used for initialising structs, tuples and other aggregate
    /// data structures
    Aggregate(AggregateKind, Vec<RValueId>),
    /// Compute the discriminant of a [Place], this is essentially checking
    /// which variant a union is. For types that don't have a discriminant
    /// (non-union types ) this will return the value as 0.
    Discriminant(Place),
}

impl RValue {
    /// Check if an [RValue] is a constant.
    pub fn is_const(&self) -> bool {
        matches!(self, RValue::Const(_))
    }

    /// Check if an [RValue] is a constant operation and involves a constant
    /// that is of an integral kind...
    pub fn is_integral_const(&self) -> bool {
        matches!(self, RValue::Const(Const::Int(_) | Const::Float(_) | Const::Char(_)))
    }

    /// Convert the RValue into a constant, having previously
    /// checked that it is a constant.
    pub fn as_const(&self) -> Const {
        match self {
            RValue::Const(c) => *c,
            rvalue => unreachable!("Expected a constant, got {:?}", rvalue),
        }
    }
}

impl From<Const> for RValue {
    fn from(value: Const) -> Self {
        Self::Const(value)
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
    Assign(Place, RValueId),

    /// Set the discriminant on a particular place, this is used to conceretly
    /// specify what the discrimniant of a particular enum/union type is.
    Discriminate(Place, VariantIdx),

    /// Allocate some value on the the heap using reference
    /// counting.
    Alloc(Local),

    /// Allocate a value on the heap without reference counting
    AllocRaw(Local),
}

/// A [Statement] is a intermediate transformation step within a [BasicBlock].
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Statement {
    /// The kind of [Statement] that it is.
    pub kind: StatementKind,
    /// The [Span] of the statement, relative to the [Body]
    /// `source-id`.
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AssertKind {
    DivisionByZero,
    /// Occurs when an attempt to take the remainder of some operand with zero.
    RemainderByZero,
    /// Performing an arithmetic operation has caused the operation to overflow
    Overflow,
    /// Performing an arithmetic operation has caused the operation to overflow
    /// whilst subtracting or terms that are signed
    NegativeOverflow,
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
    /// `source-id`.
    pub span: Span,
}

/// Struct that represents all of the targets that a [TerminatorKind::Switch]
/// can jump to. This also defines some useful methods on the block to iterate
/// over all the targets, etc.
#[derive(Debug, PartialEq, Eq)]
pub struct SwitchTargets {
    /// The jump table, contains corresponding values to *jump* on and the
    /// location of where the jump goes to. The values are stored as an
    /// [u128] because we only deal with **small** integral types, for larger
    /// integer values, we default to using `Eq` check. Since the value is
    /// stored as an [u128], this is nonsensical when it comes using these
    /// values, which is why a **bias** needs to be applied before properly
    /// reading the value which can be derived from the integral type that
    /// is being matched on.
    ///
    /// N.B. All values within the table are unique, there cannot be multiple
    /// targets for the same value.
    pub table: SmallVec<[(u128, BasicBlock); 1]>,

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
        Self { table: targets.collect(), ty, otherwise }
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
        self.table.iter().map(|(_, target)| *target).chain(self.otherwise.into_iter())
    }

    pub fn iter(&self) -> SwitchTargetsIter<'_> {
        SwitchTargetsIter { inner: self.table.iter() }
    }

    /// Find the target for a specific value, if it exists.
    pub fn corresponding_target(&self, value: u128) -> BasicBlock {
        self.table
            .iter()
            .find(|(v, _)| *v == value)
            .map(|(_, b)| *b)
            .unwrap_or_else(|| self.otherwise())
    }
}

pub struct SwitchTargetsIter<'a> {
    inner: slice::Iter<'a, (u128, BasicBlock)>,
}

impl<'a> Iterator for SwitchTargetsIter<'a> {
    type Item = (u128, BasicBlock);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().copied()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

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
        op: RValueId,

        /// Arguments to the function, later we might need to distinguish
        /// whether these are move or copy arguments.
        args: Vec<RValueId>,

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
        value: RValueId,

        /// All of the targets that are defined for the particular switch.
        targets: SwitchTargets,
    },

    /// This terminator is used to verify that the result of some operation has
    /// no violated a some condition. Usually, this is combined with operations
    /// that perform a `checked` operation and sets some flag in the form of a
    /// [Place] and expects it to be equal to the `expected` boolean value.
    Assert {
        /// The condition that is to be checked against the `expected value
        condition: Place,
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
    pub fn make_if(
        place: Place,
        true_block: BasicBlock,
        false_block: BasicBlock,
        storage: &IrStorage,
    ) -> Self {
        let value = storage.push_rvalue(RValue::Use(place));

        let targets = SwitchTargets::new(
            std::iter::once((false.into(), false_block)),
            storage.ty_store().make_bool(),
            Some(true_block),
        );

        TerminatorKind::Switch { value, targets }
    }
}

/// The contents of a [BasicBlock], the statements of the block, and a
/// terminator. Initially, the `terminator` begins as [None], and will
/// be set when the lowering process is completed.
///
/// N.B. It is an invariant for a [BasicBlock] to not have a terminator.
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
}

index_vec::define_index_type! {
    /// Index for [BasicBlockData] stores within generated [Body]s.
    pub struct BasicBlock = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));

    DEBUG_FORMAT = "bb{}";
}

/// `0` is used as the starting block of any lowered body.
pub const START_BLOCK: BasicBlock = BasicBlock { _raw: 0 };

index_vec::define_index_type! {
    /// Index for [LocalDecl] stores within generated [Body]s.
    pub struct Local = u32;

    MAX_INDEX = i32::max_value() as usize;
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
    /// The item is an intrinsic function.
    Intrinsic,
}

impl fmt::Display for BodySource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BodySource::Const => write!(f, "constant block"),
            BodySource::Item => write!(f, "function"),
            BodySource::Intrinsic => write!(f, "intrinsic function"),
        }
    }
}

pub struct Body {
    /// The blocks that the function is represented with
    pub blocks: IndexVec<BasicBlock, BasicBlockData>,

    /// Declarations of local variables:
    ///
    /// Not final:
    ///
    /// - The first local is used a representation of the function return value
    ///   if any.
    ///
    /// - the next `arg_count` locals are used to represent the assigning of
    ///   function arguments.
    ///
    /// - the remaining are temporaries that are used within the function.
    pub declarations: IndexVec<Local, LocalDecl>,

    /// Information that is derived when the body in being
    /// lowered.
    pub info: BodyInfo,

    /// Number of arguments to the function
    pub arg_count: usize,

    /// The source of the function, is it a normal function, or an intrinsic
    source: BodySource,

    /// The location of the function
    span: Span,

    /// The id of the source of where this body originates from.
    source_id: SourceId,

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
        source: BodySource,
        span: Span,
        source_id: SourceId,
    ) -> Self {
        Self { blocks, info, declarations, arg_count, source, span, source_id, dump: false }
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

    /// Get the [BodySource] for the [Body]
    pub fn source(&self) -> BodySource {
        self.source
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
    pub name: Identifier,

    /// The type of the body that was lowered
    ty: Option<IrTyId>,
}

impl BodyInfo {
    /// Create a new [BodyInfo] with the given `name`.
    pub fn new(name: Identifier) -> Self {
        Self { name, ty: None }
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
}

new_store_key!(pub RValueId);

/// Stores all the used [RValue]s.
///
/// [Rvalue]s are accessed by an ID, of type [RValueId].
pub type RValueStore = DefaultStore<RValueId, RValue>;

new_sequence_store_key!(pub ProjectionId);

/// Stores all collections of projections that can occur on a place.
///
/// This is used to efficiently represent [Place]s that might have many
/// projections, and to easily copy them when duplicating places.
pub type ProjectionStore = DefaultSequenceStore<ProjectionId, PlaceProjection>;

#[cfg(test)]
mod tests {
    use crate::{ir::*, write::WriteIr};

    #[test]
    fn test_place_display() {
        let storage = IrStorage::new();

        let place = Place {
            local: Local::new(0),
            projections: storage.projection_store.create_from_slice(&[
                PlaceProjection::Deref,
                PlaceProjection::Field(0),
                PlaceProjection::Index(Local::new(1)),
                PlaceProjection::Downcast(VariantIdx::from_usize(0)),
            ]),
        };

        assert_eq!(format!("{}", place.for_fmt(&storage)), "(((*_0).0)[_1] as variant#0)");

        let place = Place {
            local: Local::new(0),
            projections: storage.projection_store.create_from_slice(&[
                PlaceProjection::Deref,
                PlaceProjection::Deref,
                PlaceProjection::Deref,
            ]),
        };

        assert_eq!(format!("{}", place.for_fmt(&storage)), "(*(*(*_0)))");
    }
}
