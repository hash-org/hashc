//! Hash Compiler Intermediate Representation (IR) crate. This module is still
//! under construction and is subject to change.
use std::fmt;

use hash_source::{
    constant::{InternedFloat, InternedInt, InternedStr},
    identifier::Identifier,
    location::{SourceLocation, Span},
    SourceId,
};
use hash_types::terms::TermId;
use hash_utils::{new_store_key, store::DefaultStore};
use index_vec::IndexVec;

use crate::ty::{IrTyId, Mutability};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Const {
    /// Nothing, it has zero size.
    Zero,

    /// Byte constant, essentially a boolean.
    Byte(u8),

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

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Zero => write!(f, "()"),
            Self::Byte(b) => write!(f, "{b}"),
            Self::Char(c) => write!(f, "{c}"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Float(flt) => write!(f, "{flt}"),
            Self::Str(s) => write!(f, "{s}"),
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

/// Binary operations on [RValue]s that are typed as primitive, or have
/// `intrinsic` implementations defined for them. Any time that does not
/// implement these binary operations by default will create a function
/// call to the implementation of the binary operation.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BinOp {
    /// '=='
    EqEq,
    /// '!='
    NotEq,
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

    /// Whether the local declaration is an auxiliary,
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PlaceProjection {
    /// When we want to narrow down the union type to some specific
    /// variant.
    Downcast(usize),
    /// A reference to a specific field within the place, at this stage they
    /// are represented as indexes into the field store of the place type.
    Field(usize),
    /// Take the index of some specific place, the index does not need to be
    /// constant
    Index(Local),
    /// We want to dereference the place
    Deref,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Place {
    /// The original place of where this is referring to.
    pub local: Local,
    /// Any projections that are applied onto the `local` in
    /// order to specify an exact location within the local.
    pub projections: Vec<PlaceProjection>,
}

impl Place {
    /// Create a [Place] that points to the return `place` of a lowered  body.
    pub fn return_place() -> Self {
        Self { local: RETURN_PLACE, projections: Vec::new() }
    }
}

impl From<Local> for Place {
    fn from(value: Local) -> Self {
        Self { local: value, projections: Vec::new() }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AggregateKind {
    Tuple,
    Array(IrTyId),
    Enum(IrTyId, usize),
    Struct(IrTyId),
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
    /// An expression which is taking the address of another expression with an
    /// mutability modifier e.g. `&mut x`.
    Ref(Mutability, Statement, AddressMode),
    /// Used for initialising structs, tuples and other aggregate
    /// data structures
    Aggregate(AggregateKind, Vec<Place>),
    /// Compute the discriminant of a [Place], this is essentially checking
    /// which variant a union is. For types that don't have a discriminant
    /// (non-union types ) this will return the value as 0.
    Discriminant(Place),
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
        /// The layout of the function type that is to be called.
        op: IrTyId,
        /// Arguments to the function.
        args: Vec<Local>,
        /// Where to return after completing the call
        target: Option<BasicBlock>,
    },

    /// Denotes that this terminator should never be reached, doing so will
    /// break IR control flow invariants.
    Unreachable,

    /// Essentially a `jump if <0> to <1> else go to <2>`. The last argument is
    /// the `otherwise` condition.
    Switch(Local, Vec<(Const, BasicBlock)>, BasicBlock),

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

/// Essentially a block
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

    /// The name of the body
    pub name: Identifier,

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
        name: Identifier,
        arg_count: usize,
        source: BodySource,
        span: Span,
        source_id: SourceId,
        dump: bool,
    ) -> Self {
        Self { blocks, name, declarations, arg_count, source, span, source_id, dump }
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

    /// Get the name of the [Body]
    pub fn name(&self) -> Identifier {
        self.name
    }
}

new_store_key!(pub RValueId);

/// Stores all the used [RValue]s.
///
/// [Rvalue]s are accessed by an ID, of type [RValueId].
pub type RValueStore = DefaultStore<RValueId, RValue>;
