//! Hash Compiler Intermediate Representation (IR) crate. This module is still
//! under construction and is subject to change.
#![allow(unused)]

use hash_source::{
    constant::{InternedFloat, InternedInt, InternedStr},
    location::{SourceLocation, Span},
    SourceId,
};
use hash_types::{nominals::NominalDefId, terms::TermId, Mutability};
use index_vec::{index_vec, IndexSlice, IndexVec};

// /// Represents the type layout of a given expression.
// #[derive(Debug, PartialEq, Eq)]
// pub enum Ty<'ir> {
//     /// `usize` type, machine specific unsigned pointer
//     USize,
//     /// `u8` type, 8bit unsigned integer
//     U8,
//     /// `u16` type, 16bit unsigned integer
//     U16,
//     /// `u32` type, 32bit unsigned integer
//     U32,
//     /// `u64` type, 64bit unsigned integer
//     U64,
//     /// `isize` type, machine specific unsigned pointer
//     ISize,
//     /// `i8` type, 8bit signed integer
//     I8,
//     /// `i16` type, 16bit signed integer
//     I16,
//     /// `i32` type, 32bit signed integer
//     I32,
//     /// `i64` type, 64bit signed integer
//     I64,
//     /// `f32` type, 32bit float
//     F32,
//     /// `f64` type, 64bit float
//     F64,
//     /// A `void` type
//     Void,
//     /// Represents any collection of types in a specific order.
//     Structural(&'ir [Ty<'ir>]),
//     /// Essentially an enum representation
//     Union(&'ir [Ty<'ir>]),
//     /// Reference type
//     Ptr(&'ir Ty<'ir>),
//     /// Raw reference type
//     RawPtr(&'ir Ty<'ir>),
// }

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Const {
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

/// A collection of operations that are constant and must run during the
/// compilation stage.
#[derive(Debug, PartialEq, Eq)]
pub enum ConstOp {
    /// Yields the size of the given type.
    SizeOf,
    /// Yields the word alignment of the type.
    AlignOf,
}

#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
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
    mutability: Mutability,
    /// The type of the local.
    ty: TermId,
}

impl LocalDecl {
    /// Create a new [LocalDecl].
    pub fn new(mutability: Mutability, ty: TermId) -> Self {
        Self { mutability, ty }
    }

    /// Create a new mutable [LocalDecl].
    pub fn new_mutable(ty: TermId) -> Self {
        Self::new(Mutability::Mutable, ty)
    }

    /// Create a new immutable [LocalDecl].
    pub fn new_immutable(ty: TermId) -> Self {
        Self::new(Mutability::Immutable, ty)
    }

    /// Returns the type of the local.
    pub fn ty(&self) -> TermId {
        self.ty
    }
}

/// The addressing mode of the [RValue::Ref].
#[derive(Debug, PartialEq, Eq)]
pub enum AddressMode {
    /// Take the `&raw` reference of something.
    Raw,
    /// Take the `&` reference of something, meaning that it is reference
    /// counted.
    Smart,
}

#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq)]
pub enum AggregateKind {
    Tuple,
    Array(TermId),
    Enum(NominalDefId, usize),
    Struct(NominalDefId),
}

#[derive(Debug, PartialEq, Eq)]
pub enum RValue<'ir> {
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
    UnaryOp(UnaryOp, &'ir RValue<'ir>),

    /// A binary expression with a binary operator and two inner expressions.
    BinaryOp(BinOp, &'ir RValue<'ir>, &'ir RValue<'ir>),
    /// An expression which is taking the address of another expression with an
    /// mutability modifier e.g. `&mut x`.
    Ref(Mutability, &'ir Statement<'ir>, AddressMode),
    /// Used for initialising structs, tuples and other aggregate
    /// data structures
    Aggregate(AggregateKind, Vec<Place>),
}

/// A defined statement within the IR
#[derive(Debug, PartialEq, Eq)]
pub enum StatementKind<'ir> {
    /// Filler kind when expressions are optimised out or removed for other
    /// reasons.
    Nop,
    /// An assignment expression, a right hand-side expression is assigned to a
    /// left hand-side pattern e.g. `x = 2`
    Assign(Place, RValue<'ir>),

    /// Allocate some value on the the heap using reference
    /// counting.
    Alloc(Local),

    /// Allocate a value on the heap without reference counting
    AllocRaw(Local),
}

/// A [Statement] is a intermediate transformation step within a [BasicBlock].
#[derive(Debug, PartialEq, Eq)]
pub struct Statement<'ir> {
    /// The kind of [Statement] that it is.
    pub kind: StatementKind<'ir>,
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

/// [Terminator] statements are essentially those that affect control
/// flow.
#[derive(Debug, PartialEq, Eq)]
pub struct Terminator<'ir> {
    /// The kind of [Terminator] that it is.
    pub kind: TerminatorKind<'ir>,
    /// The [Span] of the statement, relative to the [Body]
    /// `source-id`.
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TerminatorKind<'ir> {
    /// A simple go to block directive.
    Goto(BasicBlock),

    /// Return from the parent function
    Return,

    /// Perform a function call
    Call {
        /// The layout of the function type that is to be called.
        op: TermId,
        /// Arguments to the function.
        args: Vec<Local>,

        /// Where to return after completing the call
        target: Option<BasicBlock>,
    },

    /// Denotes that this terminator should never be reached, doing so will
    /// break IR control flow invariants.
    Unreachable,

    /// Essentially a `jump if <0> to <1> else go to <2>`
    Switch(Local, &'ir [(Const, BasicBlock)], BasicBlock),

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
pub struct BasicBlockData<'ir> {
    /// The statements that the block has.
    pub statements: Vec<Statement<'ir>>,
    /// An optional terminating statement, where the block goes
    /// after finishing execution of these statements.
    pub terminator: Option<Terminator<'ir>>,
}

impl<'ir> BasicBlockData<'ir> {
    /// Create a new [BasicBlockData] with no statements and a provided
    /// `terminator`. It is assumed that the statements are to be added
    /// later to the block.
    pub fn new(terminator: Option<Terminator<'ir>>) -> Self {
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

    DEBUG_FORMAT = "l{}";
}

/// `0` is used as the return place of any lowered body.
pub const RETURN_PLACE: Local = Local { _raw: 0 };

/// The origin of a lowered function body.
pub enum FnSource {
    /// The item is a normal function.
    Item,
    /// The item is an intrinsic function.
    Intrinsic,
}

pub struct Body<'ir> {
    /// The blocks that the function is represented with
    blocks: IndexVec<BasicBlock, BasicBlockData<'ir>>,

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
    declarations: IndexVec<Local, LocalDecl>,

    /// Number of arguments to the function
    arg_count: usize,

    /// The source of the function, is it a normal function, or an intrinsic
    source: FnSource,
    /// The location of the function
    span: Span,
    /// The id of the source of where this body originates from.
    source_id: SourceId,
}

impl<'ir> Body<'ir> {
    pub fn new(
        blocks: IndexVec<BasicBlock, BasicBlockData<'ir>>,
        declarations: IndexVec<Local, LocalDecl>,
        arg_count: usize,
        source: FnSource,
        span: Span,
        source_id: SourceId,
    ) -> Self {
        Self { blocks, declarations, arg_count, source, span, source_id }
    }
}
