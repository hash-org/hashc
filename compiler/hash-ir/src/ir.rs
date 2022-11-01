//! Hash Compiler Intermediate Representation (IR) crate. This module is still
//! under construction and is subject to change.
use hash_source::{
    constant::{InternedFloat, InternedInt, InternedStr},
    identifier::Identifier,
    location::Span,
    SourceId,
};
use hash_types::{scope::Mutability, terms::TermId};
use hash_utils::{new_store_key, store::DefaultStore};
use index_vec::IndexVec;

use crate::ty::IrTyId;

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
    mutability: Mutability,
    /// The type of the local.
    ty: IrTyId,
}

impl LocalDecl {
    /// Create a new [LocalDecl].
    pub fn new(mutability: Mutability, ty: IrTyId) -> Self {
        Self { mutability, ty }
    }

    /// Create a new mutable [LocalDecl].
    pub fn new_mutable(ty: IrTyId) -> Self {
        Self::new(Mutability::Mutable, ty)
    }

    /// Create a new immutable [LocalDecl].
    pub fn new_immutable(ty: IrTyId) -> Self {
        Self::new(Mutability::Immutable, ty)
    }

    /// Returns the type of the local.
    pub fn ty(&self) -> IrTyId {
        self.ty
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
pub enum FnSource {
    /// The item is a normal function.
    Item,
    /// The item is an intrinsic function.
    Intrinsic,
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
    _source: FnSource,
    /// The location of the function
    _span: Span,
    /// The id of the source of where this body originates from.
    _source_id: SourceId,
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
        source: FnSource,
        span: Span,
        source_id: SourceId,
        dump: bool,
    ) -> Self {
        Self {
            blocks,
            name,
            declarations,
            arg_count,
            _source: source,
            _span: span,
            _source_id: source_id,
            dump,
        }
    }

    /// Check if the [Body] needs to be dumped.
    pub fn needs_dumping(&self) -> bool {
        self.dump
    }
}

new_store_key!(pub RValueId);

/// Stores all the used [RValue]s.
///
/// [Rvalue]s are accessed by an ID, of type [RValueId].
pub type RValueStore = DefaultStore<RValueId, RValue>;
