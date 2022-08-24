//! Hash Compiler Intermediate Representation (IR) crate. This module is still
//! under construction and is subject to change.
#![allow(unused)]

use hash_source::{
    constant::{InternedFloat, InternedInt, InternedStr},
    location::{Span, SourceLocation},
};
use index_vec::{IndexVec, IndexSlice, index_vec};

/// Represents the type layout of a given expression.
#[derive(Debug, PartialEq, Eq)]
pub enum Ty<'i> {
    /// `usize` type, machine specific unsigned pointer
    USize,
    /// `u8` type, 8bit unsigned integer
    U8,
    /// `u16` type, 16bit unsigned integer
    U16,
    /// `u32` type, 32bit unsigned integer
    U32,
    /// `u64` type, 64bit unsigned integer
    U64,
    /// `isize` type, machine specific unsigned pointer
    ISize,
    /// `i8` type, 8bit signed integer
    I8,
    /// `i16` type, 16bit signed integer
    I16,
    /// `i32` type, 32bit signed integer
    I32,
    /// `i64` type, 64bit signed integer
    I64,
    /// `f32` type, 32bit float
    F32,
    /// `f64` type, 64bit float
    F64,
    /// `char` type, 32bit characters
    Char,
    /// A `void` type
    Void,
    /// Represents any collection of types in a specific order.
    Structural(&'i [Ty<'i>]),
    /// Essentially an enum representation
    Union(&'i [Ty<'i>]),
    /// Pointer that points to some type
    Ptr(&'i Ty<'i>),
    /// Raw Pointer that points to some type
    RawPtr(&'i Ty<'i>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Const {
    /// Character constant
    Char(char),
    /// Integer constant that is defined within the program source.
    Int(InternedInt),
    /// Float constant that is defined within the program source.
    Float(InternedFloat),

    /// String has to become a struct that has a pointer
    /// to bytes and a length of bytes.
    ///
    /// ```ignore
    /// str := struct(data: &raw u8, len: usize);
    /// ```
    Str(InternedStr),
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
    /// 'as'
    As,
}

/// Mutability
#[derive(Debug, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

/// An expression within the representation
#[derive(Debug, PartialEq, Eq)]
pub struct Statement<'i> {
    kind: StatementKind<'i>,
    span: Span,
}

/// Essentially a register for a value
#[derive(Debug, PartialEq, Eq)]
pub struct LocalDecl<'a> {
    /// Mutability of the local
    mutability: Mutability,

    /// The type of the local
    ty: Ty<'a>,
}

/// The addressing mode of the [Statement::AddrOf] IR statement.
#[derive(Debug, PartialEq, Eq)]
pub enum AddressMode {
    /// Take the `&raw` reference of something.
    Raw,
    /// Take the `&` reference of something, meaning that it is reference
    /// counted.
    Smart,
}

/// A defined statement within the IR
#[derive(Debug, PartialEq, Eq)]
pub enum StatementKind<'i> {
    /// Filler kind when expressions are optimised out or removed for other
    /// reasons.
    Nop,
    /// A constant value.
    Const(Const),

    /// A local variable value
    Local(Local),

    /// An identity expression, essentially wrapped with an inner expression.
    Identity(&'i Statement<'i>),
    /// A unary expression with a unary operator.
    Unary(UnaryOp, &'i Statement<'i>),
    /// A binary expression with a binary operator and two inner expressions.
    Binary(BinOp, &'i Statement<'i>, &'i Statement<'i>),
    /// An index expression e.g. `x[3]`
    Index(&'i Statement<'i>, &'i Statement<'i>),
    /// An assignment expression, a right hand-side expression is assigned to a
    /// left hand-side pattern e.g. `x = 2`
    Assign(Local, &'i Statement<'i>),

    /// An expression which is taking the address of another expression with an
    /// mutability modifier e.g. `&mut x`.
    Ref(Mutability, &'i Statement<'i>, AddressMode),

    /// Allocate some value on the the heap using reference 
    /// counting.
    Alloc(Local),
}

/// [Terminator] statements are essentially those that affect control
/// flow.
#[derive(Debug, PartialEq, Eq)]
pub enum Terminator {
    /// A simple go to block directive.
    Goto(BasicBlock),

    /// Return from the parent function
    Return,

    /// Perform a function call
    Call {
        // op: todo!(),

        args: Vec<Local>,

        /// Where to return after completing the call
        target: Option<BasicBlock>
    },

    /// Denotes that this terminator should never be reached, doing so will
    /// break IR control flow invariants.
    Unreachable,

    /// Essentially a `jump if <0> to <1> else go to <2>`
    Switch(Local, Vec<(Const, BasicBlock)>, BasicBlock),
}


/// Essentially a block
#[derive(Debug, PartialEq, Eq)]
pub struct BasicBlockData<'i> {
    /// The statements that the block has.
    statements: Vec<Statement<'i>>,
    /// An optional terminating statement, where the block goes
    /// after finishing execution of these statements.
    terminator: Option<Terminator>,
}


index_vec::define_index_type! {
    /// Index for [BasicBlockData] stores within generated [Body]s.
    pub struct BasicBlock = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

index_vec::define_index_type! {
    /// Index for [LocalDecl] stores within generated [Body]s.
    pub struct Local = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}


pub enum FnSource {
    Item,
    Intrinsic
}

pub struct Body<'i> {
    /// The blocks that the function is represented with
    blocks: IndexVec<BasicBlock, BasicBlockData<'i>>,

    /// Declarations of local variables:
    /// 
    /// Not final:
    /// 
    /// - The first local is used a representation of the function return value if any.
    /// 
    /// - the next `arg_count` locals are used to represent the assigning of function arguments.
    /// 
    /// - the remaining are temporaries that are used within the function.
    declarations: IndexVec<Local, LocalDecl<'i>>,

    /// Number of arguments to the function
    arg_count: usize,

    /// The source of the function, is it a normal function, or an intrinsic
    source: FnSource,

    /// The location of the function 
    span: SourceLocation
}
