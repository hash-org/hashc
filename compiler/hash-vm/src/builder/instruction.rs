//! Instruction builder macros for convenient VM bytecode generation.
//!
//! This module provides the [`inst!`] macro which allows writing instructions
//! in a readable, assembly-like syntax.
//!
//! # Syntax
//!
//! The macro supports several types of operands (note the space after prefix):
//! - `[N]` - Literal register number (e.g., `[100]`)
//! - `r [expr]` - Parametrized register (e.g., `r [reg_id]` or `r [5 + 10]`)
//! - `@ [N]` - Block label reference (e.g., `@ [6]`)
//! - `# [N]` - Immediate value (e.g., `# [42]`)
//!
//! # Examples
//!
//! ```ignore
//! use hash_vm::builder::inst;
//!
//! // Basic usage with literal registers
//! let instructions = inst! {
//!     add64 [0], [42];
//!     mov [100], [98];
//!     push64 [10];
//! };
//!
//! // Using parametrized registers with expressions
//! let instructions = inst! {
//!     add64 r [5], r [10];
//!     mov r [5 + 10], r [10 + 10];
//! };
//!
//! // Using label references for jumps
//! let instructions = inst! {
//!     add32 [1], [2];
//!     cmp [1], [100];
//!     jmpzero [1], @ [0];
//! };
//!
//! // Using immediate values for write instructions
//! let instructions = inst! {
//!     write64 [50], # [1234];
//!     write32 [51], # [42];
//! };
//! ```

/// Helper macro to parse operands in instruction syntax.
#[doc(hidden)]
#[macro_export]
macro_rules! __parse_operand {
    // Parametrized register: r [expr]
    (r [$expr:expr]) => {
        $crate::bytecode::register::Register::new($expr as u8)
    };

    // Literal register: [N]
    ([$lit:literal]) => {
        $crate::bytecode::register::Register::new($lit)
    };

    // Parse the Stack Pointer register
    (SP) => {
        $crate::bytecode::register::Register::STACK_POINTER
    };
}

/// Helper macro to parse operand values (for Operand enum).
#[doc(hidden)]
#[macro_export]
macro_rules! __parse_operand_value {
    // Parametrized register: r [expr]
    (r [$expr:expr]) => {
        $crate::bytecode::op::Operand::Register($crate::bytecode::register::Register::new(
            $expr as u8,
        ))
    };

    // Literal register: [N]
    ([$lit:literal]) => {
        $crate::bytecode::op::Operand::Register($crate::bytecode::register::Register::new($lit))
    };

    // Label reference: @ [N]
    (@ [$expr:expr]) => {
        $crate::bytecode::op::Operand::Label($crate::bytecode::op::LabelOffset::new($expr))
    };

    // Immediate value: # [N]
    (# [$expr:expr]) => {
        $crate::bytecode::op::Operand::Immediate($expr)
    };
}

/// Main instruction builder macro.
///
/// Supports assembly-like syntax for creating VM instructions.
///
/// # Operand Syntax (note the space after prefix)
/// - `[N]`: Literal register number
/// - `r [expr]`: Parametrized register from expression
/// - `@ [N]`: Label offset reference
/// - `# [N]`: Immediate value
///
/// # Examples
///
/// ```ignore
/// use hash_vm::builder::inst;
///
/// let instructions = inst! {
///     // Stack operations
///     push64 [10];
///     pop64 [11];
///
///     // Arithmetic
///     add64 [1], [2];
///     sub32 [3], [4];
///     mul16 [5], [6];
///
///     // Move operation
///     mov [100], [98];
///
///     // With parametrized registers
///     mov r [5], r [10];
///
///     // Jumps with labels
///     jmp @ [0];
///     jmpzero [0], @ [100];
///
///     // Write with immediate
///     write64 [50], # [1234];
///     write32 [51], # [42];
///
///     // System calls
///     syscall [0];
///     call [10];
///     return;
/// };
/// ```
#[macro_export]
macro_rules! inst {
    // Empty case
    () => { vec![] };

    // Entry point: collect all instructions
    ($($inst:tt)*) => {{
        let mut instructions = Vec::new();
        $crate::__inst_impl!(instructions; $($inst)*);
        instructions
    }};
}

/// Internal implementation macro for instruction parsing.
#[doc(hidden)]
#[macro_export]
macro_rules! __inst_impl {
    // Base case: no more instructions
    ($vec:ident;) => {};

    // Stack operations - Pop (8/16/32/64 bit)
    ($vec:ident; pop8 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Pop8 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; pop16 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Pop16 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; pop32 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Pop32 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; pop64 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Pop64 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Stack operations - Push (8/16/32/64 bit)
    ($vec:ident; push8 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Push8 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; push16 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Push16 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; push32 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Push32 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; push64 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Push64 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Arithmetic operations - Addition
    ($vec:ident; add8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Add8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; add16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Add16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; add32  r[$r1:expr], r[$r2:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Add32 {
            l1: $crate::__parse_operand!(r [$r1]),
            l2: $crate::__parse_operand!(r [$r2])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; add32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Add32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; add64  r[$r1:expr], r[$r2:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Add64 {
            l1: $crate::__parse_operand!(r [$r1]),
            l2: $crate::__parse_operand!(r [$r2])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; add64  $r1:tt, r[$r2:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Add64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!(r [$r2])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; add64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Add64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Arithmetic operations - Subtraction
    ($vec:ident; sub8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Sub8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; sub16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Sub16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; sub32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Sub32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; sub64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Sub64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Arithmetic operations - Multiplication
    ($vec:ident; mul8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mul8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mul16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mul16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mul32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mul32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mul64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mul64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Arithmetic operations - Division
    ($vec:ident; div8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Div8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; div16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Div16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; div32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Div32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; div64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Div64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Arithmetic operations - Modulo
    ($vec:ident; mod8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mod8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mod16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mod16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mod32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mod32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mod64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mod64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Signed operations - Division
    ($vec:ident; idiv8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::IDiv8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; idiv16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::IDiv16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; idiv32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::IDiv32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; idiv64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::IDiv64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Signed operations - Multiplication
    ($vec:ident; imul8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::IMul8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; imul16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::IMul16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; imul32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::IMul32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; imul64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::IMul64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Float operations - Addition
    ($vec:ident; addf32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::AddF32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; addf64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::AddF64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Float operations - Subtraction
    ($vec:ident; subf32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::SubF32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; subf64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::SubF64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Float operations - Multiplication
    ($vec:ident; mulf32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::MulF32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mulf64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::MulF64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Float operations - Division
    ($vec:ident; divf32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::DivF32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; divf64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::DivF64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Float operations - Modulo
    ($vec:ident; modf32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::ModF32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; modf64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::ModF64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Float operations - Power
    ($vec:ident; powf32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::PowF32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; powf64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::PowF64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Bitwise operations - XOR
    ($vec:ident; xor8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Xor8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; xor16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Xor16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; xor32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Xor32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; xor64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Xor64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Bitwise operations - OR
    ($vec:ident; or8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Or8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; or16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Or16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; or32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Or32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; or64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Or64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Bitwise operations - AND
    ($vec:ident; and8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::And8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; and16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::And16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; and32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::And32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; and64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::And64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Bitwise operations - NOT
    ($vec:ident; not8 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Not8 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; not16 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Not16 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; not32 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Not32 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; not64 $r1:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Not64 { l1: $crate::__parse_operand!($r1) });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Bitwise operations - Shift left
    ($vec:ident; shl8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Shl8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; shl16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Shl16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; shl32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Shl32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; shl64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Shl64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Bitwise operations - Shift right
    ($vec:ident; shr8 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Shr8 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; shr16 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Shr16 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; shr32 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Shr32 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; shr64 $r1:tt, $r2:tt; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Shr64 {
            l1: $crate::__parse_operand!($r1),
            l2: $crate::__parse_operand!($r2)
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Write operations with immediate values
    ($vec:ident; write8 $r1:tt, # [$val:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Write8 {
            op: $crate::__parse_operand_value!($r1),
            value: $val as u8
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; write16 $r1:tt, # [$val:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Write16 {
            op: $crate::__parse_operand_value!($r1),
            value: $val as u16
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; write32 $r1:tt, # [$val:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Write32 {
            op: $crate::__parse_operand_value!($r1),
            value: $val as u32
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; write64 $r1:tt, # [$val:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Write64 {
            op: $crate::__parse_operand_value!($r1),
            value: $val as u64
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Write operations with immediate address and value
    ($vec:ident; write8 # [$addr:expr], # [$val:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Write8 {
            op: $crate::__parse_operand_value!(# [$addr]),
            value: $val as u8
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; write16 # [$addr:expr], # [$val:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Write16 {
            op: $crate::__parse_operand_value!(# [$addr]),
            value: $val as u16
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; write32 # [$addr:expr], # [$val:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Write32 {
            op: $crate::__parse_operand_value!(# [$addr]),
            value: $val as u32
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; write64 # [$addr:expr], # [$val:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Write64 {
            op: $crate::__parse_operand_value!(# [$addr]),
            value: $val as u64
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Control flow operations
    ($vec:ident; call r [$r1:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Call { func: $crate::__parse_operand_value!(r [$r1]) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; call [$r1:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Call { func: $crate::__parse_operand_value!([$r1]) });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    ($vec:ident; mov r [$dest:expr], r [$src:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mov {
            dest: $crate::__parse_operand!(r [$dest]),
            src: $crate::__parse_operand!(r [$src])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mov r [$dest:expr], [$src:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mov {
            dest: $crate::__parse_operand!(r [$dest]),
            src: $crate::__parse_operand!([$src])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mov [$dest:literal], r [$src:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mov {
            dest: $crate::__parse_operand!([$dest]),
            src: $crate::__parse_operand!(r [$src])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; mov [$dest:literal], [$src:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Mov {
            dest: $crate::__parse_operand!([$dest]),
            src: $crate::__parse_operand!([$src])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    ($vec:ident; syscall r [$r1:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Syscall { id: $crate::__parse_operand!(r [$r1]) });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; syscall [$r1:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Syscall { id: $crate::__parse_operand!([$r1]) });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    ($vec:ident; return; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Return);
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Jump operations with Operand support (labels and registers)
    ($vec:ident; jmp @ [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Jmp {
            location: $crate::__parse_operand_value!(@ [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmp r [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Jmp {
            location: $crate::__parse_operand_value!(r [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmp [$loc:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Jmp {
            location: $crate::__parse_operand_value!([$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    ($vec:ident; jmppos [$r1:literal], @ [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpPos {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!(@ [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmppos [$r1:literal], r [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpPos {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!(r [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmppos [$r1:literal], [$loc:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpPos {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!([$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmppos r [$r1:expr], @ [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpPos {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!(@ [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmppos r [$r1:expr], r [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpPos {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!(r [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmppos r [$r1:expr], [$loc:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpPos {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!([$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    ($vec:ident; jmpneg [$r1:literal], @ [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpNeg {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!(@ [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpneg [$r1:literal], r [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpNeg {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!(r [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpneg [$r1:literal], [$loc:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpNeg {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!([$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpneg r [$r1:expr], @ [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpNeg {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!(@ [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpneg r [$r1:expr], r [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpNeg {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!(r [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpneg r [$r1:expr], [$loc:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpNeg {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!([$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    ($vec:ident; jmpzero [$r1:literal], @ [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpZero {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!(@ [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpzero [$r1:literal], r [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpZero {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!(r [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpzero [$r1:literal], [$loc:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpZero {
            l1: $crate::__parse_operand!([$r1]),
            location: $crate::__parse_operand_value!([$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpzero r [$r1:expr], @ [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpZero {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!(@ [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpzero r [$r1:expr], r [$loc:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpZero {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!(r [$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; jmpzero r [$r1:expr], [$loc:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::JmpZero {
            l1: $crate::__parse_operand!(r [$r1]),
            location: $crate::__parse_operand_value!([$loc])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };

    // Comparison
    ($vec:ident; cmp r [$r1:expr], r [$r2:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Cmp {
            l1: $crate::__parse_operand!(r [$r1]),
            l2: $crate::__parse_operand!(r [$r2])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; cmp r [$r1:expr], [$r2:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Cmp {
            l1: $crate::__parse_operand!(r [$r1]),
            l2: $crate::__parse_operand!([$r2])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; cmp [$r1:literal], r [$r2:expr]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Cmp {
            l1: $crate::__parse_operand!([$r1]),
            l2: $crate::__parse_operand!(r [$r2])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
    ($vec:ident; cmp [$r1:literal], [$r2:literal]; $($rest:tt)*) => {
        $vec.push($crate::bytecode::Instruction::Cmp {
            l1: $crate::__parse_operand!([$r1]),
            l2: $crate::__parse_operand!([$r2])
        });
        $crate::__inst_impl!($vec; $($rest)*);
    };
}

#[cfg(test)]
mod tests {
    use crate::bytecode::{Instruction, op::Operand, register::Register};

    #[test]
    fn test_literal_registers() {
        let instructions = inst! {
            mov [10], [20];
            add64 [1], [2];
        };

        assert_eq!(instructions.len(), 2);
        assert!(matches!(instructions[0], Instruction::Mov { .. }));
        assert!(matches!(instructions[1], Instruction::Add64 { .. }));
    }

    #[test]
    fn test_register_with_expressions() {
        // The r [expr] syntax is for computed register indices
        let instructions = inst! {
            mov r [5], r [10];
            add32 r[15], r[20];
        };

        assert_eq!(instructions.len(), 2);
        if let Instruction::Mov { dest: d, src: s } = instructions[0] {
            assert_eq!(d, Register::new(5));
            assert_eq!(s, Register::new(10));
        } else {
            panic!("Expected Mov instruction");
        }

        if let Instruction::Add32 { l1, l2 } = instructions[1] {
            assert_eq!(l1, Register::new(15));
            assert_eq!(l2, Register::new(20));
        } else {
            panic!("Expected Add32 instruction");
        }
    }

    #[test]
    fn test_stack_operations() {
        let instructions = inst! {
            push64 [10];
            push32 [20];
            pop64 [30];
            pop32 [40];
        };

        assert_eq!(instructions.len(), 4);
        assert!(matches!(instructions[0], Instruction::Push64 { .. }));
        assert!(matches!(instructions[1], Instruction::Push32 { .. }));
        assert!(matches!(instructions[2], Instruction::Pop64 { .. }));
        assert!(matches!(instructions[3], Instruction::Pop32 { .. }));
    }

    #[test]
    fn test_arithmetic_operations() {
        let instructions = inst! {
            add64 [1], [2];
            sub32 [3], [4];
            mul16 [5], [6];
            div8 [7], [8];
        };

        assert_eq!(instructions.len(), 4);
        assert!(matches!(instructions[0], Instruction::Add64 { .. }));
        assert!(matches!(instructions[1], Instruction::Sub32 { .. }));
        assert!(matches!(instructions[2], Instruction::Mul16 { .. }));
        assert!(matches!(instructions[3], Instruction::Div8 { .. }));
    }

    #[test]
    fn test_signed_operations() {
        let instructions = inst! {
            idiv32 [1], [2];
            imul64 [3], [4];
        };

        assert_eq!(instructions.len(), 2);
        assert!(matches!(instructions[0], Instruction::IDiv32 { .. }));
        assert!(matches!(instructions[1], Instruction::IMul64 { .. }));
    }

    #[test]
    fn test_float_operations() {
        let instructions = inst! {
            addf64 [1], [2];
            subf32 [3], [4];
            mulf64 [5], [6];
            divf32 [7], [8];
            powf64 [9], [10];
        };

        assert_eq!(instructions.len(), 5);
        assert!(matches!(instructions[0], Instruction::AddF64 { .. }));
        assert!(matches!(instructions[1], Instruction::SubF32 { .. }));
        assert!(matches!(instructions[2], Instruction::MulF64 { .. }));
        assert!(matches!(instructions[3], Instruction::DivF32 { .. }));
        assert!(matches!(instructions[4], Instruction::PowF64 { .. }));
    }

    #[test]
    fn test_bitwise_operations() {
        let instructions = inst! {
            and64 [1], [2];
            or32 [3], [4];
            xor16 [5], [6];
            not8 [7];
            shl64 [8], [9];
            shr32 [10], [11];
        };

        assert_eq!(instructions.len(), 6);
        assert!(matches!(instructions[0], Instruction::And64 { .. }));
        assert!(matches!(instructions[1], Instruction::Or32 { .. }));
        assert!(matches!(instructions[2], Instruction::Xor16 { .. }));
        assert!(matches!(instructions[3], Instruction::Not8 { .. }));
        assert!(matches!(instructions[4], Instruction::Shl64 { .. }));
        assert!(matches!(instructions[5], Instruction::Shr32 { .. }));
    }

    #[test]
    fn test_write_with_immediate() {
        let instructions = inst! {
            write64 [50], # [1234];
            write32 [51], # [42];
            write16 [52], # [255];
            write8 [53], # [128];
        };

        assert_eq!(instructions.len(), 4);

        if let Instruction::Write64 { op, value } = instructions[0] {
            assert_eq!(op, Operand::Register(Register::new(50)));
            assert_eq!(value, 1234);
        } else {
            panic!("Expected Write64 instruction");
        }

        if let Instruction::Write32 { op, value } = instructions[1] {
            assert_eq!(op, Operand::Register(Register::new(51)));
            assert_eq!(value, 42);
        } else {
            panic!("Expected Write32 instruction");
        }
    }

    #[test]
    fn test_jumps_with_labels() {
        let instructions = inst! {
            jmp @ [0];
            jmpzero [1], @ [100];
            jmppos [2], @ [0];
            jmpneg [3], @ [100];
        };

        assert_eq!(instructions.len(), 4);

        if let Instruction::Jmp { location } = instructions[0] {
            assert!(matches!(location, Operand::Label(_)));
        } else {
            panic!("Expected Jmp instruction");
        }

        if let Instruction::JmpZero { l1, location } = instructions[1] {
            assert_eq!(l1, Register::new(1));
            assert!(matches!(location, Operand::Label(_)));
        } else {
            panic!("Expected JmpZero instruction");
        }
    }

    #[test]
    fn test_jumps_with_registers() {
        let instructions = inst! {
            jmp [10];
            jmpzero [1], [20];
        };

        assert_eq!(instructions.len(), 2);

        if let Instruction::Jmp { location } = instructions[0] {
            assert!(matches!(location, Operand::Register(_)));
        } else {
            panic!("Expected Jmp instruction");
        }
    }

    #[test]
    fn test_control_flow() {
        let instructions = inst! {
            call [100];
            syscall [0];
            return;
            cmp [1], [2];
        };

        assert_eq!(instructions.len(), 4);
        assert!(matches!(instructions[0], Instruction::Call { .. }));
        assert!(matches!(instructions[1], Instruction::Syscall { .. }));
        assert!(matches!(instructions[2], Instruction::Return));
        assert!(matches!(instructions[3], Instruction::Cmp { .. }));
    }

    #[test]
    fn test_mixed_operand_types() {
        let instructions = inst! {
            mov [10], [15];
            add64 [15], [20];
            jmp @ [42];
            write64 [30], # [9999];
        };

        assert_eq!(instructions.len(), 4);

        if let Instruction::Mov { dest, src } = instructions[0] {
            assert_eq!(dest, Register::new(10));
            assert_eq!(src, Register::new(15));
        } else {
            panic!("Expected Mov instruction");
        }
    }

    #[test]
    fn test_empty_macro() {
        let instructions: Vec<Instruction> = inst! {};
        assert_eq!(instructions.len(), 0);
    }

    #[test]
    fn test_complex_sequence() {
        // A simple loop counting from 0 to 100
        let instructions = inst! {
            write64 [10], # [0];
            write64 [11], # [100];
            add64 [10], [1];
            cmp [10], [11];
            jmppos [10], @ [0];
            return;
        };

        assert_eq!(instructions.len(), 6);
        assert!(matches!(instructions[0], Instruction::Write64 { .. }));
        assert!(matches!(instructions[1], Instruction::Write64 { .. }));
        assert!(matches!(instructions[2], Instruction::Add64 { .. }));
        assert!(matches!(instructions[3], Instruction::Cmp { .. }));
        assert!(matches!(instructions[4], Instruction::JmpPos { .. }));
        assert!(matches!(instructions[5], Instruction::Return));
    }
}
