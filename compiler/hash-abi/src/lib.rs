//! This module defines types and logic that deal with ABIs (Application Binary
//! Interfaces). This is needed in order to communicate with the outside world
//! and to be able to call functions from other languages, but to also provide
//! information to code generation backends about how values are represented.

use hash_layout::TyInfo;
use hash_target::{abi::AbiRepresentation, alignment::Alignments, size::Size};

/// Defines the available calling conventions that can be
/// used when invoking functions with the ABI.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CallingConvention {
    /// The C calling convention.
    ///
    /// Equivalent to the `ccc` calling convention in LLVM.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#calling-conventions> (ccc)
    C,

    /// Cold calling convention for functions that are unlikely to be called.
    ///
    /// Equivalent to the `coldcc` calling convention in LLVM.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#calling-conventions> (coldcc)
    Cold,
}

/// Defines ABI specific information about a function.
///
/// @@TODO: Do we need to record information about variadics here (when we add
/// them)?
#[derive(Debug)]
pub struct FnAbi {
    /// All the types of the arguments in order, and how they should
    /// be passed to the function (as per convention).
    pub args: Box<[ArgAbi]>,

    /// The return type of the function, and how it should be returned
    /// (as per convention).
    pub ret_abi: ArgAbi,

    /// The calling convention that should be used when invoking the function.
    pub calling_convention: CallingConvention,
}

/// Defines ABI specific information about an argument. [ArgAbi] is also
/// used to denote the return type of the function it has similar conventions
/// to function arguments.
#[derive(Debug)]
pub struct ArgAbi {
    /// The type of the argument.
    pub info: TyInfo,

    /// The ABI representation of the argument.
    pub abi: AbiRepresentation,

    /// The alignment of the argument.
    pub align: Alignments,

    /// The size of the argument.
    pub size: Size,
}
