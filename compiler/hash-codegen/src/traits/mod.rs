//! backends in order to create a backend agnostic interface.

use std::fmt;

use self::{
    constants::BuildConstValueMethods, ctx::HasCtxMethods, debug::BuildDebugInfoMethods,
    target::HasTargetSpec, ty::BuildTypeMethods,
};

pub mod builder;
pub mod constants;
pub mod ctx;
pub mod debug;
pub mod intrinsics;
pub mod layout;
pub mod target;
pub mod ty;

/// This trait represents all of the commonly accessed types that a
/// code generation backend is supposed to have. It is used to provide
/// a common interface for when this crate `hash-codegen` converts the
/// IR into the target backend via the [BackendBuilder] interface.
pub trait BackendTypes {
    /// A value that has been generated by a particular backend.
    type Value: CodeGenObject;

    /// A function that has been generated by the particular backend.
    type Function: CodeGenObject;

    /// A type that has been generated by a particular backend.
    type Type: CodeGenObject;

    /// A basic block structure within the specific backend, used as a
    /// chunk of a generated function with particular control flow
    /// properties.
    type BasicBlock: Copy;

    /// Debug information about a particular scope.
    type DebugInfoScope: Copy;

    /// Debug information about a particular "location" which can be
    /// mapped back to a particular point in the source.
    type DebugInfoLocation: Copy;

    /// Debug information about a particular variable.
    type DebugInfoVariable: Copy;
}

pub trait CodeGenObject: Copy + PartialEq + fmt::Debug {}
impl<T: Copy + PartialEq + fmt::Debug> CodeGenObject for T {}

/// The core trait of the code generation backend which is used to
/// generate code for a particular backend. This trait provides IR
pub trait Backend<'b>: Sized + BackendTypes {}

pub trait CodeGenMethods<'b>:
    Backend<'b>
    + HasCtxMethods<'b>
    + BuildTypeMethods<'b>
    + BuildConstValueMethods<'b>
    + BuildDebugInfoMethods
    + HasTargetSpec
{
}

pub trait HasCodegen<'b>:
    Backend<'b> + std::ops::Deref<Target = <Self as HasCodegen<'b>>::CodegenCtx>
{
    /// The type of the codegen context, all items within the context can access
    /// all of the methods that are provided via [CodeGenMethods]
    type CodegenCtx: CodeGenMethods<'b>
        + BackendTypes<
            Value = Self::Value,
            Function = Self::Function,
            BasicBlock = Self::BasicBlock,
            Type = Self::Type,
            DebugInfoLocation = Self::DebugInfoLocation,
            DebugInfoScope = Self::DebugInfoScope,
            DebugInfoVariable = Self::DebugInfoVariable,
        >;
}