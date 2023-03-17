//! backends in order to create a backend agnostic interface.

use std::fmt;

use hash_ir::IrCtx;
use hash_layout::{compute::LayoutComputer, LayoutCtx};
use hash_pipeline::settings::CompilerSettings;
use hash_target::{data_layout::HasDataLayout, Target};

use self::{
    constants::ConstValueBuilderMethods, layout::LayoutMethods, misc::MiscBuilderMethods,
    ty::TypeBuilderMethods,
};

pub mod abi;
pub mod builder;
pub mod constants;
pub mod debug;
pub mod intrinsics;
pub mod layout;
pub mod misc;
pub mod ty;

/// This trait represents all of the commonly accessed types that a
/// code generation backend is supposed to have. It is used to provide
/// a common interface for when this crate `hash-codegen` converts the
/// IR into the target backend via the [crate::traits::CodeGen] interface.
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

/// A trait that provides the backend the necessary context to perform
/// code generation.
pub trait HasCtxMethods<'b>: HasDataLayout {
    /// Return a reference to the current [CompilerSettings] for the
    /// workspace.
    fn settings(&self) -> &CompilerSettings;

    /// Return the current compilation target.
    fn target(&self) -> &Target {
        self.settings().target()
    }

    /// Returns a reference to the IR [IrCtx].
    fn ir_ctx(&self) -> &IrCtx;

    /// Create a [LayoutComputer] for the current context.
    fn layout_computer(&self) -> LayoutComputer<'_> {
        LayoutComputer::new(self.layouts(), self.ir_ctx())
    }

    /// Returns a reference to the [LayoutCtx].
    fn layouts(&self) -> &LayoutCtx;
}

/// The core trait of the code generation backend which is used to
/// generate code for a particular backend. This trait provides IR
pub trait Backend<'b>: Sized + BackendTypes + LayoutMethods<'b> {}

pub trait CodeGenMethods<'b>:
    Backend<'b>
    + MiscBuilderMethods<'b>
    + HasCtxMethods<'b>
    + TypeBuilderMethods<'b>
    + ConstValueBuilderMethods<'b>
{
}

// Dummy implementation for `CodeGenMethods` for any T that implements
// those methods too.
impl<'b, T> CodeGenMethods<'b> for T where
    Self: Backend<'b>
        + MiscBuilderMethods<'b>
        + HasCtxMethods<'b>
        + TypeBuilderMethods<'b>
        + ConstValueBuilderMethods<'b>
{
}

pub trait Codegen<'b>:
    Backend<'b> + std::ops::Deref<Target = <Self as Codegen<'b>>::CodegenCtx>
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
