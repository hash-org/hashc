//! Contains a trait for emitting debug information for specific
//! backends. This trait is used to provide a common interface for
//! when this crate `hash-codegen` converts the IR into the target
//! backend via the [crate::traits::CodeGen] interface, and when it adds
//! debug information to all of the generated IR.

use hash_ir::ty::IrTyId;
use hash_source::{identifier::Identifier, location::SourceLocation};

use super::BackendTypes;

/// Represents the kind of variable that is being references within
/// a particular body, whether it is an argument, a local variable.
pub enum VariableKind {
    /// An argument that was passed into a function, with the index
    /// of the argument.
    Argument(usize),

    /// A local variable that exists within the function body.
    Local,
}

/// This trait represents an interface for the building methods to generate
/// debug information from the Hash IR.
pub trait BuildDebugInfoMethods: BackendTypes {
    /// Create a new [`BackendTypes::DebugInfoScope`] object which represents a
    /// particular scope in the source code. This is attached to a function.
    fn create_debug_info_scope_for_fn(
        &self,
        fn_abi: (),
        value: Option<Self::Function>,
    ) -> Self::DebugInfoScope;

    /// Create a new [`BackendTypes::DebugInfoVariable`] which represents a
    /// particular variable entry within the function. This debug information
    /// records the name, type, kind and position of the variable definition.
    fn create_debug_info_for_variable(
        &self,
        name: Identifier,
        ty: IrTyId,
        scope: Self::DebugInfoScope,
        kind: VariableKind,
        span: SourceLocation,
    ) -> Self::DebugInfoVariable;

    /// Create a new [`BackendTypes::DebugInfoLocation`] which represents a
    /// particular location in the source code. This debug information records
    /// the source location and the scope that the location is within.
    fn create_debug_info_location(
        &self,
        scope: Self::DebugInfoScope,
        span: SourceLocation,
    ) -> Self::DebugInfoLocation;

    /// Finish the process of generating debug information for a particular
    /// function. This maybe used to fill any parts with filler values or to
    /// validate that the provided debug information is valid.
    fn finalise_debug_info(&self);
}
