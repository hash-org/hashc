//! Implements all of the required functionality for generating debug
//! information for the LLVM backend.

use hash_codegen::{
    abi::FnAbi,
    traits::debug::{BuildDebugInfoMethods, VariableKind},
};
use hash_source::{identifier::Identifier, location::SourceLocation};

use super::Builder;

impl<'b> BuildDebugInfoMethods for Builder<'b> {
    fn create_debug_info_scope_for_fn(
        &self,
        fn_abi: &FnAbi,
        value: Option<Self::Function>,
    ) -> Self::DebugInfoScope {
        todo!()
    }

    fn create_debug_info_for_variable(
        &self,
        name: Identifier,
        ty: hash_ir::ty::IrTyId,
        scope: Self::DebugInfoScope,
        kind: VariableKind,
        span: SourceLocation,
    ) -> Self::DebugInfoVariable {
        todo!()
    }

    fn create_debug_info_location(
        &self,
        scope: Self::DebugInfoScope,
        span: SourceLocation,
    ) -> Self::DebugInfoLocation {
        todo!()
    }

    fn finalise_debug_info(&self) {
        todo!()
    }
}
