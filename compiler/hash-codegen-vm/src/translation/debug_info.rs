//! Implements all of the required functionality for generating debug
//! information for the LLVM backend.

use hash_codegen::{
    abi::FnAbi,
    traits::debug::{DebugInfoBuilderMethods, VariableKind},
};
use hash_source::{identifier::Identifier, location::Span};

use super::VMBuilder;

impl DebugInfoBuilderMethods for VMBuilder<'_, '_> {
    fn create_debug_info_scope_for_fn(
        &self,
        _fn_abi: &FnAbi,
        _value: Option<Self::Function>,
    ) -> Self::DebugInfoScope {
        unimplemented!()
    }

    fn create_debug_info_for_variable(
        &self,
        _name: Identifier,
        _ty: hash_ir::ty::ReprTyId,
        _scope: Self::DebugInfoScope,
        _kind: VariableKind,
        _span: Span,
    ) -> Self::DebugInfoVariable {
        unimplemented!()
    }

    fn create_debug_info_location(
        &self,
        _scope: Self::DebugInfoScope,
        _span: Span,
    ) -> Self::DebugInfoLocation {
        unimplemented!()
    }

    fn finalise_debug_info(&self) {
        unimplemented!()
    }
}
