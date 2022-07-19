//! Typechecking traversal for parameter fields that occur from sources
//! such as function definitions, struct definitions, etc.

use hash_ast::{
    ast::{self},
    visitor::{walk, AstVisitor},
};
use hash_reporting::macros::panic_on_span;

use crate::{
    diagnostics::error::TcResult,
    ops::AccessToOpsMut,
    storage::{primitives::Param, AccessToStorage, AccessToStorageMut},
};

use super::TcVisitor;

impl<'gs, 'ls, 'cd, 'src> TcVisitor<'gs, 'ls, 'cd, 'src> {
    /// Function that combines the logic between visiting struct
    /// and function definition parameters/fields. The function
    /// will perform the correct operations based on if there
    /// is a present annotation type, and or default value.
    pub(crate) fn visit_fn_or_struct_param(
        &mut self,
        node: ast::AstNodeRef<ast::Param>,
        ctx: &<Self as AstVisitor>::Ctx,
    ) -> TcResult<Param> {
        let walk::Param { name, ty, default } = walk::walk_param(self, ctx, node)?;

        // Try and figure out a known term...
        let (ty, default_value) = match (ty, default) {
            (Some(annotation_ty), Some(default_value)) => {
                let default_ty = self.typer().infer_ty_of_term(default_value)?;

                // Here, we have to unify both of the provided types...
                let sub = self.unifier().unify_terms(default_ty, annotation_ty)?;

                let default_value_sub = self.substituter().apply_sub_to_term(&sub, default_value);
                let annot_sub = self.substituter().apply_sub_to_term(&sub, annotation_ty);

                (annot_sub, Some(default_value_sub))
            }
            (None, Some(default_value)) => {
                let default_ty = self.typer().infer_ty_of_term(default_value)?;
                (default_ty, Some(default_value))
            }
            (Some(annot_ty), None) => (annot_ty, None),
            (None, None) => panic_on_span!(
                self.source_location(node.span()),
                self.source_map(),
                "tc: found {} field/parameter with no value and type annotation",
                node.origin
            ),
        };

        // Append location to value term
        let ty_span = if node.ty.is_some() {
            node.ty.as_ref().map(|n| n.span())
        } else {
            node.default.as_ref().map(|n| n.span())
        };

        // @@Note: This should never fail since we panic above if there is no span!
        if let Some(ty_span) = ty_span {
            let value_location = self.source_location(ty_span);
            self.location_store_mut().add_location_to_target(ty, value_location);
        }

        Ok(Param { name: Some(name), ty, default_value })
    }

    /// Function that encapsulates the visiting logic for parameters of type
    /// functions.
    pub(crate) fn visit_ty_fn_param(
        &mut self,
        node: ast::AstNodeRef<ast::Param>,
        ctx: &<Self as AstVisitor>::Ctx,
    ) -> TcResult<Param> {
        let walk::Param { name, ty, default } = walk::walk_param(self, ctx, node)?;

        // The location of the param type is either the bound or the name (since
        // <T>     // means <T: Type>):
        let location = self.source_location(
            node.ty.as_ref().map(|ty| ty.span()).unwrap_or_else(|| node.name.span()),
        );

        // The type of the param is the given bound, or Type if no bound was
        // given.
        let runtime_instantiable_trt = self.core_defs().runtime_instantiable_trt;
        let ty = ty.unwrap_or_else(|| self.builder().create_trt_term(runtime_instantiable_trt));

        self.location_store_mut().add_location_to_target(ty, location);

        Ok(Param { ty, name: Some(name), default_value: default })
    }
}
