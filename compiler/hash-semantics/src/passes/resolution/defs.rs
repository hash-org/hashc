//! Resolution for existing definitions.
//!
//! This module re-traverses existing definitions and resolves their
//! inner terms, which were left as holes after the discovery pass.

use std::cell::Cell;

use hash_ast::ast::{self, AstNodeRef};
use hash_reporting::diagnostic::Diagnostics;
use hash_storage::store::{statics::StoreId, SequenceStoreKey};
use hash_tir::tir::{DataDefCtors, ModDefId, ModMemberValue, NodesId, Ty};

use super::{scoping::ContextKind, ResolutionPass};
use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
    passes::analysis_pass::AnalysisPass,
};

impl<'env, E: SemanticEnv + 'env> ResolutionPass<'env, E> {
    /// Resolve the inner terms of the given [`ast::ModDef`].
    ///
    /// Returns a void term to assign to the mod def.
    pub(super) fn resolve_ast_mod_def_inner_terms(
        &self,
        node: AstNodeRef<ast::ModDef>,
    ) -> SemanticResult<ModDefId> {
        let mod_def_id = self.ast_info.mod_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_mod_def_inner_terms(mod_def_id, node.entries.ast_ref_iter())?;
        Ok(mod_def_id)
    }

    /// Resolve the inner terms of the given [`ast::Module`].
    pub(super) fn resolve_ast_module_inner_terms(
        &self,
        node: AstNodeRef<ast::Module>,
    ) -> SemanticResult<ModDefId> {
        let mod_def_id = self.ast_info.mod_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_mod_def_inner_terms(mod_def_id, node.contents.ast_ref_iter())?;
        Ok(mod_def_id)
    }

    /// Resolve the inner terms of the given data definition, which must be
    /// either a struct or enum node.
    ///
    /// This modifies the given data definition.
    pub(super) fn resolve_data_def_inner_terms(
        &self,
        originating_node: ast::AstNodeRef<ast::Expr>,
    ) -> SemanticResult<()> {
        let data_def_id =
            self.ast_info.data_defs().get_data_by_node(originating_node.id()).unwrap();
        self.scoping().enter_scope(ContextKind::Environment, || {
            let found_error = &Cell::new(false);
            let attempt = |err| {
                if self.try_or_add_error(err).is_none() {
                    found_error.set(true);
                }
            };

            match originating_node.body() {
                // Resolve the data of the definition depending on its kind:
                ast::Expr::StructDef(struct_def) => {
                    // Type parameters
                    if let Some(ty_params) = &struct_def.ty_params {
                        attempt(self.resolve_params_from_ast_ty_params(
                            ty_params
                        ));
                    }

                    self.scoping().enter_scope(
                        ContextKind::Environment,
                        || {
                            // Struct fields
                            attempt(self.resolve_params_from_ast_params(
                                &struct_def.fields,
                                false,
                            ));
                        },
                    );
                }
                ast::Expr::EnumDef(enum_def) => {
                    // Type parameters
                    if let Some(ty_params) = &enum_def.ty_params {
                        attempt(self.resolve_params_from_ast_ty_params(
                            ty_params
                        ));
                    }

                    // Enum variants
                    let data_def_ctors =
                        match data_def_id.borrow().ctors {
                            DataDefCtors::Defined(id) => id,
                            DataDefCtors::Primitive(_) => unreachable!() // No primitive user-defined enums
                        };
                    assert!(data_def_ctors.len() == enum_def.entries.len());

                    for (i, variant) in enum_def.entries.ast_ref_iter().enumerate() {
                        self.scoping().enter_scope(
                            ContextKind::Environment,
                            || {
                                // Variant fields
                                if let Some(fields) = &variant.fields {
                                    attempt(self.resolve_params_from_ast_params(
                                        fields,
                                        false,
                                    ));
                                }

                                // Variant indices
                                if let Some(variant_ty) = variant.ty.as_ref() {
                                    if let Some(result) = self.try_or_add_error(
                                        self.make_ty_from_ast_ty(variant_ty.ast_ref()),
                                    ) {
                                        match *result.value() {
                                            Ty::DataTy(d) if d.data_def == data_def_id => {
                                                // Variant type is the same as the enum type
                                                data_def_ctors.value().borrow_mut()[i].result_args = d.args;
                                            }
                                            _ => {
                                                self.diagnostics().add_error(
                                                    SemanticError::EnumTypeAnnotationMustBeOfDefiningType {
                                                       location: variant_ty.span()
                                                    }
                                                );
                                            }
                                        }
                                    }
                                }
                            },
                        )
                    }
                }
                _ => unreachable!("Expected a data definition node"),
            }

            if found_error.get() {
                Err(SemanticError::Signal)
            } else {
                Ok(())
            }
        })
    }

    /// Use the given expression as the declaration of a module definition for
    /// the given member.
    ///
    /// This registers any directives and returns the RHS of the declaration.
    fn use_expr_as_mod_def_declaration_and_get_rhs(
        member_expr: ast::AstNodeRef<'_, ast::Expr>,
    ) -> ast::AstNodeRef<'_, ast::Expr> {
        // By this point, all members should be declarations (caught at pre-TC)
        match member_expr.body() {
            ast::Expr::Declaration(decl) => decl.value.ast_ref(),
            ast::Expr::Macro(invocation) => {
                // Recurse to the inner declaration
                Self::use_expr_as_mod_def_declaration_and_get_rhs(invocation.subject.ast_ref())
            }
            _ => unreachable!("Found non-declaration in module definition"),
        }
    }

    /// Resolve the inner terms of the given module definition, by calling
    /// `make_{term,ty,pat}_from_*` on its contents.
    ///
    /// This modifies the given module definition.
    pub(super) fn resolve_mod_def_inner_terms<'a>(
        &self,
        mod_def_id: ModDefId,
        member_exprs: impl Iterator<Item = ast::AstNodeRef<'a, ast::Expr>>,
    ) -> SemanticResult<()> {
        self.scoping().enter_scope(ContextKind::Environment, || {
            self.scoping().add_mod_members(mod_def_id);

            let mut found_error = false;
            let members = mod_def_id.borrow().members;

            for (i, member_expr) in members.to_index_range().zip(member_exprs) {
                let member_value = members.elements().borrow()[i].value;
                let member_rhs_expr =
                    Self::use_expr_as_mod_def_declaration_and_get_rhs(member_expr);

                match member_value {
                    ModMemberValue::Data(_) => {
                        // Must be a struct or enum (handled in `resolve_data_def_inner_terms`)
                        if self
                            .try_or_add_error(self.resolve_data_def_inner_terms(member_rhs_expr))
                            .is_none()
                        {
                            found_error = true;
                        }
                    }
                    ModMemberValue::Mod(mod_def_id) => {
                        // If be a module definition node, recurse into it.
                        match member_rhs_expr.body() {
                            ast::Expr::ModDef(mod_def) => {
                                if self
                                    .try_or_add_error(self.resolve_mod_def_inner_terms(
                                        mod_def_id,
                                        mod_def.entries.ast_ref_iter(),
                                    ))
                                    .is_none()
                                {
                                    found_error = true;
                                }
                            }
                            ast::Expr::Import(import_expr) => {
                                // If it's an import, resolve the source
                                let source_id = import_expr.data.source;
                                ResolutionPass::new(self.env, self.ast_info)
                                    .pass_source(source_id)?
                            }
                            _ => {}
                        }
                    }
                    ModMemberValue::Fn(_) => {
                        if self
                            .try_or_add_error(self.make_term_from_ast_expr(member_rhs_expr))
                            .is_none()
                        {
                            found_error = true;
                        }
                    }
                    ModMemberValue::Intrinsic(_) => {
                        // Nothing to do
                    }
                }
            }

            if found_error {
                Err(SemanticError::Signal)
            } else {
                Ok(())
            }
        })
    }
}
