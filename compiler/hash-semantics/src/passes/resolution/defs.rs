//! Resolution for existing definitions.
//!
//! This module re-traverses existing definitions and resolves their
//! inner terms, which were left as holes after the discovery pass.

use std::cell::Cell;

use hash_ast::ast::{self, AstNodeRef};
use hash_reporting::diagnostic::Diagnostics;
use hash_tir::{
    data::{CtorDefId, DataDefCtors},
    directives::AppliedDirectives,
    environment::env::AccessToEnv,
    mods::{ModDefId, ModMemberValue},
    tys::Ty,
    utils::common::CommonUtils,
};
use hash_utils::store::{PartialStore, SequenceStore, SequenceStoreKey, Store};

use super::{scoping::ContextKind, ResolutionPass};
use crate::{
    diagnostics::error::{SemanticError, SemanticResult},
    environment::sem_env::AccessToSemEnv,
    ops::common::CommonOps,
    passes::ast_utils::{AstPass, AstUtils},
};

impl<'tc> ResolutionPass<'tc> {
    /// Resolve the inner terms of the given [`ast::ModDef`].
    ///
    /// Returns a void term to assign to the mod def.
    pub(super) fn resolve_ast_mod_def_inner_terms(
        &self,
        node: AstNodeRef<ast::ModDef>,
    ) -> SemanticResult<ModDefId> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_mod_def_inner_terms(mod_def_id, node.block.members())?;
        Ok(mod_def_id)
    }

    /// Resolve the inner terms of the given [`ast::Module`].
    pub(super) fn resolve_ast_module_inner_terms(
        &self,
        node: AstNodeRef<ast::Module>,
    ) -> SemanticResult<ModDefId> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
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
            self.ast_info().data_defs().get_data_by_node(originating_node.id()).unwrap();
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
                    attempt(self.resolve_params_from_ast_params(
                        &struct_def.ty_params,
                        true,
                        data_def_id.into(),
                    ));

                    // Struct variant
                    let struct_ctor =
                        self.stores().data_def().map_fast(data_def_id, |def| match def.ctors {
                            DataDefCtors::Defined(id) => {
                                // There should only be one variant
                                assert!(id.len() == 1);
                                CtorDefId(id, 0)
                            },
                            DataDefCtors::Primitive(_) => unreachable!() // No primitive user-defined structs
                        });

                    self.scoping().enter_scope(
                        ContextKind::Environment,
                        || {
                            // Struct fields
                            attempt(self.resolve_params_from_ast_params(
                                &struct_def.fields,
                                false,
                                struct_ctor.into(),
                            ));
                        },
                    );
                }
                ast::Expr::EnumDef(enum_def) => {
                    // Type parameters
                    attempt(self.resolve_params_from_ast_params(
                        &enum_def.ty_params,
                        true,
                        data_def_id.into(),
                    ));

                    // Enum variants
                    let data_def_ctors =
                        self.stores().data_def().map_fast(data_def_id, |def| match def.ctors {
                            DataDefCtors::Defined(id) => id,
                            DataDefCtors::Primitive(_) => unreachable!() // No primitive user-defined enums
                        });
                    assert!(data_def_ctors.len() == enum_def.entries.len());

                    for (i, variant) in enum_def.entries.ast_ref_iter().enumerate() {
                        self.scoping().enter_scope(
                            ContextKind::Environment,
                            || {
                                // Variant fields
                                attempt(self.resolve_params_from_ast_params(
                                    &variant.fields,
                                    false,
                                    CtorDefId(data_def_ctors, i).into(),
                                ));

                                // Variant type
                                attempt(self.resolve_params_from_ast_params(
                                    &variant.fields,
                                    false,
                                    CtorDefId(data_def_ctors, i).into(),
                                ));

                                // Variant indices
                                if let Some(variant_ty) = variant.ty.as_ref() {
                                    if let Some(result) = self.try_or_add_error(
                                        self.make_ty_from_ast_ty(variant_ty.ast_ref()),
                                    ) {
                                        match self.get_ty(result) {
                                            Ty::Data(d) if d.data_def == data_def_id => {
                                                // Variant type is the same as the enum type
                                                self.stores().ctor_defs().modify_fast(data_def_ctors, |ctors| {
                                                    ctors[i].result_args = d.args;
                                                });
                                            }
                                            _ => {
                                                self.diagnostics().add_error(
                                                    SemanticError::EnumTypeAnnotationMustBeOfDefiningType {
                                                       location: self.node_location(variant_ty.ast_ref())}
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
    fn use_expr_as_mod_def_declaration_and_get_rhs<'a>(
        &self,
        member: ModMemberValue,
        member_expr: ast::AstNodeRef<'a, ast::Expr>,
    ) -> ast::AstNodeRef<'a, ast::Expr> {
        // By this point, all members should be declarations (caught at pre-TC)
        match member_expr.body() {
            ast::Expr::Declaration(decl) => decl.value.as_ref().unwrap().ast_ref(),
            ast::Expr::Directive(directive) => {
                // Add all directives to the target
                self.stores().directives().insert(
                    member.into(),
                    AppliedDirectives {
                        directives: directive.directives.iter().map(|d| d.ident).collect(),
                    },
                );

                // Recurse to the inner declaration
                self.use_expr_as_mod_def_declaration_and_get_rhs(
                    member,
                    directive.subject.ast_ref(),
                )
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
            let members = self.stores().mod_def().map_fast(mod_def_id, |def| def.members);

            for (i, member_expr) in members.to_index_range().zip(member_exprs) {
                let member_value =
                    self.stores().mod_members().map_fast(members, |members| members[i].value);
                let member_rhs_expr =
                    self.use_expr_as_mod_def_declaration_and_get_rhs(member_value, member_expr);

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
                                        mod_def.block.members(),
                                    ))
                                    .is_none()
                                {
                                    found_error = true;
                                }
                            }
                            ast::Expr::Import(import_expr) => {
                                // If it's an import, resolve the source
                                let source_id = self
                                    .source_map()
                                    .get_id_by_path(&import_expr.data.resolved_path)
                                    .unwrap();
                                self.current_source_info().with_source_id(source_id, || {
                                    ResolutionPass::new(self.sem_env()).pass_source()
                                })?;
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
