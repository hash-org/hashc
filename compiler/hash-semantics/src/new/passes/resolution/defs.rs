//! Resolution for existing definitions.
//!
//! This module re-traverses existing definitions and resolves their
//! inner terms, which were left as holes after the discovery pass.

use hash_ast::ast::{self, AstNodeRef};
use hash_tir::new::{
    environment::env::AccessToEnv,
    mods::{ModDefId, ModMemberValue},
};
use hash_utils::store::{SequenceStore, SequenceStoreKey, Store};

use super::{scoping::ContextKind, ResolutionPass};
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    environment::tc_env::AccessToTcEnv,
    ops::common::CommonOps,
};

impl<'tc> ResolutionPass<'tc> {
    /// Resolve the inner terms of the given [`ast::ModDef`].
    ///
    /// Returns a void term to assign to the mod def.
    pub(super) fn resolve_ast_mod_def_inner_terms(
        &self,
        node: AstNodeRef<ast::ModDef>,
    ) -> TcResult<ModDefId> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_mod_def_inner_terms(mod_def_id, node.block.members())?;
        Ok(mod_def_id)
    }

    /// Resolve the inner terms of the given [`ast::Module`].
    pub(super) fn resolve_ast_module_inner_terms(
        &self,
        node: AstNodeRef<ast::Module>,
    ) -> TcResult<ModDefId> {
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
    ) -> TcResult<()> {
        let data_def_id =
            self.ast_info().data_defs().get_data_by_node(originating_node.id()).unwrap();
        self.scoping().enter_scope(data_def_id.into(), ContextKind::Environment, || {
            let mut found_error = false;

            match originating_node.body() {
                // Resolve the data of the definition depending on its kind:
                ast::Expr::StructDef(struct_def) => {
                    // Type parameters
                    if self
                        .try_or_add_error(
                            self.resolve_params_from_ast_params(&struct_def.ty_params, true),
                        )
                        .is_none()
                    {
                        found_error = true;
                    }

                    // Struct fields
                    if self
                        .try_or_add_error(
                            self.resolve_params_from_ast_params(&struct_def.fields, false),
                        )
                        .is_none()
                    {
                        found_error = true;
                    }
                }
                ast::Expr::EnumDef(enum_def) => {
                    // Type parameters
                    if self
                        .try_or_add_error(
                            self.resolve_params_from_ast_params(&enum_def.ty_params, true),
                        )
                        .is_none()
                    {
                        found_error = true;
                    }
                    for variant in enum_def.entries.ast_ref_iter() {
                        // Variant fields
                        if self
                            .try_or_add_error(
                                self.resolve_params_from_ast_params(&variant.fields, false),
                            )
                            .is_none()
                        {
                            found_error = true;
                        }
                    }
                }
                _ => unreachable!(),
            }

            if found_error {
                Err(TcError::Signal)
            } else {
                Ok(())
            }
        })
    }

    /// Resolve the inner terms of the given module definition, by calling
    /// `make_{term,ty,pat}_from_*` on its contents.
    ///
    /// This modifies the given module definition.
    fn resolve_mod_def_inner_terms<'a>(
        &self,
        mod_def_id: ModDefId,
        member_exprs: impl Iterator<Item = ast::AstNodeRef<'a, ast::Expr>>,
    ) -> TcResult<()> {
        self.scoping().enter_scope(mod_def_id.into(), ContextKind::Environment, || {
            let mut found_error = false;
            let members = self.stores().mod_def().map_fast(mod_def_id, |def| def.members);

            for (i, member_expr) in members.to_index_range().zip(member_exprs) {
                let member_value =
                    self.stores().mod_members().map_fast(members, |members| members[i].value);

                // By this point, all members should be declarations (caught at pre-TC)
                let member_rhs_expr = match member_expr.body() {
                    ast::Expr::Declaration(decl) => decl.value.as_ref().unwrap().ast_ref(),
                    _ => unreachable!(),
                };

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
                        // Must be a module definition node.
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
                            _ => unreachable!(),
                        }
                    }
                    ModMemberValue::Fn(_) => {
                        // Must be a function definition node.
                        match member_rhs_expr.body() {
                            ast::Expr::TyFnDef(ty_fn_def) => {
                                if self
                                    .try_or_add_error(self.make_term_from_ast_ty_fn_def(
                                        member_rhs_expr.with_body(ty_fn_def),
                                    ))
                                    .is_none()
                                {
                                    found_error = true;
                                }
                            }
                            ast::Expr::FnDef(fn_def) => {
                                if self
                                    .try_or_add_error(self.make_term_from_ast_fn_def(
                                        member_rhs_expr.with_body(fn_def),
                                    ))
                                    .is_none()
                                {
                                    found_error = true;
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }

            if found_error {
                Err(TcError::Signal)
            } else {
                Ok(())
            }
        })
    }
}
