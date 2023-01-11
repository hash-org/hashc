//! Resolution for existing definitions.
//!
//! This module re-traverses existing definitions and resolves their
//! inner terms, which were left as holes after the discovery pass.

use hash_ast::ast::{self, AstNodeRef};
use hash_types::new::{
    data::{DataDefCtors, DataDefId},
    environment::env::AccessToEnv,
    mods::{ModDefId, ModMemberValue},
};
use hash_utils::store::{SequenceStore, SequenceStoreKey, Store};

use super::ResolutionPass;
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    environment::tc_env::AccessToTcEnv,
    ops::{common::CommonOps, AccessToOps},
};

impl<'tc> ResolutionPass<'tc> {
    /// Resolve the inner terms of the given [`ast::StructDef`].
    pub(super) fn resolve_ast_struct_def_inner_terms(
        &self,
        node: AstNodeRef<ast::StructDef>,
    ) -> TcResult<DataDefId> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_data_def_inner_terms(data_def_id)?;
        // @@Reconsider: is void the right thing to return here? Maybe we should have
        // meta-terms for defs?
        Ok(data_def_id)
    }

    /// Resolve the inner terms of the given [`ast::EnumDef`].
    pub(super) fn resolve_ast_enum_def_inner_terms(
        &self,
        node: AstNodeRef<ast::EnumDef>,
    ) -> TcResult<DataDefId> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_data_def_inner_terms(data_def_id)?;
        Ok(data_def_id)
    }

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

    /// Resolve the inner terms of the given data definition, by calling
    /// `make_{term,ty,pat}_from_*` on its contents.
    ///
    /// This modifies the given data definition.
    fn resolve_data_def_inner_terms(
        &self,
        data_def_id: DataDefId,
        // The two indices of the function are `(def_param_index,
        // param_index)`.
        // ctor_params: impl Fn(usize, usize) -> AstNodeRef<'a, ast::Param>,
    ) -> TcResult<()> {
        self.context_ops().enter_scope(data_def_id.into(), || {
            let _found_error = false;
            let ctors = self.stores().data_def().map_fast(data_def_id, |def| def.ctors);

            match ctors {
                DataDefCtors::Primitive(_) => {} // Nothing to do
                DataDefCtors::Defined(ctors) => {
                    for _i in ctors.to_index_range() {
                        self.stores().ctor_defs().map_fast(ctors, |_ctor_def| {})
                    }
                    // @@Todo: data defs
                }
            }

            Ok(())
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
        self.context_ops().enter_scope(mod_def_id.into(), || {
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
                    ModMemberValue::Data(data_def_id) => {
                        if self
                            .try_or_add_error(self.resolve_data_def_inner_terms(data_def_id))
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
