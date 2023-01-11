//! Resolution for existing definitions.
//!
//! This module re-traverses existing definitions and resolves their
//! inner terms, which were left as holes after the discovery pass.

use hash_ast::ast::{self, AstNodeRef};
use hash_types::new::{
    data::{DataDefCtors, DataDefId},
    environment::env::AccessToEnv,
    mods::{ModDefId, ModMemberValue},
    terms::TermId,
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
    ///
    /// Returns a void term to assign to the struct def.
    pub(super) fn resolve_ast_struct_def_inner_terms(
        &self,
        node: AstNodeRef<ast::StructDef>,
    ) -> TcResult<TermId> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_data_def_inner_terms(data_def_id)?;
        // @@Reconsider: is void the right thing to return here? Maybe we should have
        // meta-terms for defs?
        Ok(self.new_void_term())
    }

    /// Resolve the inner terms of the given [`ast::EnumDef`].
    ///
    /// Returns a void term to assign to the enum def.
    pub(super) fn resolve_ast_enum_def_inner_terms(
        &self,
        node: AstNodeRef<ast::EnumDef>,
    ) -> TcResult<TermId> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_data_def_inner_terms(data_def_id)?;
        Ok(self.new_void_term())
    }

    /// Resolve the inner terms of the given [`ast::ModDef`].
    ///
    /// Returns a void term to assign to the mod def.
    pub(super) fn resolve_ast_mod_def_inner_terms(
        &self,
        node: AstNodeRef<ast::ModDef>,
    ) -> TcResult<TermId> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_mod_def_inner_terms(mod_def_id, |i| node.block.statements[i].ast_ref())?;
        Ok(self.new_void_term())
    }

    /// Resolve the inner terms of the given [`ast::Module`].
    pub(super) fn resolve_ast_module_inner_terms(
        &self,
        node: AstNodeRef<ast::Module>,
    ) -> TcResult<()> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.resolve_mod_def_inner_terms(mod_def_id, |i| node.contents[i].ast_ref())
    }

    /// Resolve the inner terms of the given data definition, by calling
    /// `make_{term,ty,pat}_from_*` on its contents.
    ///
    /// This modifies the given data definition.
    fn resolve_data_def_inner_terms(&self, data_def_id: DataDefId) -> TcResult<()> {
        self.context_ops().enter_scope(data_def_id.into(), || {
            let _found_error = false;
            let ctors = self.stores().data_def().map_fast(data_def_id, |def| def.ctors);

            match ctors {
                DataDefCtors::Primitive(_) => {} // Nothing to do
                DataDefCtors::Defined(_ctors) => {
                    // for i in ctors.to_index_range() {
                    //     self.resolve_params_from_ast_params(params)
                    // }
                    todo!()
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
        rhs_expr_of_member: impl Fn(usize) -> AstNodeRef<'a, ast::Expr>,
    ) -> TcResult<()> {
        self.context_ops().enter_scope(mod_def_id.into(), || {
            let mut found_error = false;
            let members = self.stores().mod_def().map_fast(mod_def_id, |def| def.members);

            for i in members.to_index_range() {
                let member_value =
                    self.stores().mod_members().map_fast(members, |members| members[i].value);
                let member_expr = rhs_expr_of_member(i);

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
                        match member_expr.body() {
                            ast::Expr::ModDef(mod_def) => {
                                let rhs_expr_of_nested =
                                    |i: usize| mod_def.block.statements[i].ast_ref();
                                if self
                                    .try_or_add_error(self.resolve_mod_def_inner_terms(
                                        mod_def_id,
                                        rhs_expr_of_nested,
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
                        match member_expr.body() {
                            ast::Expr::TyFnDef(ty_fn_def) => {
                                if self
                                    .try_or_add_error(self.make_term_from_ast_ty_fn_def(
                                        member_expr.with_body(ty_fn_def),
                                    ))
                                    .is_none()
                                {
                                    found_error = true;
                                }
                            }
                            ast::Expr::FnDef(fn_def) => {
                                if self
                                    .try_or_add_error(
                                        self.make_term_from_ast_fn_def(
                                            member_expr.with_body(fn_def),
                                        ),
                                    )
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
