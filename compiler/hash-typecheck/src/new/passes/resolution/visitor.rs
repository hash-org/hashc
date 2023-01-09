//! AST visitor for the resolution pass.

use hash_ast::{
    ast::{self, AstNodeRef},
    ast_visitor_default_impl,
    visitor::walk,
};
use hash_types::new::environment::{context::ScopeKind, env::AccessToEnv};

use super::{scoping::ContextKind, InExpr, ResolutionPass};
use crate::new::{
    diagnostics::error::TcError, environment::tc_env::AccessToTcEnv, ops::common::CommonOps,
};

impl ast::AstVisitor for ResolutionPass<'_> {
    type Error = TcError;
    ast_visitor_default_impl!(
        hiding: Module,
        Declaration,
        ModDef,
        StructDef,
        EnumDef,
        FnDef,
        TyFnDef,
        BodyBlock,
        MatchCase,
        Expr,
        Ty,
        AccessTy,
        AccessPat,
        AccessExpr,
        BindingPat,
        NamedTy,
        VariableExpr,
        Pat,
    );

    type ModuleRet = ();
    fn visit_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.scoping().enter_scope(ScopeKind::Mod(mod_def_id), ContextKind::Environment, || {
            walk::walk_module(self, node)
        })?;
        Ok(())
    }

    type ModDefRet = ();
    fn visit_mod_def(
        &self,
        node: ast::AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.scoping().enter_scope(ScopeKind::Mod(mod_def_id), ContextKind::Environment, || {
            walk::walk_mod_def(self, node)
        })?;
        Ok(())
    }

    type StructDefRet = ();
    fn visit_struct_def(
        &self,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.scoping().enter_scope(
            ScopeKind::Data(data_def_id),
            ContextKind::Environment,
            || walk::walk_struct_def(self, node),
        )?;
        Ok(())
    }

    type EnumDefRet = ();
    fn visit_enum_def(
        &self,
        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.scoping().enter_scope(
            ScopeKind::Data(data_def_id),
            ContextKind::Environment,
            || walk::walk_enum_def(self, node),
        )?;
        Ok(())
    }

    type FnDefRet = ();
    fn visit_fn_def(
        &self,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let fn_def_id = self.ast_info().fn_defs().get_data_by_node(node.id()).unwrap();
        self.scoping().enter_scope(ScopeKind::Fn(fn_def_id), ContextKind::Environment, || {
            walk::walk_fn_def(self, node)
        })?;
        Ok(())
    }

    type TyFnDefRet = ();
    fn visit_ty_fn_def(
        &self,
        node: ast::AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let fn_def_id = self.ast_info().fn_defs().get_data_by_node(node.id()).unwrap();
        self.scoping().enter_scope(ScopeKind::Fn(fn_def_id), ContextKind::Environment, || {
            walk::walk_ty_fn_def(self, node)
        })?;
        Ok(())
    }

    type BodyBlockRet = ();
    fn visit_body_block(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        match self.ast_info().stacks().get_data_by_node(node.id()) {
            Some(stack_id) => {
                // This is a stack, so we need to enter its scope.
                self.scoping().enter_scope(
                    ScopeKind::Stack(stack_id),
                    ContextKind::Environment,
                    || {
                        walk::walk_body_block(self, node)?;
                        Ok(())
                    },
                )?;
            }
            None => {
                // This is not a stack, so it must be some other block handled
                // elsewhere.
                walk::walk_body_block(self, node)?;
            }
        };
        Ok(())
    }

    type DeclarationRet = ();
    fn visit_declaration(
        &self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        // If we are in a stack, then we need to add the declaration to the
        // stack's scope. Otherwise the declaration is handled higher up.
        if let ScopeKind::Stack(_) = self.context().get_current_scope_kind() {
            self.scoping().for_each_stack_member_of_pat(node.pat.ast_ref(), |member| {
                self.scoping().add_stack_binding(member);
            });
        }
        walk::walk_declaration(self, node)?;
        Ok(())
    }

    type MatchCaseRet = ();
    fn visit_match_case(
        &self,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let stack_id = self.ast_info().stacks().get_data_by_node(node.id()).unwrap();
        // Each match case has its own scope, so we need to enter it, and add all the
        // pattern bindings to the context.
        self.scoping().enter_scope(ScopeKind::Stack(stack_id), ContextKind::Environment, || {
            self.scoping().for_each_stack_member_of_pat(node.pat.ast_ref(), |member| {
                self.scoping().add_stack_binding(member);
            });
            walk::walk_match_case(self, node)?;
            Ok(())
        })
    }

    type TyRet = ();
    fn visit_ty(&self, node: ast::AstNodeRef<ast::Ty>) -> Result<Self::TyRet, Self::Error> {
        if let ContextKind::Access(_, _) = self.scoping().get_current_context_kind() {
            // Handled by path resolution.
            return Ok(());
        }

        self.in_expr.enter(InExpr::Ty, || {
            walk::walk_ty(self, node)?;
            // For each node, try to resolve it as a type.
            self.try_or_add_error(self.make_ty_from_ast_ty(node));
            Ok(())
        })
    }

    type ExprRet = ();
    fn visit_expr(&self, node: ast::AstNodeRef<ast::Expr>) -> Result<Self::ExprRet, Self::Error> {
        if let ContextKind::Access(_, _) = self.scoping().get_current_context_kind() {
            // Handled by path resolution.
            return Ok(());
        }

        self.in_expr.enter(InExpr::Value, || {
            walk::walk_expr(self, node)?;
            // For each node, try to resolve it as a term.
            self.try_or_add_error(self.make_term_from_ast_expr(node));
            Ok(())
        })
    }

    type PatRet = ();
    fn visit_pat(&self, node: AstNodeRef<ast::Pat>) -> Result<Self::PatRet, Self::Error> {
        if let ContextKind::Access(_, _) = self.scoping().get_current_context_kind() {
            // Handled by path resolution.
            return Ok(());
        }

        if let ScopeKind::Stack(_) = self.context().get_current_scope_kind() {
            // Only look at patterns if we are in a stack.
            self.in_expr.enter(InExpr::Pat, || {
                walk::walk_pat(self, node)?;
                // For each node, try to resolve it as a pattern.
                self.try_or_add_error(self.make_pat_from_ast_pat(node));
                Ok(())
            })
        } else {
            Ok(())
        }
    }

    // These are all handled by path resolution:

    type AccessPatRet = ();
    fn visit_access_pat(
        &self,
        _node: AstNodeRef<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        Ok(())
    }

    type AccessTyRet = ();
    fn visit_access_ty(
        &self,
        _node: AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        Ok(())
    }

    type AccessExprRet = ();
    fn visit_access_expr(
        &self,
        _node: AstNodeRef<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        Ok(())
    }

    type BindingPatRet = ();
    fn visit_binding_pat(
        &self,
        _node: AstNodeRef<ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        Ok(())
    }

    type VariableExprRet = ();
    fn visit_variable_expr(
        &self,
        _node: AstNodeRef<ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        Ok(())
    }

    type NamedTyRet = ();
    fn visit_named_ty(
        &self,
        _node: AstNodeRef<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        Ok(())
    }
}
