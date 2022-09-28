//! Visitor pattern for thedataanalysis stage. This file implements
//! the [AstVisitor] pattern on the AST for [SemanticAnalyser]. During
//! traversal, the visitor calls various functions that are defined on the
//! analyser to perform a variety of semantic checks.

use std::{collections::HashSet, convert::Infallible, mem};

use ::if_chain::if_chain;
use hash_ast::ast::{
    walk_mut_self, AstVisitorMutSelf, BindingPat, Block, BlockExpr, Expr, LitExpr, ModulePatEntry,
    Mutability, ParamOrigin, Pat, TuplePatEntry,
};
use hash_reporting::macros::panic_on_span;
use hash_source::{identifier::IDENTS, ModuleKind};

use crate::{
    analysis::SemanticAnalyser,
    diagnostics::{
        directives::DirectiveArgument,
        error::AnalysisErrorKind,
        origins::{BlockOrigin, PatOrigin},
        warning::AnalysisWarningKind,
    },
};

impl AstVisitorMutSelf for SemanticAnalyser<'_> {
    type Error = Infallible;

    type NameRet = ();

    fn visit_name(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        Ok(())
    }

    type LitRet = ();

    fn visit_lit(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Lit>,
    ) -> Result<Self::LitRet, Self::Error> {
        let _ = walk_mut_self::walk_lit_same_children(self, node);
        Ok(())
    }

    type MapLitRet = ();

    fn visit_map_lit(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLit>,
    ) -> Result<Self::MapLitRet, Self::Error> {
        let _ = walk_mut_self::walk_map_lit(self, node);
        Ok(())
    }

    type MapLitEntryRet = ();

    fn visit_map_lit_entry(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLitEntry>,
    ) -> Result<Self::MapLitEntryRet, Self::Error> {
        let _ = walk_mut_self::walk_map_lit_entry(self, node);
        Ok(())
    }

    type ListLitRet = ();

    fn visit_list_lit(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListLit>,
    ) -> Result<Self::ListLitRet, Self::Error> {
        let _ = walk_mut_self::walk_list_lit(self, node);
        Ok(())
    }

    type SetLitRet = ();

    fn visit_set_lit(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetLit>,
    ) -> Result<Self::SetLitRet, Self::Error> {
        let _ = walk_mut_self::walk_set_lit(self, node);
        Ok(())
    }

    type TupleLitEntryRet = ();

    fn visit_tuple_lit_entry(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitEntryRet, Self::Error> {
        let _ = walk_mut_self::walk_tuple_lit_entry(self, node);
        Ok(())
    }

    type TupleLitRet = ();

    fn visit_tuple_lit(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        let _ = walk_mut_self::walk_tuple_lit(self, node);
        Ok(())
    }

    type StrLitRet = ();

    fn visit_str_lit(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error> {
        Ok(())
    }

    type CharLitRet = ();

    fn visit_char_lit(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error> {
        Ok(())
    }

    type FloatLitRet = ();

    fn visit_float_lit(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        // We disallow float literals within patterns
        if self.is_in_lit_pat {
            self.append_error(AnalysisErrorKind::DisallowedFloatPat, node);
        }

        Ok(())
    }

    type BoolLitRet = ();

    fn visit_bool_lit(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error> {
        Ok(())
    }

    type IntLitRet = ();

    fn visit_int_lit(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error> {
        Ok(())
    }

    type BinOpRet = ();

    fn visit_bin_op(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinOpRet, Self::Error> {
        Ok(())
    }

    type UnOpRet = ();

    fn visit_un_op(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnOpRet, Self::Error> {
        Ok(())
    }

    type ExprRet = ();

    fn visit_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Expr>,
    ) -> Result<Self::ExprRet, Self::Error> {
        walk_mut_self::walk_expr_same_children(self, node)
    }

    type VariableExprRet = ();

    fn visit_variable_expr(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        Ok(())
    }

    type DirectiveExprRet = ();

    fn visit_directive_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let _ = walk_mut_self::walk_directive_expr(self, node);

        let module_kind = self.source_map.module_kind_by_id(self.source_id);

        // Here we should check if in the event that an `intrinsics` directive
        // is being used only within the `prelude` module.
        if node.name.is(IDENTS.intrinsics) {
            if !matches!(module_kind, Some(ModuleKind::Prelude)) {
                self.append_error(
                    AnalysisErrorKind::DisallowedDirective { name: node.name.ident, module_kind },
                    node.name.ast_ref(),
                );

                // exit early as we don't care about if the arguments of the directive are
                // invalid in an invalid module context.
                return Ok(());
            }

            // @@Cleanup @@Hardcoded: we check here that this particular directive
            // expression must be a `mod` block since otherwise the directive
            // wouldn't make sense...
            if_chain! {
                if let Expr::Block(BlockExpr { data }) = node.subject.body();
                if matches!(data.body(), Block::Mod(_));
                then {}
                else {
                    self.append_error(
                        AnalysisErrorKind::InvalidDirectiveArgument {
                            name: node.name.ident,
                            expected: DirectiveArgument::ModBlock,
                            given: node.subject.body().into()
                        },
                        node.subject.ast_ref(),
                    );
                }
            }
        }

        Ok(())
    }

    type ConstructorCallArgRet = ();

    fn visit_constructor_call_arg(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
        let _ = walk_mut_self::walk_constructor_call_arg(self, node);
        Ok(())
    }

    type ConstructorCallExprRet = ();

    fn visit_constructor_call_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        let _ = walk_mut_self::walk_constructor_call_expr(self, node);
        Ok(())
    }

    type PropertyKindRet = ();

    fn visit_property_kind(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::PropertyKind>,
    ) -> Result<Self::PropertyKindRet, Self::Error> {
        Ok(())
    }

    type AccessExprRet = ();

    fn visit_access_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let _ = walk_mut_self::walk_access_expr(self, node);
        Ok(())
    }

    type AccessKindRet = ();

    fn visit_access_kind(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessKind>,
    ) -> Result<Self::AccessKindRet, Self::Error> {
        Ok(())
    }

    type RefExprRet = ();

    fn visit_ref_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let _ = walk_mut_self::walk_ref_expr(self, node);
        Ok(())
    }

    type DerefExprRet = ();

    fn visit_deref_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let _ = walk_mut_self::walk_deref_expr(self, node);
        Ok(())
    }

    type UnsafeExprRet = ();

    fn visit_unsafe_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        let _ = walk_mut_self::walk_unsafe_expr(self, node);
        Ok(())
    }

    type LitExprRet = ();

    fn visit_lit_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LitExpr>,
    ) -> Result<Self::LitExprRet, Self::Error> {
        let _ = walk_mut_self::walk_lit_expr(self, node);
        Ok(())
    }

    type CastExprRet = ();

    fn visit_cast_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let _ = walk_mut_self::walk_cast_expr(self, node);
        Ok(())
    }

    type TyExprRet = ();

    fn visit_ty_expr(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error> {
        Ok(())
    }

    type BlockExprRet = ();

    #[inline]
    fn visit_block_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        let _ = walk_mut_self::walk_block_expr(self, node)?;

        Ok(())
    }

    type ImportRet = ();

    fn visit_import(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        Ok(())
    }

    type ImportExprRet = ();

    fn visit_import_expr(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(())
    }

    type TyRet = ();

    fn visit_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Ty>,
    ) -> Result<Self::TyRet, Self::Error> {
        Ok(())
    }

    type TupleTyRet = ();

    fn visit_tuple_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        Ok(())
    }

    type ListTyRet = ();

    fn visit_list_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ListTy>,
    ) -> Result<Self::ListTyRet, Self::Error> {
        Ok(())
    }

    type SetTyRet = ();

    fn visit_set_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::SetTy>,
    ) -> Result<Self::SetTyRet, Self::Error> {
        Ok(())
    }

    type MapTyRet = ();

    fn visit_map_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::MapTy>,
    ) -> Result<Self::MapTyRet, Self::Error> {
        Ok(())
    }

    type TyArgRet = ();

    fn visit_ty_arg(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        Ok(())
    }

    type FnTyRet = ();

    fn visit_fn_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::FnTy>,
    ) -> Result<Self::FnTyRet, Self::Error> {
        Ok(())
    }

    type TyFnRet = ();

    fn visit_ty_fn(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFn>,
    ) -> Result<Self::TyFnRet, Self::Error> {
        Ok(())
    }

    type TyFnCallRet = ();

    fn visit_ty_fn_call(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error> {
        Ok(())
    }

    type NamedTyRet = ();

    fn visit_named_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        Ok(())
    }

    type AccessTyRet = ();

    fn visit_access_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        Ok(())
    }

    type RefTyRet = ();

    fn visit_ref_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error> {
        Ok(())
    }

    type MergeTyRet = ();

    fn visit_merge_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error> {
        Ok(())
    }

    type UnionTyRet = ();

    fn visit_union_ty(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error> {
        Ok(())
    }

    type TyFnDefRet = ();

    fn visit_ty_fn_def(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let _ = walk_mut_self::walk_ty_fn_def(self, node);
        Ok(())
    }

    type FnDefRet = ();

    fn visit_fn_def(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        // Swap the values with a new `true` and save the old state.
        let last_in_fn = mem::replace(&mut self.is_in_fn, true);
        let _ = walk_mut_self::walk_fn_def(self, node);
        self.is_in_fn = last_in_fn;

        Ok(())
    }

    type ParamRet = ();

    fn visit_param(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        let _ = walk_mut_self::walk_param(self, node);

        if matches!(node.origin, ParamOrigin::Fn) {
            match self.current_block {
                // Check that `self` cannot be within a free standing functions
                BlockOrigin::Root => {
                    if let Some(name) = node.name.as_ref() && name.is(IDENTS.self_i) {
                        self.append_error(AnalysisErrorKind::SelfInFreeStandingFn, node);
                    }
                }
                BlockOrigin::Impl | BlockOrigin::Trait | BlockOrigin::Mod  => {
                    // If both the type definition is missing and the default expression assignment
                    // to the struct-def field, then a type cannot be inferred and is thus
                    // ambiguous.
                    if let Some(name) = node.name.as_ref() && !name.is(IDENTS.self_i)
                        && node.ty.is_none()
                        && node.default.is_none()
                    {
                        self.append_error(
                            AnalysisErrorKind::InsufficientTypeAnnotations { origin: node.origin },
                            node,
                        );
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }

    type BlockRet = ();

    fn visit_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        let _ = walk_mut_self::walk_block(self, node);

        Ok(())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let _ = walk_mut_self::walk_match_case(self, node);
        Ok(())
    }

    type MatchBlockRet = ();

    fn visit_match_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let _ = walk_mut_self::walk_match_block(self, node);
        Ok(())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        // Swap the values with a new `true` and save the old state.
        let last_in_loop = mem::replace(&mut self.is_in_loop, true);

        let _ = walk_mut_self::walk_loop_block(self, node);

        // Reset the value to the old value
        self.is_in_loop = last_in_loop;

        Ok(())
    }

    type ForLoopBlockRet = ();

    fn visit_for_loop_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        panic_on_span!(
            self.source_location(node.span()),
            self.source_map,
            "hit non de-sugared for-block whilst performing semantic analysis"
        );
    }

    type WhileLoopBlockRet = ();

    fn visit_while_loop_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        panic_on_span!(
            self.source_location(node.span()),
            self.source_map,
            "hit non de-sugared while-block whilst performing semantic analysis"
        );
    }

    type ModBlockRet = ();

    fn visit_mod_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        self.check_constant_body_block(&node.body().block, BlockOrigin::Mod);
        Ok(())
    }

    type ImplBlockRet = ();

    fn visit_impl_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        self.check_constant_body_block(&node.body().block, BlockOrigin::Impl);
        Ok(())
    }

    type IfClauseRet = ();

    fn visit_if_clause(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        panic_on_span!(
            self.source_location(node.span()),
            self.source_map,
            "hit non de-sugared if-clause whilst performing semantic analysis"
        );
    }

    type IfBlockRet = ();

    fn visit_if_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        panic_on_span!(
            self.source_location(node.span()),
            self.source_map,
            "hit non de-sugared if-block whilst performing semantic analysis"
        );
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        // Iterate over the statements in a body block to check if there are any
        // 'useless' expressions... a literal that is constant of made of other
        // constant literals
        for statement in node.statements.iter() {
            match statement.body() {
                Expr::LitExpr(LitExpr { data }) if data.body().is_constant() => {
                    self.append_warning(
                        AnalysisWarningKind::UselessExpression,
                        statement.ast_ref(),
                    );
                }
                _ => {}
            }
        }

        let old_block_origin = mem::replace(&mut self.current_block, BlockOrigin::Body);

        let _ = walk_mut_self::walk_body_block(self, node);

        self.current_block = old_block_origin;

        Ok(())
    }

    type ReturnStatementRet = ();

    fn visit_return_statement(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        if !self.is_in_fn {
            self.append_error(AnalysisErrorKind::UsingReturnOutsideOfFn, node);
        }

        let _ = walk_mut_self::walk_return_statement(self, node);
        Ok(())
    }

    type BreakStatementRet = ();

    fn visit_break_statement(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        if !self.is_in_loop {
            self.append_error(AnalysisErrorKind::UsingBreakOutsideLoop, node);
        }

        Ok(())
    }

    type ContinueStatementRet = ();

    fn visit_continue_statement(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        if !self.is_in_loop {
            self.append_error(AnalysisErrorKind::UsingContinueOutsideLoop, node);
        }

        Ok(())
    }

    type VisibilityRet = ();

    fn visit_visibility(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        Ok(())
    }

    type MutabilityRet = ();

    fn visit_mutability(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error> {
        Ok(())
    }

    type RefKindRet = ();

    fn visit_ref_kind(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::RefKind>,
    ) -> Result<Self::RefKindRet, Self::Error> {
        Ok(())
    }

    type DeclarationRet = ();

    fn visit_declaration(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let _ = walk_mut_self::walk_declaration(self, node);
        Ok(())
    }

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        // @@Note: We probably don't have to walk this??
        let _ = walk_mut_self::walk_merge_declaration(self, node);
        Ok(())
    }

    type AssignExprRet = ();

    fn visit_assign_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error> {
        let _ = walk_mut_self::walk_assign_expr(self, node);
        Ok(())
    }

    type AssignOpExprRet = ();

    fn visit_assign_op_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error> {
        let _ = walk_mut_self::walk_assign_op_expr(self, node);
        Ok(())
    }

    type BinaryExprRet = ();

    fn visit_binary_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error> {
        let _ = walk_mut_self::walk_binary_expr(self, node);
        Ok(())
    }

    type UnaryExprRet = ();

    fn visit_unary_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error> {
        let _ = walk_mut_self::walk_unary_expr(self, node);
        Ok(())
    }

    type IndexExprRet = ();

    fn visit_index_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error> {
        let _ = walk_mut_self::walk_index_expr(self, node);
        Ok(())
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let _ = walk_mut_self::walk_struct_def(self, node);

        // Verify that all of the specified fields are either named, or all un-named!
        self.check_field_naming(node.fields.ast_ref_iter());

        Ok(())
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        // Verify that all of the specified fields are either named, or all un-named!
        self.check_field_naming(node.fields.ast_ref_iter());

        Ok(())
    }

    type EnumDefRet = ();

    fn visit_enum_def(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        Ok(())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let old_block_origin = mem::replace(&mut self.current_block, BlockOrigin::Trait);
        let _ = walk_mut_self::walk_trait_def(self, node);
        self.current_block = old_block_origin;

        Ok(())
    }

    type TraitImplRet = ();

    fn visit_trait_impl(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        self.check_members_are_declarative(node.trait_body.ast_ref_iter(), BlockOrigin::Impl);

        // Verify that the declarations in this implementation block adhere to the
        // rules of constant blocks....
        let old_block_origin = mem::replace(&mut self.current_block, BlockOrigin::Impl);
        let _ = walk_mut_self::walk_trait_impl(self, node);
        self.current_block = old_block_origin;

        Ok(())
    }

    type PatRet = ();

    fn visit_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Pat>,
    ) -> Result<Self::PatRet, Self::Error> {
        let _ = walk_mut_self::walk_pat(self, node);

        Ok(())
    }

    type AccessPatRet = ();

    fn visit_access_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        let _ = walk_mut_self::walk_access_pat(self, node);
        Ok(())
    }

    type ConstructorPatRet = ();

    /// This function verifies that constructor patterns adhere to the following
    /// rules:
    ///
    /// - All named fields must after before any nameless fields.
    ///
    /// - Only one spread pattern is ever present within a compound pattern.
    fn visit_constructor_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        self.check_compound_pat_rules(&node.body().fields, PatOrigin::Constructor);

        let _ = walk_mut_self::walk_constructor_pat(self, node);
        Ok(())
    }

    type TuplePatEntryRet = ();

    fn visit_tuple_pat_entry(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePatEntry>,
    ) -> Result<Self::TuplePatEntryRet, Self::Error> {
        let TuplePatEntry { name, pat } = node.body();

        // Spread patterns are always disallowed within a named field entry
        if name.is_some() && matches!(pat.body(), Pat::Spread(_)) {
            self.append_error(
                AnalysisErrorKind::IllegalSpreadPatUse { origin: PatOrigin::NamedField },
                pat.ast_ref(),
            );
        } else {
            // We only need to walk the children if it hasn't error'd yet
            let _ = walk_mut_self::walk_tuple_pat_entry(self, node);
        }

        Ok(())
    }

    type TuplePatRet = ();

    /// This function verifies that tuple patterns adhere to the following
    /// rules:
    ///
    /// - All named fields must after before any nameless fields.
    ///
    /// - Only one spread pattern is ever present within a compound pattern.
    fn visit_tuple_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        self.check_compound_pat_rules(&node.body().fields, PatOrigin::Tuple);

        // Continue walking the tree
        let _ = walk_mut_self::walk_tuple_pat(self, node);
        Ok(())
    }

    type ListPatRet = ();

    fn visit_list_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListPat>,
    ) -> Result<Self::ListPatRet, Self::Error> {
        self.check_list_pat(&node.body().fields);

        // Continue walking the tree
        let _ = walk_mut_self::walk_list_pat(self, node);
        Ok(())
    }

    type SpreadPatRet = ();

    fn visit_spread_pat(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error> {
        Ok(())
    }

    type LitPatRet = ();

    fn visit_lit_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LitPat>,
    ) -> Result<Self::LitPatRet, Self::Error> {
        let last_in_lit_pat = mem::replace(&mut self.is_in_lit_pat, true);

        let _ = walk_mut_self::walk_lit_pat(self, node);

        self.is_in_lit_pat = last_in_lit_pat;
        Ok(())
    }

    type RangePatRet = ();

    fn visit_range_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::RangePat>,
    ) -> Result<Self::RangePatRet, Self::Error> {
        let _ = walk_mut_self::walk_range_pat(self, node)?;

        Ok(())
    }

    type OrPatRet = ();

    fn visit_or_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error> {
        let _ = walk_mut_self::walk_or_pat(self, node);
        Ok(())
    }

    type IfPatRet = ();

    fn visit_if_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error> {
        let _ = walk_mut_self::walk_if_pat(self, node);
        Ok(())
    }

    type BindingPatRet = ();

    fn visit_binding_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        let BindingPat { mutability, visibility, .. } = node.body();

        // If the pattern is present in a declaration that is within a constant block,
        // it it not allowed to be declared to be mutable. If we are not in a
        // constant scope, then we should check if binding contains a visibility
        // modifier which is disallowed within body blocks.
        if self.is_in_constant_block() {
            if let Some(mut_annotation) = mutability {
                if *mut_annotation.body() == Mutability::Mutable {
                    self.append_error(
                        AnalysisErrorKind::IllegalBindingMutability,
                        mut_annotation.ast_ref(),
                    );
                }
            }
        } else if let Some(visibility_annotation) = visibility {
            self.append_error(
                AnalysisErrorKind::IllegalBindingVisibilityModifier {
                    modifier: *visibility_annotation.body(),
                    origin: self.current_block,
                },
                visibility_annotation.ast_ref(),
            );
        }

        Ok(())
    }

    type WildPatRet = ();

    fn visit_wild_pat(
        &mut self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error> {
        Ok(())
    }

    type ModulePatEntryRet = ();

    fn visit_module_pat_entry(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        let ModulePatEntry { pat, .. } = node.body();

        // Spread patterns are always disallowed within a named field entry
        if matches!(pat.body(), Pat::Spread(_)) {
            self.append_error(
                AnalysisErrorKind::IllegalSpreadPatUse { origin: PatOrigin::Namespace },
                pat.ast_ref(),
            );
        } else {
            // We only need to walk the children if it hasn't error'd yet
            let _ = walk_mut_self::walk_module_pat_entry(self, node);
        }

        Ok(())
    }

    type ModulePatRet = ();

    fn visit_module_pat(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error> {
        let _ = walk_mut_self::walk_module_pat(self, node);
        Ok(())
    }

    type ModuleRet = HashSet<usize>;

    fn visit_module(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let error_indices =
            self.check_members_are_declarative(node.contents.ast_ref_iter(), BlockOrigin::Root);

        Ok(error_indices)
    }
}
