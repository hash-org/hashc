//! Visitor pattern for the semantic analysis stage. This file implements
//! the [ast::AstVisitor] pattern on the AST for [SemanticAnalyser]. During
//! traversal, the visitor calls various functions that are defined on the
//! analyser to perform a variety of semantic checks.

use std::{collections::HashSet, convert::Infallible, mem};

use hash_ast::{
    ast::{self, walk_mut_self},
    ast_visitor_mut_self_default_impl,
    origin::BlockOrigin,
    visitor::AstVisitorMutSelf,
};
use hash_reporting::macros::panic_on_span;

use crate::{
    analysis::SemanticAnalyser,
    diagnostics::{error::AnalysisErrorKind, warning::AnalysisWarningKind},
};

impl AstVisitorMutSelf for SemanticAnalyser {
    type Error = Infallible;

    ast_visitor_mut_self_default_impl!(
        hiding: FloatLit,
        DirectiveExpr,
        FnDef,
        Params,
        LoopBlock,
        ForLoopBlock,
        WhileLoopBlock,
        TokenMacroInvocation,
        ModDef,
        IfClause,
        IfBlock,
        BodyBlock,
        ReturnStatement,
        BreakStatement,
        ContinueStatement,
        LitPat,
        BindingPat,
        RangePat,
        Module
    );

    type FloatLitRet = ();

    fn visit_float_lit(
        &mut self,
        node: ast::AstNodeRef<ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        // We disallow float literals within patterns
        if self.is_in_lit_pat {
            self.append_error(AnalysisErrorKind::DisallowedFloatPat, node);
        }

        Ok(())
    }

    type FnDefRet = ();

    fn visit_fn_def(
        &mut self,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        // Swap the values with a new `true` and save the old state.
        let last_in_fn = mem::replace(&mut self.is_in_fn, true);
        let _ = walk_mut_self::walk_fn_def(self, node);
        self.is_in_fn = last_in_fn;

        Ok(())
    }

    type ParamsRet = ();
    fn visit_params(
        &mut self,
        node: ast::AstNodeRef<ast::Params>,
    ) -> Result<Self::ParamsRet, Self::Error> {
        let _ = walk_mut_self::walk_params(self, node);

        // Check that the parameters are all named or all un-named.
        self.check_field_naming(node.origin, node.params.ast_ref_iter());

        // We also want to check that the parameters adhere to the rules
        // of `self` and if any parameters don't specify any type annotations
        // which could make them ambigious.
        for param in node.params.ast_ref_iter() {
            self.check_fn_param_type_annotations(node.origin, param);
        }

        Ok(())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &mut self,
        node: ast::AstNodeRef<ast::LoopBlock>,
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
        node: ast::AstNodeRef<ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        panic_on_span!(
            node.span(),
            "hit non de-sugared for-block whilst performing semantic analysis"
        );
    }

    type WhileLoopBlockRet = ();

    fn visit_while_loop_block(
        &mut self,
        node: ast::AstNodeRef<ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        panic_on_span!(
            node.span(),
            "hit non de-sugared while-block whilst performing semantic analysis"
        );
    }

    type TokenMacroInvocationRet = ();

    fn visit_token_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::TokenMacroInvocation>,
    ) -> Result<Self::TokenMacroInvocationRet, Self::Error> {
        panic_on_span!(
            node.span(),
            "hit non expanded token macro whilst performing semantic analysis"
        );
    }

    type ModDefRet = ();

    fn visit_mod_def(
        &mut self,
        node: ast::AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        self.check_constant_body_block(&node.body().block, BlockOrigin::Mod);
        Ok(())
    }

    type IfClauseRet = ();

    fn visit_if_clause(
        &mut self,
        node: ast::AstNodeRef<ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        panic_on_span!(
            node.span(),
            "hit non de-sugared if-clause whilst performing semantic analysis"
        );
    }

    type IfBlockRet = ();

    fn visit_if_block(
        &mut self,
        node: ast::AstNodeRef<ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        panic_on_span!(
            node.span(),
            "hit non de-sugared if-block whilst performing semantic analysis"
        );
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        // Iterate over the statements in a body block to check if there are any
        // 'useless' expressions... a literal that is constant of made of other
        // constant literals
        for statement in node.statements.iter() {
            match statement.body() {
                ast::Expr::Lit(ast::LitExpr { data }) if data.body().is_constant() => {
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
        node: ast::AstNodeRef<ast::ReturnStatement>,
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
        node: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        if !self.is_in_loop {
            self.append_error(AnalysisErrorKind::UsingBreakOutsideLoop, node);
        }

        Ok(())
    }

    type ContinueStatementRet = ();

    fn visit_continue_statement(
        &mut self,
        node: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        if !self.is_in_loop {
            self.append_error(AnalysisErrorKind::UsingContinueOutsideLoop, node);
        }

        Ok(())
    }

    type LitPatRet = ();

    fn visit_lit_pat(
        &mut self,
        node: ast::AstNodeRef<ast::LitPat>,
    ) -> Result<Self::LitPatRet, Self::Error> {
        let last_in_lit_pat = mem::replace(&mut self.is_in_lit_pat, true);

        let _ = walk_mut_self::walk_lit_pat(self, node);

        self.is_in_lit_pat = last_in_lit_pat;
        Ok(())
    }

    type BindingPatRet = ();

    fn visit_binding_pat(
        &mut self,
        node: ast::AstNodeRef<ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        let ast::BindingPat { mutability, visibility, .. } = node.body();

        // If the pattern is present in a declaration that is within a constant block,
        // it it not allowed to be declared to be mutable. If we are not in a
        // constant scope, then we should check if binding contains a visibility
        // modifier which is disallowed within body blocks.
        if self.is_in_constant_block() {
            if let Some(mut_annotation) = mutability {
                if *mut_annotation.body() == ast::Mutability::Mutable {
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

    type RangePatRet = ();

    fn visit_range_pat(
        &mut self,
        node: ast::AstNodeRef<ast::RangePat>,
    ) -> Result<Self::RangePatRet, Self::Error> {
        let _ = walk_mut_self::walk_range_pat(self, node);

        // Check that the range pattern is not used in a constant block.
        if node.body().end == ast::RangeEnd::Excluded && node.body().hi.is_none() {
            self.append_error(AnalysisErrorKind::ExclusiveRangeWithNoEnding, node)
        }

        Ok(())
    }

    type ModuleRet = HashSet<usize>;

    fn visit_module(
        &mut self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let error_indices =
            self.check_members_are_declarative(node.contents.ast_ref_iter(), BlockOrigin::Root);

        Ok(error_indices)
    }
}
