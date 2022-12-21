//! Visitor pattern for the semantic analysis stage. This file implements
//! the [AstVisitor] pattern on the AST for [SemanticAnalyser]. During
//! traversal, the visitor calls various functions that are defined on the
//! analyser to perform a variety of semantic checks.

use std::{collections::HashSet, convert::Infallible, mem};

use hash_ast::{
    ast::{
        walk_mut_self, AstVisitorMutSelf, BindingPat, Block, BlockExpr, DirectiveExpr, Expr,
        LitExpr, Mutability, ParamOrigin,
    },
    ast_visitor_mut_self_default_impl,
    origin::BlockOrigin,
};
use hash_reporting::macros::panic_on_span;
use hash_source::{identifier::IDENTS, ModuleKind};

use crate::{
    analysis::SemanticAnalyser,
    diagnostics::{
        directives::DirectiveArgument, error::AnalysisErrorKind, warning::AnalysisWarningKind,
    },
};

impl AstVisitorMutSelf for SemanticAnalyser<'_> {
    type Error = Infallible;

    ast_visitor_mut_self_default_impl!(
        hiding: FloatLit,
        DirectiveExpr,
        FnDef,
        Param,
        LoopBlock,
        ForLoopBlock,
        WhileLoopBlock,
        ModDef,
        ImplDef,
        IfClause,
        IfBlock,
        BodyBlock,
        ReturnStatement,
        BreakStatement,
        ContinueStatement,
        MergeDeclaration,
        EnumDefEntry,
        TraitDef,
        TraitImpl,
        LitPat,
        BindingPat,
        Module,
        StructDef
    );

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

    type DirectiveExprRet = ();

    fn visit_directive_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let DirectiveExpr { name, .. } = node.body();
        let _ = walk_mut_self::walk_directive_expr(self, node);

        let module_kind = self.source_map.module_kind_by_id(self.source_id);

        // Here we should check if in the event that an `intrinsics` directive
        // is being used only within the `prelude` module.
        if name.is(IDENTS.intrinsics) {
            if !matches!(module_kind, Some(ModuleKind::Prelude)) {
                self.append_error(
                    AnalysisErrorKind::DisallowedDirective { name: name.ident, module_kind },
                    name.ast_ref(),
                );

                // exit early as we don't care about if the arguments of the directive are
                // invalid in an invalid module context.
                return Ok(());
            }

            // @@Cleanup @@Hardcoded: we check here that this particular directive
            // expression must be a `mod` block since otherwise the directive
            // wouldn't make sense...
            if !matches!(node.subject.body(), Expr::ModDef(..)) {
                self.append_error(
                    AnalysisErrorKind::InvalidDirectiveArgument {
                        name: name.ident,
                        expected: DirectiveArgument::ModDef,
                        received: node.subject.body().into(),
                    },
                    node.subject.ast_ref(),
                );
            }
        } else if name.is(IDENTS.dump_ir) {
            let is_in_constant_block = self.is_in_constant_block();

            let maybe_emit_invalid_scope_err = |this: &mut Self| {
                if !is_in_constant_block {
                    this.append_error(
                        AnalysisErrorKind::InvalidDirectiveScope {
                            name: name.ident,
                            expected: BlockOrigin::Const,
                            received: this.current_block,
                        },
                        node.subject.ast_ref(),
                    );
                }
            };

            // For the `#dump_ir` directive, we are expecting that it takes either a
            // function definition and be within a constant scope
            match node.subject.body() {
                Expr::Declaration(_) => {
                    maybe_emit_invalid_scope_err(self);
                }
                Expr::Block(BlockExpr { data: block })
                    if matches!(block.body(), Block::Body(..)) =>
                {
                    maybe_emit_invalid_scope_err(self);
                }
                _ => self.append_error(
                    AnalysisErrorKind::InvalidDirectiveArgument {
                        name: name.ident,
                        // @@Improvement, specify multiple allowed argument kinds
                        expected: DirectiveArgument::Declaration,
                        received: node.subject.body().into(),
                    },
                    node.subject.ast_ref(),
                ),
            }
        } else if !name.is(IDENTS.dump_ast) {
            // @@Future: use some kind of scope validation in order to verify that
            // the used directives are valid
            self.append_warning(
                AnalysisWarningKind::UnknownDirective { name: name.ident },
                node.name.ast_ref(),
            )
        }

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

    type ModDefRet = ();

    fn visit_mod_def(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        self.check_constant_body_block(&node.body().block, BlockOrigin::Mod);
        Ok(())
    }

    type ImplDefRet = ();

    fn visit_impl_def(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImplDef>,
    ) -> Result<Self::ImplDefRet, Self::Error> {
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
                Expr::Lit(LitExpr { data }) if data.body().is_constant() => {
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

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        // @@Note: We probably don't have to walk this??
        let _ = walk_mut_self::walk_merge_declaration(self, node);
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
