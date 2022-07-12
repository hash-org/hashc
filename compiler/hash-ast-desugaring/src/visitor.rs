use std::convert::Infallible;

use hash_ast::{
    ast::Block,
    visitor::{walk_mut, AstVisitorMut},
};
use hash_source::{
    location::{SourceLocation, Span},
    SourceId, SourceMap,
};

#[derive(Debug)]
pub struct AstDesugaring<'s> {
    pub(crate) source_map: &'s SourceMap,
    source_id: SourceId,
}

impl<'s> AstDesugaring<'s> {
    /// Create a new [AstDesugaring]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new(source_map: &'s SourceMap, source_id: SourceId) -> Self {
        Self { source_map, source_id }
    }

    /// Create a [SourceLocation] from a [Span]
    pub(crate) fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, source_id: self.source_id }
    }
}

impl<'s> AstVisitorMut for AstDesugaring<'s> {
    type Ctx = ();

    type CollectionContainer<T> = Vec<T>;

    fn try_collect_items<T, E, I: Iterator<Item = Result<T, E>>>(
        _: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E> {
        items.collect()
    }

    type Error = Infallible;

    type NameRet = ();

    fn visit_name(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        Ok(())
    }

    type AccessNameRet = ();

    fn visit_access_name(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AccessName>,
    ) -> Result<Self::AccessNameRet, Self::Error> {
        Ok(())
    }

    type LiteralRet = ();

    fn visit_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Literal>,
    ) -> Result<Self::LiteralRet, Self::Error> {
        Ok(())
    }

    type MapLiteralRet = ();

    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapLiteral>,
    ) -> Result<Self::MapLiteralRet, Self::Error> {
        let _ = walk_mut::walk_map_literal(self, ctx, node);
        Ok(())
    }

    type MapLiteralEntryRet = ();

    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapLiteralEntry>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error> {
        let _ = walk_mut::walk_map_literal_entry(self, ctx, node);
        Ok(())
    }

    type ListLiteralRet = ();

    fn visit_list_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListLiteral>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        let _ = walk_mut::walk_list_literal(self, ctx, node);
        Ok(())
    }

    type SetLiteralRet = ();

    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SetLiteral>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        let _ = walk_mut::walk_set_literal(self, ctx, node);
        Ok(())
    }

    type TupleLiteralEntryRet = ();

    fn visit_tuple_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleLiteralEntry>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error> {
        let _ = walk_mut::walk_tuple_literal_entry(self, ctx, node);
        Ok(())
    }

    type TupleLiteralRet = ();

    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleLiteral>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        let _ = walk_mut::walk_tuple_literal(self, ctx, node);
        Ok(())
    }

    type StrLiteralRet = ();

    fn visit_str_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        Ok(())
    }

    type CharLiteralRet = ();

    fn visit_char_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error> {
        Ok(())
    }

    type FloatLiteralRet = ();

    fn visit_float_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        Ok(())
    }

    type BoolLiteralRet = ();

    fn visit_bool_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error> {
        Ok(())
    }

    type IntLiteralRet = ();

    fn visit_int_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        Ok(())
    }

    type BinaryOperatorRet = ();

    fn visit_binary_operator(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinaryOperatorRet, Self::Error> {
        Ok(())
    }

    type UnaryOperatorRet = ();

    fn visit_unary_operator(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnaryOperatorRet, Self::Error> {
        Ok(())
    }

    type ExpressionRet = ();

    fn visit_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Expression>,
    ) -> Result<Self::ExpressionRet, Self::Error> {
        let _ = walk_mut::walk_expression(self, ctx, node);
        Ok(())
    }

    type ImportRet = ();

    fn visit_import(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        Ok(())
    }

    type VariableExprRet = ();

    fn visit_variable_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        Ok(())
    }

    type DirectiveExprRet = ();

    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let _ = walk_mut::walk_directive_expr(self, ctx, node);
        Ok(())
    }

    type ConstructorCallArgRet = ();

    fn visit_constructor_call_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
        let _ = walk_mut::walk_constructor_call_arg(self, ctx, node);
        Ok(())
    }

    type ConstructorCallArgsRet = ();

    fn visit_constructor_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorCallArgs>,
    ) -> Result<Self::ConstructorCallArgsRet, Self::Error> {
        let _ = walk_mut::walk_constructor_call_args(self, ctx, node);
        Ok(())
    }

    type ConstructorCallExprRet = ();

    fn visit_constructor_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        let _ = walk_mut::walk_constructor_call_expr(self, ctx, node);
        Ok(())
    }

    type MethodCallExprRet = ();

    fn visit_method_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MethodCallExpr>,
    ) -> Result<Self::MethodCallExprRet, Self::Error> {
        let _ = walk_mut::walk_method_call_expr(self, ctx, node);

        Ok(())
    }

    type PropertyAccessExprRet = ();

    fn visit_property_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::PropertyAccessExpr>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        let _ = walk_mut::walk_property_access_expr(self, ctx, node);
        Ok(())
    }

    type RefExprRet = ();

    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let _ = walk_mut::walk_ref_expr(self, ctx, node);
        Ok(())
    }

    type DerefExprRet = ();

    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let _ = walk_mut::walk_deref_expr(self, ctx, node);
        Ok(())
    }

    type UnsafeExprRet = ();

    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        let _ = walk_mut::walk_unsafe_expr(self, ctx, node);
        Ok(())
    }

    type LiteralExprRet = ();

    fn visit_literal_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LiteralExpr>,
    ) -> Result<Self::LiteralExprRet, Self::Error> {
        Ok(())
    }

    type CastExprRet = ();

    fn visit_cast_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let _ = walk_mut::walk_cast_expr(self, ctx, node);
        Ok(())
    }

    type TyExprRet = ();

    fn visit_ty_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error> {
        Ok(())
    }

    type BlockExprRet = ();

    #[inline]
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        let _ = walk_mut::walk_block_expr(self, ctx, node)?;

        Ok(())
    }

    type ImportExprRet = ();

    fn visit_import_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(())
    }

    type TyRet = ();

    fn visit_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Ty>,
    ) -> Result<Self::TyRet, Self::Error> {
        Ok(())
    }

    type TupleTyRet = ();

    fn visit_tuple_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        Ok(())
    }

    type ListTyRet = ();

    fn visit_list_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListTy>,
    ) -> Result<Self::ListTyRet, Self::Error> {
        Ok(())
    }

    type SetTyRet = ();

    fn visit_set_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SetTy>,
    ) -> Result<Self::SetTyRet, Self::Error> {
        Ok(())
    }

    type MapTyRet = ();

    fn visit_map_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapTy>,
    ) -> Result<Self::MapTyRet, Self::Error> {
        Ok(())
    }

    type NamedFieldTyRet = ();

    fn visit_named_field_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::NamedFieldTyEntry>,
    ) -> Result<Self::NamedFieldTyRet, Self::Error> {
        Ok(())
    }

    type FnTyRet = ();

    fn visit_fn_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FnTy>,
    ) -> Result<Self::FnTyRet, Self::Error> {
        Ok(())
    }

    type TyFnParamRet = ();

    fn visit_ty_fn_param(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TyFnParam>,
    ) -> Result<Self::TyFnParamRet, Self::Error> {
        Ok(())
    }

    type TyFnRet = ();

    fn visit_ty_fn_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TyFn>,
    ) -> Result<Self::TyFnRet, Self::Error> {
        Ok(())
    }

    type TyFnCallRet = ();

    fn visit_ty_fn_call(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error> {
        Ok(())
    }

    type NamedTyRet = ();

    fn visit_named_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        Ok(())
    }

    type RefTyRet = ();

    fn visit_ref_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error> {
        Ok(())
    }

    type MergeTyRet = ();

    fn visit_merge_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error> {
        Ok(())
    }

    type UnionTyRet = ();

    fn visit_union_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error> {
        Ok(())
    }

    type TyFnDefRet = ();

    fn visit_ty_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let _ = walk_mut::walk_ty_fn_def(self, ctx, node);
        Ok(())
    }

    type TyFnDefArgRet = ();

    fn visit_ty_fn_def_param(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TyFnDefParam>,
    ) -> Result<Self::TyFnDefArgRet, Self::Error> {
        Ok(())
    }

    type FnDefRet = ();

    fn visit_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let _ = walk_mut::walk_fn_def(self, ctx, node);
        Ok(())
    }

    type FnDefParamRet = ();

    fn visit_fn_def_param(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FnDefParam>,
    ) -> Result<Self::FnDefParamRet, Self::Error> {
        let _ = walk_mut::walk_fn_def_param(self, ctx, node);
        Ok(())
    }

    type BlockRet = ();

    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        mut node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        let parent_span = node.span();

        // Check if this is a for, while, or if block and then apply the appropriate
        // transformations.
        match node.body() {
            Block::For(_) => {
                node.replace(|old| self.desugar_for_loop_block(old, parent_span));
            }
            Block::While(_) => {
                node.replace(|old| self.desugar_while_loop_block(old, parent_span));
            }
            Block::If(_) => {
                node.replace(|old| self.desugar_if_block(old, parent_span));
            }
            _ => {}
        };

        // We still need to walk the block now
        let _ = walk_mut::walk_block(self, ctx, node);

        Ok(())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let _ = walk_mut::walk_match_case(self, ctx, node);
        Ok(())
    }

    type MatchBlockRet = ();

    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let _ = walk_mut::walk_match_block(self, ctx, node);
        Ok(())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let _ = walk_mut::walk_loop_block(self, ctx, node);

        Ok(())
    }

    type ForLoopBlockRet = ();

    fn visit_for_loop_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type WhileLoopBlockRet = ();

    fn visit_while_loop_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type ModBlockRet = ();

    fn visit_mod_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        let _ = walk_mut::walk_mod_block(self, ctx, node);
        Ok(())
    }

    type ImplBlockRet = ();

    fn visit_impl_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        let _ = walk_mut::walk_impl_block(self, ctx, node);
        Ok(())
    }

    type IfClauseRet = ();

    fn visit_if_clause(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type IfBlockRet = ();

    fn visit_if_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let _ = walk_mut::walk_body_block(self, ctx, node);
        Ok(())
    }

    type ReturnStatementRet = ();

    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let _ = walk_mut::walk_return_statement(self, ctx, node);
        Ok(())
    }

    type BreakStatementRet = ();

    fn visit_break_statement(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        Ok(())
    }

    type ContinueStatementRet = ();

    fn visit_continue_statement(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        Ok(())
    }

    type VisibilityRet = ();

    fn visit_visibility_modifier(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        Ok(())
    }

    type MutabilityRet = ();

    fn visit_mutability_modifier(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error> {
        Ok(())
    }

    type DeclarationRet = ();

    fn visit_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let _ = walk_mut::walk_declaration(self, ctx, node);
        Ok(())
    }

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        // @@Note: We probably don't have to walk this??
        let _ = walk_mut::walk_merge_declaration(self, ctx, node);
        Ok(())
    }

    type MergeExprRet = ();

    fn visit_merge_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MergeExpr>,
    ) -> Result<Self::MergeExprRet, Self::Error> {
        let _ = walk_mut::walk_merge_expr(self, ctx, node);
        Ok(())
    }

    type AssignExpressionRet = ();

    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AssignExpression>,
    ) -> Result<Self::AssignExpressionRet, Self::Error> {
        let _ = walk_mut::walk_assign_statement(self, ctx, node);
        Ok(())
    }

    type AssignOpExpressionRet = ();

    fn visit_assign_op_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AssignOpExpression>,
    ) -> Result<Self::AssignOpExpressionRet, Self::Error> {
        let _ = walk_mut::walk_assign_op_statement(self, ctx, node);
        Ok(())
    }

    type BinaryExpressionRet = ();

    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BinaryExpression>,
    ) -> Result<Self::BinaryExpressionRet, Self::Error> {
        let _ = walk_mut::walk_binary_expr(self, ctx, node);
        Ok(())
    }

    type UnaryExpressionRet = ();

    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnaryExpression>,
    ) -> Result<Self::UnaryExpressionRet, Self::Error> {
        let _ = walk_mut::walk_unary_expr(self, ctx, node);
        Ok(())
    }

    type IndexExpressionRet = ();

    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IndexExpression>,
    ) -> Result<Self::IndexExpressionRet, Self::Error> {
        let _ = walk_mut::walk_index_expr(self, ctx, node);
        Ok(())
    }

    type StructDefEntryRet = ();

    fn visit_struct_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StructDefEntry>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        let _ = walk_mut::walk_struct_def_entry(self, ctx, node);
        Ok(())
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let _ = walk_mut::walk_struct_def(self, ctx, node);
        Ok(())
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        Ok(())
    }

    type EnumDefRet = ();

    fn visit_enum_def(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        Ok(())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let _ = walk_mut::walk_trait_def(self, ctx, node);
        Ok(())
    }

    type TraitImplRet = ();

    fn visit_trait_impl(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let _ = walk_mut::walk_trait_impl(self, ctx, node);
        Ok(())
    }

    type PatternRet = ();

    fn visit_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Pattern>,
    ) -> Result<Self::PatternRet, Self::Error> {
        Ok(())
    }

    type ConstructorPatternRet = ();

    fn visit_constructor_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorPattern>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error> {
        Ok(())
    }

    type NamespacePatternRet = ();

    fn visit_namespace_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::NamespacePattern>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        Ok(())
    }

    type TuplePatternEntryRet = ();

    fn visit_tuple_pattern_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TuplePatternEntry>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error> {
        Ok(())
    }

    type TuplePatternRet = ();

    fn visit_tuple_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TuplePattern>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        Ok(())
    }

    type ListPatternRet = ();

    fn visit_list_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListPattern>,
    ) -> Result<Self::ListPatternRet, Self::Error> {
        Ok(())
    }

    type StrLiteralPatternRet = ();

    fn visit_str_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type CharLiteralPatternRet = ();

    fn visit_char_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type IntLiteralPatternRet = ();

    fn visit_int_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type FloatLiteralPatternRet = ();

    fn visit_float_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type BoolLiteralPatternRet = ();

    fn visit_bool_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type LiteralPatternRet = ();

    fn visit_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error> {
        Ok(())
    }

    type OrPatternRet = ();

    fn visit_or_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::OrPattern>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        Ok(())
    }

    type IfPatternRet = ();

    fn visit_if_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfPattern>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        let _ = walk_mut::walk_if_pattern(self, ctx, node);
        Ok(())
    }

    type BindingPatternRet = ();

    fn visit_binding_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BindingPattern>,
    ) -> Result<Self::BindingPatternRet, Self::Error> {
        Ok(())
    }

    type SpreadPatternRet = ();

    fn visit_spread_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SpreadPattern>,
    ) -> Result<Self::SpreadPatternRet, Self::Error> {
        Ok(())
    }

    type IgnorePatternRet = ();

    fn visit_ignore_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        Ok(())
    }

    type DestructuringPatternRet = ();

    fn visit_destructuring_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::DestructuringPattern>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error> {
        Ok(())
    }

    type ModuleRet = ();

    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let _ = walk_mut::walk_module(self, ctx, node);
        Ok(())
    }
}
