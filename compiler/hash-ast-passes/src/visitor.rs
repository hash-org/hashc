//! Visitor pattern for the semantic analysis stage.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use std::convert::Infallible;

use hash_ast::visitor::{walk, AstVisitor};

#[derive(Default)]
pub struct AstPasses;

impl AstPasses {
    pub fn new() -> Self {
        Self
    }
}

impl AstVisitor for AstPasses {
    type Ctx = ();

    type CollectionContainer<T> = Vec<T>;

    fn try_collect_items<T, E, I: Iterator<Item = Result<T, E>>>(
        _: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E> {
        items.collect()
    }

    type Error = Infallible;

    type ImportRet = ();

    fn visit_import(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        Ok(())
    }

    type NameRet = ();

    fn visit_name(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        Ok(())
    }

    type AccessNameRet = ();

    fn visit_access_name(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessName>,
    ) -> Result<Self::AccessNameRet, Self::Error> {
        Ok(())
    }

    type LiteralRet = ();

    fn visit_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Literal>,
    ) -> Result<Self::LiteralRet, Self::Error> {
        Ok(())
    }

    type BinaryOperatorRet = ();

    fn visit_binary_operator(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinaryOperatorRet, Self::Error> {
        Ok(())
    }

    type UnaryOperatorRet = ();

    fn visit_unary_operator(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnaryOperatorRet, Self::Error> {
        Ok(())
    }

    type ExpressionRet = ();

    fn visit_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Expression>,
    ) -> Result<Self::ExpressionRet, Self::Error> {
        let _ = walk::walk_expression(self, ctx, node);
        Ok(())
    }

    type VariableExprRet = ();

    fn visit_variable_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        Ok(())
    }

    type DirectiveExprRet = ();

    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let _ = walk::walk_directive_expr(self, ctx, node);
        Ok(())
    }

    type FunctionCallArgRet = ();

    fn visit_function_call_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionCallArg>,
    ) -> Result<Self::FunctionCallArgRet, Self::Error> {
        let _ = walk::walk_function_call_arg(self, ctx, node);
        Ok(())
    }

    type FunctionCallArgsRet = ();

    fn visit_function_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionCallArgs>,
    ) -> Result<Self::FunctionCallArgsRet, Self::Error> {
        let _ = walk::walk_function_call_args(self, ctx, node);
        Ok(())
    }

    type FunctionCallExprRet = ();

    fn visit_function_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionCallExpr>,
    ) -> Result<Self::FunctionCallExprRet, Self::Error> {
        let _ = walk::walk_function_call_expr(self, ctx, node);
        Ok(())
    }

    type PropertyAccessExprRet = ();

    fn visit_property_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::PropertyAccessExpr>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        let _ = walk::walk_property_access_expr(self, ctx, node);
        Ok(())
    }

    type RefExprRet = ();

    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let _ = walk::walk_ref_expr(self, ctx, node);
        Ok(())
    }

    type DerefExprRet = ();

    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let _ = walk::walk_deref_expr(self, ctx, node);
        Ok(())
    }

    type UnsafeExprRet = ();

    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        let _ = walk::walk_unsafe_expr(self, ctx, node);
        Ok(())
    }

    type LiteralExprRet = ();

    fn visit_literal_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::LiteralExpr>,
    ) -> Result<Self::LiteralExprRet, Self::Error> {
        Ok(())
    }

    type CastExprRet = ();

    fn visit_cast_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let _ = walk::walk_cast_expr(self, ctx, node);
        Ok(())
    }

    type TypeExprRet = ();

    fn visit_type_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeExpr>,
    ) -> Result<Self::TypeExprRet, Self::Error> {
        Ok(())
    }

    type BlockExprRet = ();

    #[inline]
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        let _ = walk::walk_block_expr(self, ctx, node)?;

        Ok(())
    }

    type ImportExprRet = ();

    fn visit_import_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(())
    }

    type TypeRet = ();

    fn visit_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Type>,
    ) -> Result<Self::TypeRet, Self::Error> {
        Ok(())
    }

    type NamedFieldTypeRet = ();

    fn visit_named_field_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedFieldTypeEntry>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error> {
        Ok(())
    }

    type FnTypeRet = ();

    fn visit_function_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::FnType>,
    ) -> Result<Self::FnTypeRet, Self::Error> {
        Ok(())
    }

    type TypeFunctionParamRet = ();

    fn visit_type_function_param(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionParam>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error> {
        Ok(())
    }

    type TypeFunctionRet = ();

    fn visit_type_function(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunction>,
    ) -> Result<Self::TypeFunctionRet, Self::Error> {
        Ok(())
    }

    type TypeFunctionCallRet = ();

    fn visit_type_function_call(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionCall>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error> {
        Ok(())
    }

    type NamedTypeRet = ();

    fn visit_named_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedType>,
    ) -> Result<Self::NamedTypeRet, Self::Error> {
        Ok(())
    }

    type RefTypeRet = ();

    fn visit_ref_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::RefType>,
    ) -> Result<Self::RefTypeRet, Self::Error> {
        Ok(())
    }

    type MergedTypeRet = ();

    fn visit_merged_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::MergedType>,
    ) -> Result<Self::MergedTypeRet, Self::Error> {
        Ok(())
    }

    type MapLiteralRet = ();

    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLiteral>,
    ) -> Result<Self::MapLiteralRet, Self::Error> {
        let _ = walk::walk_map_literal(self, ctx, node);
        Ok(())
    }

    type MapLiteralEntryRet = ();

    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLiteralEntry>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error> {
        let _ = walk::walk_map_literal_entry(self, ctx, node);
        Ok(())
    }

    type ListLiteralRet = ();

    fn visit_list_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListLiteral>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        let _ = walk::walk_list_literal(self, ctx, node);
        Ok(())
    }

    type SetLiteralRet = ();

    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetLiteral>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        let _ = walk::walk_set_literal(self, ctx, node);
        Ok(())
    }

    type TupleLiteralEntryRet = ();

    fn visit_tuple_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLiteralEntry>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error> {
        let _ = walk::walk_tuple_literal_entry(self, ctx, node);
        Ok(())
    }

    type TupleLiteralRet = ();

    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLiteral>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        let _ = walk::walk_tuple_literal(self, ctx, node);
        Ok(())
    }

    type StrLiteralRet = ();

    fn visit_str_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        Ok(())
    }

    type CharLiteralRet = ();

    fn visit_char_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error> {
        Ok(())
    }

    type FloatLiteralRet = ();

    fn visit_float_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        Ok(())
    }

    type BoolLiteralRet = ();

    fn visit_bool_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error> {
        Ok(())
    }

    type IntLiteralRet = ();

    fn visit_int_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        Ok(())
    }

    type FunctionDefRet = ();

    fn visit_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionDef>,
    ) -> Result<Self::FunctionDefRet, Self::Error> {
        let _ = walk::walk_function_def(self, ctx, node);
        Ok(())
    }

    type FunctionDefArgRet = ();

    fn visit_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionDefArg>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error> {
        let _ = walk::walk_function_def_arg(self, ctx, node);
        Ok(())
    }

    type BlockRet = ();

    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        let _ = walk::walk_block(self, ctx, node);

        Ok(())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let _ = walk::walk_match_case(self, ctx, node);
        Ok(())
    }

    type MatchBlockRet = ();

    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let _ = walk::walk_match_block(self, ctx, node);
        Ok(())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let _ = walk::walk_loop_block(self, ctx, node);

        Ok(())
    }

    type ForLoopBlockRet = ();

    fn visit_for_loop_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type WhileLoopBlockRet = ();

    fn visit_while_loop_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type IfClauseRet = ();

    fn visit_if_clause(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type IfBlockRet = ();

    fn visit_if_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type ModBlockRet = ();

    fn visit_mod_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        let _ = walk::walk_mod_block(self, ctx, node);
        Ok(())
    }

    type ImplBlockRet = ();

    fn visit_impl_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        let _ = walk::walk_impl_block(self, ctx, node);
        Ok(())
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let _ = walk::walk_body_block(self, ctx, node);
        Ok(())
    }

    type ReturnStatementRet = ();

    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let _ = walk::walk_return_statement(self, ctx, node);
        Ok(())
    }

    type BreakStatementRet = ();

    fn visit_break_statement(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        Ok(())
    }

    type ContinueStatementRet = ();

    fn visit_continue_statement(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        Ok(())
    }

    type VisibilityRet = ();

    fn visit_visibility_modifier(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        Ok(())
    }

    type MutabilityRet = ();

    fn visit_mutability_modifier(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error> {
        Ok(())
    }

    type DeclarationRet = ();

    fn visit_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let _ = walk::walk_declaration(self, ctx, node);
        Ok(())
    }

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        // @@Note: We probably don't have to walk this??
        let _ = walk::walk_merge_declaration(self, ctx, node);
        Ok(())
    }

    type AssignExpressionRet = ();

    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignExpression>,
    ) -> Result<Self::AssignExpressionRet, Self::Error> {
        let _ = walk::walk_assign_statement(self, ctx, node);
        Ok(())
    }

    type AssignOpExpressionRet = ();

    fn visit_assign_op_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignOpExpression>,
    ) -> Result<Self::AssignOpExpressionRet, Self::Error> {
        let _ = walk::walk_assign_op_statement(self, ctx, node);
        Ok(())
    }

    type BinaryExpressionRet = ();

    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinaryExpression>,
    ) -> Result<Self::BinaryExpressionRet, Self::Error> {
        let _ = walk::walk_binary_expr(self, ctx, node);
        Ok(())
    }

    type UnaryExpressionRet = ();

    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnaryExpression>,
    ) -> Result<Self::UnaryExpressionRet, Self::Error> {
        let _ = walk::walk_unary_expr(self, ctx, node);
        Ok(())
    }

    type IndexExpressionRet = ();

    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IndexExpression>,
    ) -> Result<Self::IndexExpressionRet, Self::Error> {
        let _ = walk::walk_index_expr(self, ctx, node);
        Ok(())
    }

    type StructDefEntryRet = ();

    fn visit_struct_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDefEntry>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        let _ = walk::walk_struct_def_entry(self, ctx, node);
        Ok(())
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let _ = walk::walk_struct_def(self, ctx, node);
        Ok(())
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        Ok(())
    }

    type EnumDefRet = ();

    fn visit_enum_def(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        Ok(())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let _ = walk::walk_trait_def(self, ctx, node);
        Ok(())
    }

    type PatternRet = ();

    fn visit_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Pattern>,
    ) -> Result<Self::PatternRet, Self::Error> {
        Ok(())
    }

    type TraitImplRet = ();

    fn visit_trait_impl(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let _ = walk::walk_trait_impl(self, ctx, node);
        Ok(())
    }

    type TypeFunctionDefRet = ();

    fn visit_type_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionDef>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error> {
        let _ = walk::walk_type_function_def(self, ctx, node);
        Ok(())
    }

    type TypeFunctionDefArgRet = ();

    fn visit_type_function_def_arg(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionDefArg>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error> {
        Ok(())
    }

    type ConstructorPatternRet = ();

    fn visit_constructor_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorPattern>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error> {
        Ok(())
    }

    type NamespacePatternRet = ();

    fn visit_namespace_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::NamespacePattern>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        Ok(())
    }

    type TuplePatternEntryRet = ();

    fn visit_tuple_pattern_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePatternEntry>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error> {
        Ok(())
    }

    type TuplePatternRet = ();

    fn visit_tuple_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePattern>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        Ok(())
    }

    type ListPatternRet = ();

    fn visit_list_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ListPattern>,
    ) -> Result<Self::ListPatternRet, Self::Error> {
        Ok(())
    }

    type TupleTypeRet = ();

    fn visit_tuple_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleType>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        Ok(())
    }

    type ListTypeRet = ();

    fn visit_list_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ListType>,
    ) -> Result<Self::ListTypeRet, Self::Error> {
        Ok(())
    }

    type SetTypeRet = ();

    fn visit_set_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::SetType>,
    ) -> Result<Self::SetTypeRet, Self::Error> {
        Ok(())
    }

    type MapTypeRet = ();

    fn visit_map_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::MapType>,
    ) -> Result<Self::MapTypeRet, Self::Error> {
        Ok(())
    }

    type StrLiteralPatternRet = ();

    fn visit_str_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type CharLiteralPatternRet = ();

    fn visit_char_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type IntLiteralPatternRet = ();

    fn visit_int_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type FloatLiteralPatternRet = ();

    fn visit_float_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type BoolLiteralPatternRet = ();

    fn visit_bool_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type LiteralPatternRet = ();

    fn visit_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error> {
        Ok(())
    }

    type OrPatternRet = ();

    fn visit_or_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::OrPattern>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        Ok(())
    }

    type IfPatternRet = ();

    fn visit_if_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfPattern>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        let _ = walk::walk_if_pattern(self, ctx, node);
        Ok(())
    }

    type BindingPatternRet = ();

    fn visit_binding_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BindingPattern>,
    ) -> Result<Self::BindingPatternRet, Self::Error> {
        Ok(())
    }

    type SpreadPatternRet = ();

    fn visit_spread_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::SpreadPattern>,
    ) -> Result<Self::SpreadPatternRet, Self::Error> {
        Ok(())
    }

    type IgnorePatternRet = ();

    fn visit_ignore_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        Ok(())
    }

    type DestructuringPatternRet = ();

    fn visit_destructuring_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::DestructuringPattern>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error> {
        Ok(())
    }

    type ModuleRet = ();

    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let _ = walk::walk_module(self, ctx, node);
        Ok(())
    }
}
