//! Visitor implementation for [crate::ast] nodes.

use crate::ast;
use std::convert::Infallible;

/// The main visitor trait for [crate::ast] nodes.
///
/// This contains a method for each AST structure, as well as a dedicated return
/// type for it. These can be implemented using the functions defined in [walk]
/// that can traverse the children of each node.
pub trait AstVisitor: Sized {
    /// Context type immutably passed to each visitor method for separating
    /// mutable from immutable context.
    type Ctx;

    /// What container to use to collect multiple children, used by [walk].
    type CollectionContainer<T>: Sized;

    /// Try collect an iterator of results into a container specified by
    /// [Self::CollectionContainer].
    fn try_collect_items<T, E, I: Iterator<Item = Result<T, E>>>(
        ctx: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E>;

    /// Collect an iterator of items into a container specified by
    /// [Self::CollectionContainer].
    fn collect_items<T, E, I: Iterator<Item = T>>(
        ctx: &Self::Ctx,
        items: I,
    ) -> Self::CollectionContainer<T> {
        Self::try_collect_items::<T, Infallible, _>(ctx, items.map(|item| Ok(item))).unwrap()
    }

    /// The error type to use for each visit method.
    type Error;

    type ImportRet;
    fn visit_import(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error>;

    type NameRet;
    fn visit_name(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Name>,
    ) -> Result<Self::NameRet, Self::Error>;

    type AccessNameRet;
    fn visit_access_name(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AccessName>,
    ) -> Result<Self::AccessNameRet, Self::Error>;

    type LiteralRet;
    fn visit_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Literal>,
    ) -> Result<Self::LiteralRet, Self::Error>;

    type BinaryOperatorRet;
    fn visit_binary_operator(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BinOp>,
    ) -> Result<Self::BinaryOperatorRet, Self::Error>;

    type UnaryOperatorRet;
    fn visit_unary_operator(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::UnOp>,
    ) -> Result<Self::UnaryOperatorRet, Self::Error>;

    type ExpressionRet;
    fn visit_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Expression>,
    ) -> Result<Self::ExpressionRet, Self::Error>;

    type VariableExprRet;
    fn visit_variable_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error>;

    type DirectiveExprRet;
    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error>;

    type ConstructorCallArgRet;
    fn visit_constructor_call_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error>;

    type ConstructorCallArgsRet;
    fn visit_constructor_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ConstructorCallArgs>,
    ) -> Result<Self::ConstructorCallArgsRet, Self::Error>;

    type ConstructorCallExprRet;
    fn visit_constructor_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error>;

    type PropertyAccessExprRet;
    fn visit_property_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::PropertyAccessExpr>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error>;

    type RefExprRet;
    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error>;

    type DerefExprRet;
    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error>;

    type UnsafeExprRet;
    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error>;

    type LiteralExprRet;
    fn visit_literal_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralExpr>,
    ) -> Result<Self::LiteralExprRet, Self::Error>;

    type CastExprRet;
    fn visit_cast_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error>;

    type TypeExprRet;
    fn visit_type_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeExpr>,
    ) -> Result<Self::TypeExprRet, Self::Error>;

    type BlockExprRet;
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error>;

    type ImportExprRet;
    fn visit_import_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error>;

    type TypeRet;
    fn visit_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Type>,
    ) -> Result<Self::TypeRet, Self::Error>;

    type NamedFieldTypeRet;
    fn visit_named_field_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedFieldTypeEntry>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error>;

    type FnTypeRet;
    fn visit_function_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FnType>,
    ) -> Result<Self::FnTypeRet, Self::Error>;

    type TypeFunctionParamRet;
    fn visit_type_function_param(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionParam>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error>;

    type TypeFunctionRet;
    fn visit_type_function(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunction>,
    ) -> Result<Self::TypeFunctionRet, Self::Error>;

    type TypeFunctionCallRet;
    fn visit_type_function_call(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionCall>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error>;

    type NamedTypeRet;
    fn visit_named_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedType>,
    ) -> Result<Self::NamedTypeRet, Self::Error>;

    type RefTypeRet;
    fn visit_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefType>,
    ) -> Result<Self::RefTypeRet, Self::Error>;

    type MergedTypeRet;
    fn visit_merged_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MergedType>,
    ) -> Result<Self::MergedTypeRet, Self::Error>;

    type MapLiteralRet;
    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLiteral>,
    ) -> Result<Self::MapLiteralRet, Self::Error>;

    type MapLiteralEntryRet;
    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLiteralEntry>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error>;

    type ListLiteralRet;
    fn visit_list_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListLiteral>,
    ) -> Result<Self::ListLiteralRet, Self::Error>;

    type SetLiteralRet;
    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetLiteral>,
    ) -> Result<Self::SetLiteralRet, Self::Error>;

    type TupleLiteralEntryRet;
    fn visit_tuple_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteralEntry>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error>;

    type TupleLiteralRet;
    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteral>,
    ) -> Result<Self::TupleLiteralRet, Self::Error>;

    type StrLiteralRet;
    fn visit_str_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error>;

    type CharLiteralRet;
    fn visit_char_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error>;

    type FloatLiteralRet;
    fn visit_float_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error>;

    type BoolLiteralRet;
    fn visit_bool_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error>;

    type IntLiteralRet;
    fn visit_int_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error>;

    type FunctionDefRet;
    fn visit_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDef>,
    ) -> Result<Self::FunctionDefRet, Self::Error>;

    type FunctionDefArgRet;
    fn visit_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDefArg>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error>;

    type BlockRet;
    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error>;

    type MatchCaseRet;
    fn visit_match_case(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error>;

    type MatchBlockRet;
    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error>;

    type LoopBlockRet;
    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error>;

    type ForLoopBlockRet;
    fn visit_for_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error>;

    type WhileLoopBlockRet;
    fn visit_while_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error>;

    type ModBlockRet;
    fn visit_mod_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error>;

    type ImplBlockRet;
    fn visit_impl_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error>;

    type IfClauseRet;
    fn visit_if_clause(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error>;

    type IfBlockRet;
    fn visit_if_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error>;

    type BodyBlockRet;
    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error>;

    type ReturnStatementRet;
    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error>;

    type BreakStatementRet;
    fn visit_break_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error>;

    type ContinueStatementRet;
    fn visit_continue_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error>;

    type VisibilityRet;
    fn visit_visibility_modifier(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error>;

    type MutabilityRet;
    fn visit_mutability_modifier(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error>;

    type DeclarationRet;
    fn visit_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error>;

    type MergeDeclarationRet;
    fn visit_merge_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error>;

    type AssignExpressionRet;
    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AssignExpression>,
    ) -> Result<Self::AssignExpressionRet, Self::Error>;

    type AssignOpExpressionRet;
    fn visit_assign_op_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AssignOpExpression>,
    ) -> Result<Self::AssignOpExpressionRet, Self::Error>;

    type BinaryExpressionRet;
    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BinaryExpression>,
    ) -> Result<Self::BinaryExpressionRet, Self::Error>;

    type UnaryExpressionRet;
    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::UnaryExpression>,
    ) -> Result<Self::UnaryExpressionRet, Self::Error>;

    type IndexExpressionRet;
    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IndexExpression>,
    ) -> Result<Self::IndexExpressionRet, Self::Error>;

    type StructDefEntryRet;
    fn visit_struct_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructDefEntry>,
    ) -> Result<Self::StructDefEntryRet, Self::Error>;

    type StructDefRet;
    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error>;

    type EnumDefEntryRet;
    fn visit_enum_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error>;

    type EnumDefRet;
    fn visit_enum_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error>;

    type TraitDefRet;
    fn visit_trait_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error>;

    type PatternRet;
    fn visit_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Pattern>,
    ) -> Result<Self::PatternRet, Self::Error>;

    type TraitImplRet;
    fn visit_trait_impl(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error>;

    type TypeFunctionDefRet;
    fn visit_type_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDef>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error>;

    type TypeFunctionDefArgRet;
    fn visit_type_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDefArg>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error>;

    type ConstructorPatternRet;
    fn visit_constructor_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ConstructorPattern>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error>;

    type NamespacePatternRet;
    fn visit_namespace_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamespacePattern>,
    ) -> Result<Self::NamespacePatternRet, Self::Error>;

    type TuplePatternEntryRet;
    fn visit_tuple_pattern_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePatternEntry>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error>;

    type TuplePatternRet;
    fn visit_tuple_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePattern>,
    ) -> Result<Self::TuplePatternRet, Self::Error>;

    type ListPatternRet;
    fn visit_list_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListPattern>,
    ) -> Result<Self::ListPatternRet, Self::Error>;

    type TupleTypeRet;
    fn visit_tuple_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleType>,
    ) -> Result<Self::TupleTypeRet, Self::Error>;

    type ListTypeRet;
    fn visit_list_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListType>,
    ) -> Result<Self::ListTypeRet, Self::Error>;

    type SetTypeRet;
    fn visit_set_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetType>,
    ) -> Result<Self::SetTypeRet, Self::Error>;

    type MapTypeRet;
    fn visit_map_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapType>,
    ) -> Result<Self::MapTypeRet, Self::Error>;

    type StrLiteralPatternRet;
    fn visit_str_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error>;

    type CharLiteralPatternRet;
    fn visit_char_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error>;

    type IntLiteralPatternRet;
    fn visit_int_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error>;

    type FloatLiteralPatternRet;
    fn visit_float_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error>;

    type BoolLiteralPatternRet;
    fn visit_bool_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error>;

    type LiteralPatternRet;
    fn visit_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error>;

    type OrPatternRet;
    fn visit_or_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::OrPattern>,
    ) -> Result<Self::OrPatternRet, Self::Error>;

    type IfPatternRet;
    fn visit_if_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IfPattern>,
    ) -> Result<Self::IfPatternRet, Self::Error>;

    type BindingPatternRet;
    fn visit_binding_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BindingPattern>,
    ) -> Result<Self::BindingPatternRet, Self::Error>;

    type SpreadPatternRet;
    fn visit_spread_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SpreadPattern>,
    ) -> Result<Self::SpreadPatternRet, Self::Error>;

    type IgnorePatternRet;
    fn visit_ignore_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error>;

    type DestructuringPatternRet;
    fn visit_destructuring_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DestructuringPattern>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error>;

    type ModuleRet;
    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error>;
}

pub trait AstVisitorMut: Sized {
    /// Context type immutably passed to each visitor method for separating
    /// mutable from immutable context.
    type Ctx;

    /// What container to use to collect multiple children, used by [walk].
    type CollectionContainer<T>: Sized;

    /// Try collect an iterator of results into a container specified by
    /// [Self::CollectionContainer].
    fn try_collect_items<T, E, I: Iterator<Item = Result<T, E>>>(
        ctx: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E>;

    /// Collect an iterator of items into a container specified by
    /// [Self::CollectionContainer].
    fn collect_items<T, E, I: Iterator<Item = T>>(
        ctx: &Self::Ctx,
        items: I,
    ) -> Self::CollectionContainer<T> {
        Self::try_collect_items::<T, Infallible, _>(ctx, items.map(|item| Ok(item))).unwrap()
    }

    /// The error type to use for each visit method.
    type Error;

    type ImportRet;
    fn visit_import(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error>;

    type NameRet;
    fn visit_name(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Name>,
    ) -> Result<Self::NameRet, Self::Error>;

    type AccessNameRet;
    fn visit_access_name(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::AccessName>,
    ) -> Result<Self::AccessNameRet, Self::Error>;

    type LiteralRet;
    fn visit_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Literal>,
    ) -> Result<Self::LiteralRet, Self::Error>;

    type BinaryOperatorRet;
    fn visit_binary_operator(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BinOp>,
    ) -> Result<Self::BinaryOperatorRet, Self::Error>;

    type UnaryOperatorRet;
    fn visit_unary_operator(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::UnOp>,
    ) -> Result<Self::UnaryOperatorRet, Self::Error>;

    type ExpressionRet;
    fn visit_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Expression>,
    ) -> Result<Self::ExpressionRet, Self::Error>;

    type VariableExprRet;
    fn visit_variable_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error>;

    type DirectiveExprRet;
    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error>;

    type ConstructorCallArgRet;
    fn visit_constructor_call_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error>;

    type ConstructorCallArgsRet;
    fn visit_constructor_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ConstructorCallArgs>,
    ) -> Result<Self::ConstructorCallArgsRet, Self::Error>;

    type ConstructorCallExprRet;
    fn visit_constructor_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error>;

    type PropertyAccessExprRet;
    fn visit_property_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::PropertyAccessExpr>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error>;

    type RefExprRet;
    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error>;

    type DerefExprRet;
    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error>;

    type UnsafeExprRet;
    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error>;

    type LiteralExprRet;
    fn visit_literal_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::LiteralExpr>,
    ) -> Result<Self::LiteralExprRet, Self::Error>;

    type CastExprRet;
    fn visit_cast_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error>;

    type TypeExprRet;
    fn visit_type_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TypeExpr>,
    ) -> Result<Self::TypeExprRet, Self::Error>;

    type BlockExprRet;
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error>;

    type ImportExprRet;
    fn visit_import_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error>;

    type TypeRet;
    fn visit_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Type>,
    ) -> Result<Self::TypeRet, Self::Error>;

    type NamedFieldTypeRet;
    fn visit_named_field_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::NamedFieldTypeEntry>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error>;

    type FnTypeRet;
    fn visit_function_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::FnType>,
    ) -> Result<Self::FnTypeRet, Self::Error>;

    type TypeFunctionParamRet;
    fn visit_type_function_param(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TypeFunctionParam>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error>;

    type TypeFunctionRet;
    fn visit_type_function(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TypeFunction>,
    ) -> Result<Self::TypeFunctionRet, Self::Error>;

    type TypeFunctionCallRet;
    fn visit_type_function_call(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TypeFunctionCall>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error>;

    type NamedTypeRet;
    fn visit_named_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::NamedType>,
    ) -> Result<Self::NamedTypeRet, Self::Error>;

    type RefTypeRet;
    fn visit_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::RefType>,
    ) -> Result<Self::RefTypeRet, Self::Error>;

    type MergedTypeRet;
    fn visit_merged_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MergedType>,
    ) -> Result<Self::MergedTypeRet, Self::Error>;

    type MapLiteralRet;
    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MapLiteral>,
    ) -> Result<Self::MapLiteralRet, Self::Error>;

    type MapLiteralEntryRet;
    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MapLiteralEntry>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error>;

    type ListLiteralRet;
    fn visit_list_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ListLiteral>,
    ) -> Result<Self::ListLiteralRet, Self::Error>;

    type SetLiteralRet;
    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::SetLiteral>,
    ) -> Result<Self::SetLiteralRet, Self::Error>;

    type TupleLiteralEntryRet;
    fn visit_tuple_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TupleLiteralEntry>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error>;

    type TupleLiteralRet;
    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TupleLiteral>,
    ) -> Result<Self::TupleLiteralRet, Self::Error>;

    type StrLiteralRet;
    fn visit_str_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error>;

    type CharLiteralRet;
    fn visit_char_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error>;

    type FloatLiteralRet;
    fn visit_float_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error>;

    type BoolLiteralRet;
    fn visit_bool_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error>;

    type IntLiteralRet;
    fn visit_int_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error>;

    type FunctionDefRet;
    fn visit_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::FunctionDef>,
    ) -> Result<Self::FunctionDefRet, Self::Error>;

    type FunctionDefArgRet;
    fn visit_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::FunctionDefArg>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error>;

    type BlockRet;
    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error>;

    type MatchCaseRet;
    fn visit_match_case(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error>;

    type MatchBlockRet;
    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error>;

    type LoopBlockRet;
    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error>;

    type ForLoopBlockRet;
    fn visit_for_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error>;

    type WhileLoopBlockRet;
    fn visit_while_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error>;

    type ModBlockRet;
    fn visit_mod_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error>;

    type ImplBlockRet;
    fn visit_impl_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error>;

    type IfClauseRet;
    fn visit_if_clause(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error>;

    type IfBlockRet;
    fn visit_if_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error>;

    type BodyBlockRet;
    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error>;

    type ReturnStatementRet;
    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error>;

    type BreakStatementRet;
    fn visit_break_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error>;

    type ContinueStatementRet;
    fn visit_continue_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error>;

    type VisibilityRet;
    fn visit_visibility_modifier(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error>;

    type MutabilityRet;
    fn visit_mutability_modifier(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error>;

    type DeclarationRet;
    fn visit_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error>;

    type MergeDeclarationRet;
    fn visit_merge_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error>;

    type AssignExpressionRet;
    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::AssignExpression>,
    ) -> Result<Self::AssignExpressionRet, Self::Error>;

    type AssignOpExpressionRet;
    fn visit_assign_op_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::AssignOpExpression>,
    ) -> Result<Self::AssignOpExpressionRet, Self::Error>;

    type BinaryExpressionRet;
    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BinaryExpression>,
    ) -> Result<Self::BinaryExpressionRet, Self::Error>;

    type UnaryExpressionRet;
    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::UnaryExpression>,
    ) -> Result<Self::UnaryExpressionRet, Self::Error>;

    type IndexExpressionRet;
    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IndexExpression>,
    ) -> Result<Self::IndexExpressionRet, Self::Error>;

    type StructDefEntryRet;
    fn visit_struct_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::StructDefEntry>,
    ) -> Result<Self::StructDefEntryRet, Self::Error>;

    type StructDefRet;
    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error>;

    type EnumDefEntryRet;
    fn visit_enum_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error>;

    type EnumDefRet;
    fn visit_enum_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error>;

    type TraitDefRet;
    fn visit_trait_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error>;

    type PatternRet;
    fn visit_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Pattern>,
    ) -> Result<Self::PatternRet, Self::Error>;

    type TraitImplRet;
    fn visit_trait_impl(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error>;

    type TypeFunctionDefRet;
    fn visit_type_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TypeFunctionDef>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error>;

    type TypeFunctionDefArgRet;
    fn visit_type_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TypeFunctionDefArg>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error>;

    type ConstructorPatternRet;
    fn visit_constructor_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ConstructorPattern>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error>;

    type NamespacePatternRet;
    fn visit_namespace_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::NamespacePattern>,
    ) -> Result<Self::NamespacePatternRet, Self::Error>;

    type TuplePatternEntryRet;
    fn visit_tuple_pattern_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TuplePatternEntry>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error>;

    type TuplePatternRet;
    fn visit_tuple_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TuplePattern>,
    ) -> Result<Self::TuplePatternRet, Self::Error>;

    type ListPatternRet;
    fn visit_list_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ListPattern>,
    ) -> Result<Self::ListPatternRet, Self::Error>;

    type TupleTypeRet;
    fn visit_tuple_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TupleType>,
    ) -> Result<Self::TupleTypeRet, Self::Error>;

    type ListTypeRet;
    fn visit_list_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ListType>,
    ) -> Result<Self::ListTypeRet, Self::Error>;

    type SetTypeRet;
    fn visit_set_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::SetType>,
    ) -> Result<Self::SetTypeRet, Self::Error>;

    type MapTypeRet;
    fn visit_map_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MapType>,
    ) -> Result<Self::MapTypeRet, Self::Error>;

    type StrLiteralPatternRet;
    fn visit_str_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error>;

    type CharLiteralPatternRet;
    fn visit_char_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error>;

    type IntLiteralPatternRet;
    fn visit_int_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error>;

    type FloatLiteralPatternRet;
    fn visit_float_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error>;

    type BoolLiteralPatternRet;
    fn visit_bool_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error>;

    type LiteralPatternRet;
    fn visit_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error>;

    type OrPatternRet;
    fn visit_or_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::OrPattern>,
    ) -> Result<Self::OrPatternRet, Self::Error>;

    type IfPatternRet;
    fn visit_if_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IfPattern>,
    ) -> Result<Self::IfPatternRet, Self::Error>;

    type BindingPatternRet;
    fn visit_binding_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BindingPattern>,
    ) -> Result<Self::BindingPatternRet, Self::Error>;

    type SpreadPatternRet;
    fn visit_spread_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::SpreadPattern>,
    ) -> Result<Self::SpreadPatternRet, Self::Error>;

    type IgnorePatternRet;
    fn visit_ignore_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error>;

    type DestructuringPatternRet;
    fn visit_destructuring_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::DestructuringPattern>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error>;

    type ModuleRet;
    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error>;
}

/// Contains helper functions and structures to traverse AST nodes using a given
/// visitor.
///
/// Structures are defined which mirror the layout of the AST nodes, but instead
/// of having AST nodes as children, they have the [AstVisitor] output type for
/// each node.
///
/// For enums, there is an additional `*_same_children` function, which
/// traverses the member of each variant and returns the inner type, given that
/// all variants have the same declared type within the visitor.
pub mod walk {
    use super::{ast, AstVisitor};

    pub struct FunctionDefArg<V: AstVisitor> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
        pub default: Option<V::ExpressionRet>,
    }

    pub fn walk_function_def_arg<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FunctionDefArg>,
    ) -> Result<FunctionDefArg<V>, V::Error> {
        Ok(FunctionDefArg {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            ty: node
                .ty
                .as_ref()
                .map(|t| visitor.visit_type(ctx, t.ast_ref()))
                .transpose()?,
            default: node
                .default
                .as_ref()
                .map(|t| visitor.visit_expression(ctx, t.ast_ref()))
                .transpose()?,
        })
    }

    pub struct FunctionDef<V: AstVisitor> {
        pub args: V::CollectionContainer<V::FunctionDefArgRet>,
        pub return_ty: Option<V::TypeRet>,
        pub fn_body: V::ExpressionRet,
    }

    pub fn walk_function_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FunctionDef>,
    ) -> Result<FunctionDef<V>, V::Error> {
        Ok(FunctionDef {
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter()
                    .map(|a| visitor.visit_function_def_arg(ctx, a.ast_ref())),
            )?,
            return_ty: node
                .return_ty
                .as_ref()
                .map(|t| visitor.visit_type(ctx, t.ast_ref()))
                .transpose()?,
            fn_body: visitor.visit_expression(ctx, node.fn_body.ast_ref())?,
        })
    }

    pub enum Expression<V: AstVisitor> {
        ConstructorCall(V::ConstructorCallExprRet),
        Directive(V::DirectiveExprRet),
        Declaration(V::DeclarationRet),
        Variable(V::VariableExprRet),
        PropertyAccess(V::PropertyAccessExprRet),
        Ref(V::RefExprRet),
        Deref(V::DerefExprRet),
        Unsafe(V::UnsafeExprRet),
        LiteralExpr(V::LiteralExprRet),
        Typed(V::CastExprRet),
        Block(V::BlockExprRet),
        Import(V::ImportExprRet),
        StructDef(V::StructDefRet),
        EnumDef(V::EnumDefRet),
        TypeFunctionDef(V::TypeFunctionDefRet),
        TraitDef(V::TraitDefRet),
        FunctionDef(V::FunctionDefRet),
        Type(V::TypeExprRet),
        Return(V::ReturnStatementRet),
        Break(V::BreakStatementRet),
        Continue(V::ContinueStatementRet),
        Assign(V::AssignExpressionRet),
        AssignOp(V::AssignOpExpressionRet),
        MergeDeclaration(V::MergeDeclarationRet),
        TraitImpl(V::TraitImplRet),
        BinaryExpr(V::BinaryExpressionRet),
        UnaryExpr(V::UnaryExpressionRet),
        Index(V::IndexExpressionRet),
    }

    pub fn walk_expression<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Expression>,
    ) -> Result<Expression<V>, V::Error> {
        Ok(match node.kind() {
            ast::ExpressionKind::ConstructorCall(inner) => Expression::ConstructorCall(
                visitor.visit_constructor_call_expr(ctx, node.with_body(inner))?,
            ),
            ast::ExpressionKind::Type(inner) => {
                Expression::Type(visitor.visit_type_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::Directive(inner) => {
                Expression::Directive(visitor.visit_directive_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::Declaration(inner) => {
                Expression::Declaration(visitor.visit_declaration(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::MergeDeclaration(inner) => Expression::MergeDeclaration(
                visitor.visit_merge_declaration(ctx, node.with_body(inner))?,
            ),
            ast::ExpressionKind::Variable(inner) => {
                Expression::Variable(visitor.visit_variable_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::PropertyAccess(inner) => Expression::PropertyAccess({
                visitor.visit_property_access_expr(ctx, node.with_body(inner))?
            }),
            ast::ExpressionKind::Ref(inner) => {
                Expression::Ref(visitor.visit_ref_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::Deref(inner) => {
                Expression::Deref(visitor.visit_deref_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::Unsafe(inner) => {
                Expression::Unsafe(visitor.visit_unsafe_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::LiteralExpr(inner) => {
                Expression::LiteralExpr(visitor.visit_literal_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::As(inner) => {
                Expression::Typed(visitor.visit_cast_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::Block(inner) => {
                Expression::Block(visitor.visit_block_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::Import(inner) => {
                Expression::Import(visitor.visit_import_expr(ctx, node.with_body(inner))?)
            }
            ast::ExpressionKind::StructDef(r) => {
                Expression::StructDef(visitor.visit_struct_def(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::EnumDef(r) => {
                Expression::EnumDef(visitor.visit_enum_def(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::TypeFunctionDef(r) => Expression::TypeFunctionDef(
                visitor.visit_type_function_def(ctx, node.with_body(r))?,
            ),
            ast::ExpressionKind::TraitDef(r) => {
                Expression::TraitDef(visitor.visit_trait_def(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::FunctionDef(r) => {
                Expression::FunctionDef(visitor.visit_function_def(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::Return(r) => {
                Expression::Return(visitor.visit_return_statement(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::Break(r) => {
                Expression::Break(visitor.visit_break_statement(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::Continue(r) => {
                Expression::Continue(visitor.visit_continue_statement(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::Assign(r) => {
                Expression::Assign(visitor.visit_assign_expr(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::AssignOp(r) => {
                Expression::AssignOp(visitor.visit_assign_op_expr(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::TraitImpl(r) => {
                Expression::TraitImpl(visitor.visit_trait_impl(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::BinaryExpr(r) => {
                Expression::BinaryExpr(visitor.visit_binary_expr(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::UnaryExpr(r) => {
                Expression::UnaryExpr(visitor.visit_unary_expr(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::Index(r) => {
                Expression::Index(visitor.visit_index_expr(ctx, node.with_body(r))?)
            }
        })
    }

    pub fn walk_expression_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Expression>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            ConstructorCallExprRet = Ret,
            DirectiveExprRet = Ret,
            DeclarationRet = Ret,
            MergeDeclarationRet = Ret,
            VariableExprRet = Ret,
            PropertyAccessExprRet = Ret,
            RefExprRet = Ret,
            DerefExprRet = Ret,
            UnsafeExprRet = Ret,
            LiteralExprRet = Ret,
            CastExprRet = Ret,
            BlockExprRet = Ret,
            ImportExprRet = Ret,
            StructDefRet = Ret,
            EnumDefRet = Ret,
            TypeFunctionDefRet = Ret,
            TraitDefRet = Ret,
            TraitImplRet = Ret,
            FunctionDefRet = Ret,
            TypeExprRet = Ret,
            ReturnStatementRet = Ret,
            BreakStatementRet = Ret,
            ContinueStatementRet = Ret,
            AssignExpressionRet = Ret,
            AssignOpExpressionRet = Ret,
            BinaryExpressionRet = Ret,
            UnaryExpressionRet = Ret,
            IndexExpressionRet = Ret,
        >,
    {
        Ok(match walk_expression(visitor, ctx, node)? {
            Expression::ConstructorCall(r) => r,
            Expression::Directive(r) => r,
            Expression::Declaration(r) => r,
            Expression::MergeDeclaration(r) => r,
            Expression::Variable(r) => r,
            Expression::PropertyAccess(r) => r,
            Expression::Ref(r) => r,
            Expression::Deref(r) => r,
            Expression::Unsafe(r) => r,
            Expression::LiteralExpr(r) => r,
            Expression::Typed(r) => r,
            Expression::Block(r) => r,
            Expression::Import(r) => r,
            Expression::StructDef(r) => r,
            Expression::EnumDef(r) => r,
            Expression::TypeFunctionDef(r) => r,
            Expression::TraitDef(r) => r,
            Expression::TraitImpl(r) => r,
            Expression::FunctionDef(r) => r,
            Expression::Type(r) => r,
            Expression::Return(r) => r,
            Expression::Break(r) => r,
            Expression::Continue(r) => r,
            Expression::Assign(r) => r,
            Expression::AssignOp(r) => r,
            Expression::BinaryExpr(r) => r,
            Expression::UnaryExpr(r) => r,
            Expression::Index(r) => r,
        })
    }

    pub struct VariableExpr<V: AstVisitor> {
        pub name: V::AccessNameRet,
        pub type_args: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_variable_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::VariableExpr>,
    ) -> Result<VariableExpr<V>, V::Error> {
        Ok(VariableExpr {
            name: visitor.visit_access_name(ctx, node.name.ast_ref())?,
            type_args: V::try_collect_items(
                ctx,
                node.type_args
                    .iter()
                    .map(|t| visitor.visit_named_field_type(ctx, t.ast_ref())),
            )?,
        })
    }

    pub struct DirectiveExpr<V: AstVisitor> {
        pub name: V::NameRet,
        pub subject: V::ExpressionRet,
    }

    pub fn walk_directive_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::DirectiveExpr>,
    ) -> Result<DirectiveExpr<V>, V::Error> {
        Ok(DirectiveExpr {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            subject: visitor.visit_expression(ctx, node.subject.ast_ref())?,
        })
    }

    pub struct ConstructorCallArg<V: AstVisitor> {
        pub name: Option<V::NameRet>,
        pub value: V::ExpressionRet,
    }

    pub fn walk_constructor_call_arg<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ConstructorCallArg>,
    ) -> Result<ConstructorCallArg<V>, V::Error> {
        Ok(ConstructorCallArg {
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
            value: visitor.visit_expression(ctx, node.value.ast_ref())?,
        })
    }

    pub struct ConstructorCallArgs<V: AstVisitor> {
        pub entries: V::CollectionContainer<V::ConstructorCallArgRet>,
    }

    pub fn walk_constructor_call_args<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ConstructorCallArgs>,
    ) -> Result<ConstructorCallArgs<V>, V::Error> {
        Ok(ConstructorCallArgs {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter()
                    .map(|e| visitor.visit_constructor_call_arg(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct FunctionCallExpr<V: AstVisitor> {
        pub subject: V::ExpressionRet,
        pub args: V::ConstructorCallArgsRet,
    }

    pub fn walk_constructor_call_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ConstructorCallExpr>,
    ) -> Result<FunctionCallExpr<V>, V::Error> {
        Ok(FunctionCallExpr {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref())?,
            args: visitor.visit_constructor_call_args(ctx, node.args.ast_ref())?,
        })
    }

    pub struct PropertyAccessExpr<V: AstVisitor> {
        pub subject: V::ExpressionRet,
        pub property: V::NameRet,
    }

    pub fn walk_property_access_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::PropertyAccessExpr>,
    ) -> Result<PropertyAccessExpr<V>, V::Error> {
        Ok(PropertyAccessExpr {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref())?,
            property: visitor.visit_name(ctx, node.property.ast_ref())?,
        })
    }

    pub struct RefExpr<V: AstVisitor> {
        pub inner_expr: V::ExpressionRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::RefExpr>,
    ) -> Result<RefExpr<V>, V::Error> {
        Ok(RefExpr {
            inner_expr: visitor.visit_expression(ctx, node.inner_expr.ast_ref())?,
            mutability: node
                .mutability
                .as_ref()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct DerefExpr<V: AstVisitor>(pub V::ExpressionRet);

    pub fn walk_deref_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::DerefExpr>,
    ) -> Result<DerefExpr<V>, V::Error> {
        Ok(DerefExpr(visitor.visit_expression(ctx, node.0.ast_ref())?))
    }

    pub struct UnsafeExpr<V: AstVisitor>(pub V::ExpressionRet);

    pub fn walk_unsafe_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::UnsafeExpr>,
    ) -> Result<UnsafeExpr<V>, V::Error> {
        Ok(UnsafeExpr(visitor.visit_expression(ctx, node.0.ast_ref())?))
    }

    pub struct LiteralExpr<V: AstVisitor>(pub V::LiteralRet);

    pub fn walk_literal_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LiteralExpr>,
    ) -> Result<LiteralExpr<V>, V::Error> {
        Ok(LiteralExpr(visitor.visit_literal(ctx, node.0.ast_ref())?))
    }

    pub struct AsExpr<V: AstVisitor> {
        pub ty: V::TypeRet,
        pub expr: V::ExpressionRet,
    }

    pub fn walk_cast_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::CastExpr>,
    ) -> Result<AsExpr<V>, V::Error> {
        Ok(AsExpr {
            ty: visitor.visit_type(ctx, node.ty.ast_ref())?,
            expr: visitor.visit_expression(ctx, node.expr.ast_ref())?,
        })
    }

    pub struct TypeExpr<V: AstVisitor>(pub V::TypeRet);

    pub fn walk_type_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeExpr>,
    ) -> Result<TypeExpr<V>, V::Error> {
        Ok(TypeExpr(visitor.visit_type(ctx, node.0.ast_ref())?))
    }

    pub struct BlockExpr<V: AstVisitor>(pub V::BlockRet);

    pub fn walk_block_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BlockExpr>,
    ) -> Result<BlockExpr<V>, V::Error> {
        Ok(BlockExpr(visitor.visit_block(ctx, node.0.ast_ref())?))
    }

    pub struct ImportExpr<V: AstVisitor>(pub V::ImportRet);

    pub fn walk_import_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ImportExpr>,
    ) -> Result<ImportExpr<V>, V::Error> {
        Ok(ImportExpr(visitor.visit_import(ctx, node.0.ast_ref())?))
    }

    pub enum Literal<V: AstVisitor> {
        Str(V::StrLiteralRet),
        Char(V::CharLiteralRet),
        Int(V::IntLiteralRet),
        Float(V::FloatLiteralRet),
        Bool(V::BoolLiteralRet),
        Set(V::SetLiteralRet),
        Map(V::MapLiteralRet),
        List(V::ListLiteralRet),
        Tuple(V::TupleLiteralRet),
    }

    pub fn walk_literal<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Literal>,
    ) -> Result<Literal<V>, V::Error> {
        Ok(match &*node {
            ast::Literal::Str(r) => {
                Literal::Str(visitor.visit_str_literal(ctx, node.with_body(r))?)
            }
            ast::Literal::Char(r) => {
                Literal::Char(visitor.visit_char_literal(ctx, node.with_body(r))?)
            }
            ast::Literal::Int(r) => {
                Literal::Int(visitor.visit_int_literal(ctx, node.with_body(r))?)
            }
            ast::Literal::Float(r) => {
                Literal::Float(visitor.visit_float_literal(ctx, node.with_body(r))?)
            }
            ast::Literal::Bool(r) => {
                Literal::Bool(visitor.visit_bool_literal(ctx, node.with_body(r))?)
            }
            ast::Literal::Set(r) => {
                Literal::Set(visitor.visit_set_literal(ctx, node.with_body(r))?)
            }
            ast::Literal::Map(r) => {
                Literal::Map(visitor.visit_map_literal(ctx, node.with_body(r))?)
            }
            ast::Literal::List(r) => {
                Literal::List(visitor.visit_list_literal(ctx, node.with_body(r))?)
            }
            ast::Literal::Tuple(r) => {
                Literal::Tuple(visitor.visit_tuple_literal(ctx, node.with_body(r))?)
            }
        })
    }

    pub fn walk_literal_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Literal>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            StrLiteralRet = Ret,
            CharLiteralRet = Ret,
            IntLiteralRet = Ret,
            FloatLiteralRet = Ret,
            BoolLiteralRet = Ret,
            SetLiteralRet = Ret,
            MapLiteralRet = Ret,
            ListLiteralRet = Ret,
            TupleLiteralRet = Ret,
        >,
    {
        Ok(match walk_literal(visitor, ctx, node)? {
            Literal::Str(r) => r,
            Literal::Char(r) => r,
            Literal::Int(r) => r,
            Literal::Float(r) => r,
            Literal::Bool(r) => r,
            Literal::Set(r) => r,
            Literal::Map(r) => r,
            Literal::List(r) => r,
            Literal::Tuple(r) => r,
        })
    }

    pub struct MatchCase<V: AstVisitor> {
        pub pattern: V::PatternRet,
        pub expr: V::ExpressionRet,
    }

    pub fn walk_match_case<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<MatchCase<V>, V::Error> {
        Ok(MatchCase {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
            expr: visitor.visit_expression(ctx, node.expr.ast_ref())?,
        })
    }

    pub struct MatchBlock<V: AstVisitor> {
        pub subject: V::ExpressionRet,
        pub cases: V::CollectionContainer<V::MatchCaseRet>,
    }

    pub fn walk_match_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MatchBlock>,
    ) -> Result<MatchBlock<V>, V::Error> {
        Ok(MatchBlock {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref())?,
            cases: V::try_collect_items(
                ctx,
                node.cases
                    .iter()
                    .map(|c| visitor.visit_match_case(ctx, c.ast_ref())),
            )?,
        })
    }

    pub struct LoopBlock<V: AstVisitor>(pub V::BlockRet);

    pub fn walk_loop_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LoopBlock>,
    ) -> Result<LoopBlock<V>, V::Error> {
        Ok(LoopBlock(visitor.visit_block(ctx, node.0.ast_ref())?))
    }

    pub struct ForLoopBlock<V: AstVisitor> {
        pub pattern: V::PatternRet,
        pub iterator: V::ExpressionRet,
        pub body: V::BlockRet,
    }

    pub fn walk_for_loop_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ForLoopBlock>,
    ) -> Result<ForLoopBlock<V>, V::Error> {
        Ok(ForLoopBlock {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
            iterator: visitor.visit_expression(ctx, node.iterator.ast_ref())?,
            body: visitor.visit_block(ctx, node.body.ast_ref())?,
        })
    }

    pub struct WhileLoopBlock<V: AstVisitor> {
        pub condition: V::ExpressionRet,
        pub body: V::BlockRet,
    }

    pub fn walk_while_loop_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::WhileLoopBlock>,
    ) -> Result<WhileLoopBlock<V>, V::Error> {
        Ok(WhileLoopBlock {
            condition: visitor.visit_expression(ctx, node.condition.ast_ref())?,
            body: visitor.visit_block(ctx, node.body.ast_ref())?,
        })
    }

    pub struct ModBlock<V: AstVisitor>(pub V::BodyBlockRet);

    pub fn walk_mod_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ModBlock>,
    ) -> Result<ModBlock<V>, V::Error> {
        Ok(ModBlock(visitor.visit_body_block(ctx, node.0.ast_ref())?))
    }

    pub struct ImplBlock<V: AstVisitor>(pub V::BodyBlockRet);

    pub fn walk_impl_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ImplBlock>,
    ) -> Result<ImplBlock<V>, V::Error> {
        Ok(ImplBlock(visitor.visit_body_block(ctx, node.0.ast_ref())?))
    }

    pub struct IfClause<V: AstVisitor> {
        pub condition: V::ExpressionRet,
        pub body: V::BlockRet,
    }

    pub fn walk_if_clause<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::IfClause>,
    ) -> Result<IfClause<V>, V::Error> {
        Ok(IfClause {
            condition: visitor.visit_expression(ctx, node.condition.ast_ref())?,
            body: visitor.visit_block(ctx, node.body.ast_ref())?,
        })
    }

    pub struct IfBlock<V: AstVisitor> {
        pub clauses: V::CollectionContainer<V::IfClauseRet>,
        pub otherwise: Option<V::BlockRet>,
    }

    pub fn walk_if_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::IfBlock>,
    ) -> Result<IfBlock<V>, V::Error> {
        Ok(IfBlock {
            clauses: V::try_collect_items(
                ctx,
                node.clauses
                    .iter()
                    .map(|clause| visitor.visit_if_clause(ctx, clause.ast_ref())),
            )?,
            otherwise: node
                .otherwise
                .as_ref()
                .map(|body| visitor.visit_block(ctx, body.ast_ref()))
                .transpose()?,
        })
    }

    pub struct BodyBlock<V: AstVisitor> {
        pub statements: V::CollectionContainer<V::ExpressionRet>,
        pub expr: Option<V::ExpressionRet>,
    }

    pub fn walk_body_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<BodyBlock<V>, V::Error> {
        Ok(BodyBlock {
            statements: V::try_collect_items(
                ctx,
                node.statements
                    .iter()
                    .map(|s| visitor.visit_expression(ctx, s.ast_ref())),
            )?,
            expr: node
                .expr
                .as_ref()
                .map(|e| visitor.visit_expression(ctx, e.ast_ref()))
                .transpose()?,
        })
    }

    pub enum Block<V: AstVisitor> {
        Match(V::MatchBlockRet),
        Loop(V::LoopBlockRet),
        For(V::ForLoopBlockRet),
        While(V::WhileLoopBlockRet),
        Mod(V::ModBlockRet),
        Body(V::BodyBlockRet),
        Impl(V::ImplBlockRet),
        If(V::IfBlockRet),
    }

    pub fn walk_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Block>,
    ) -> Result<Block<V>, V::Error> {
        Ok(match &*node {
            ast::Block::Match(r) => {
                Block::Match(visitor.visit_match_block(ctx, node.with_body(r))?)
            }
            ast::Block::Loop(r) => Block::Loop(visitor.visit_loop_block(ctx, node.with_body(r))?),
            ast::Block::For(r) => Block::For(visitor.visit_for_loop_block(ctx, node.with_body(r))?),
            ast::Block::While(r) => {
                Block::While(visitor.visit_while_loop_block(ctx, node.with_body(r))?)
            }
            ast::Block::Mod(r) => Block::Mod(visitor.visit_mod_block(ctx, node.with_body(r))?),
            ast::Block::Body(r) => Block::Body(visitor.visit_body_block(ctx, node.with_body(r))?),
            ast::Block::Impl(r) => Block::Impl(visitor.visit_impl_block(ctx, node.with_body(r))?),
            ast::Block::If(r) => Block::If(visitor.visit_if_block(ctx, node.with_body(r))?),
        })
    }

    pub fn walk_block_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Block>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            MatchBlockRet = Ret,
            LoopBlockRet = Ret,
            ForLoopBlockRet = Ret,
            WhileLoopBlockRet = Ret,
            ModBlockRet = Ret,
            BodyBlockRet = Ret,
            IfBlockRet = Ret,
            ImplBlockRet = Ret,
        >,
    {
        Ok(match walk_block(visitor, ctx, node)? {
            Block::Match(r) => r,
            Block::Loop(r) => r,
            Block::For(r) => r,
            Block::If(r) => r,
            Block::While(r) => r,
            Block::Mod(r) => r,
            Block::Body(r) => r,
            Block::Impl(r) => r,
        })
    }

    pub struct SetLiteral<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_set_literal<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SetLiteral>,
    ) -> Result<SetLiteral<V>, V::Error> {
        Ok(SetLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter()
                    .map(|e| visitor.visit_expression(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct MapLiteralEntry<V: AstVisitor> {
        pub key: V::ExpressionRet,
        pub value: V::ExpressionRet,
    }

    pub fn walk_map_literal_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapLiteralEntry>,
    ) -> Result<MapLiteralEntry<V>, V::Error> {
        Ok(MapLiteralEntry {
            key: visitor.visit_expression(ctx, node.key.ast_ref())?,
            value: visitor.visit_expression(ctx, node.value.ast_ref())?,
        })
    }

    pub struct MapLiteral<V: AstVisitor> {
        pub entries: V::CollectionContainer<V::MapLiteralEntryRet>,
    }

    pub fn walk_map_literal<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapLiteral>,
    ) -> Result<MapLiteral<V>, V::Error> {
        Ok(MapLiteral {
            entries: V::try_collect_items(
                ctx,
                node.elements
                    .iter()
                    .map(|e| visitor.visit_map_literal_entry(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct ListLiteral<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_list_literal<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListLiteral>,
    ) -> Result<ListLiteral<V>, V::Error> {
        Ok(ListLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter()
                    .map(|e| visitor.visit_expression(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct TupleLiteralEntry<V: AstVisitor> {
        pub name: Option<V::NameRet>,
        pub ty: Option<V::TypeRet>,
        pub value: V::ExpressionRet,
    }

    pub fn walk_tuple_literal_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteralEntry>,
    ) -> Result<TupleLiteralEntry<V>, V::Error> {
        Ok(TupleLiteralEntry {
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
            ty: node
                .ty
                .as_ref()
                .map(|t| visitor.visit_type(ctx, t.ast_ref()))
                .transpose()?,
            value: visitor.visit_expression(ctx, node.value.ast_ref())?,
        })
    }

    pub struct TupleLiteral<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::TupleLiteralEntryRet>,
    }

    pub fn walk_tuple_literal<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteral>,
    ) -> Result<TupleLiteral<V>, V::Error> {
        Ok(TupleLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter()
                    .map(|e| visitor.visit_tuple_literal_entry(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct NamedFieldTypeEntry<V: AstVisitor> {
        pub ty: V::TypeRet,
        pub name: Option<V::NameRet>,
    }

    pub fn walk_named_field_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::NamedFieldTypeEntry>,
    ) -> Result<NamedFieldTypeEntry<V>, V::Error> {
        Ok(NamedFieldTypeEntry {
            ty: visitor.visit_type(ctx, node.ty.ast_ref())?,
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
        })
    }

    pub struct FnType<V: AstVisitor> {
        pub args: V::CollectionContainer<V::NamedFieldTypeRet>,
        pub return_ty: V::TypeRet,
    }

    pub fn walk_function_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FnType>,
    ) -> Result<FnType<V>, V::Error> {
        Ok(FnType {
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter()
                    .map(|e| visitor.visit_named_field_type(ctx, e.ast_ref())),
            )?,
            return_ty: visitor.visit_type(ctx, node.return_ty.ast_ref())?,
        })
    }

    pub struct TupleType<V: AstVisitor> {
        pub entries: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_tuple_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleType>,
    ) -> Result<TupleType<V>, V::Error> {
        Ok(TupleType {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter()
                    .map(|e| visitor.visit_named_field_type(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct ListType<V: AstVisitor> {
        pub inner: V::TypeRet,
    }

    pub fn walk_list_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListType>,
    ) -> Result<ListType<V>, V::Error> {
        Ok(ListType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref())?,
        })
    }

    pub struct SetType<V: AstVisitor> {
        pub inner: V::TypeRet,
    }

    pub fn walk_set_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SetType>,
    ) -> Result<SetType<V>, V::Error> {
        Ok(SetType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref())?,
        })
    }

    pub struct MapType<V: AstVisitor> {
        pub key: V::TypeRet,
        pub value: V::TypeRet,
    }

    pub fn walk_map_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapType>,
    ) -> Result<MapType<V>, V::Error> {
        Ok(MapType {
            key: visitor.visit_type(ctx, node.key.ast_ref())?,
            value: visitor.visit_type(ctx, node.value.ast_ref())?,
        })
    }

    pub struct NamedType<V: AstVisitor> {
        pub name: V::AccessNameRet,
    }

    pub fn walk_named_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::NamedType>,
    ) -> Result<NamedType<V>, V::Error> {
        Ok(NamedType {
            name: visitor.visit_access_name(ctx, node.name.ast_ref())?,
        })
    }

    pub struct RefType<V: AstVisitor> {
        pub inner: V::TypeRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::RefType>,
    ) -> Result<RefType<V>, V::Error> {
        Ok(RefType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref())?,
            mutability: node
                .mutability
                .as_ref()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct MergedType<V: AstVisitor>(pub V::CollectionContainer<V::TypeRet>);

    pub fn walk_merged_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MergedType>,
    ) -> Result<MergedType<V>, V::Error> {
        Ok(MergedType(V::try_collect_items(
            ctx,
            node.0.iter().map(|a| visitor.visit_type(ctx, a.ast_ref())),
        )?))
    }

    pub struct TypeFunctionCall<V: AstVisitor> {
        pub subject: V::TypeRet,
        pub args: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_type_function_call<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionCall>,
    ) -> Result<TypeFunctionCall<V>, V::Error> {
        Ok(TypeFunctionCall {
            subject: visitor.visit_type(ctx, node.subject.ast_ref())?,
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter()
                    .map(|a| visitor.visit_named_field_type(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct TypeFunctionParam<V: AstVisitor> {
        pub name: V::NameRet,
        pub bound: Option<V::TypeRet>,
        pub default: Option<V::TypeRet>,
    }

    pub fn walk_type_function_param<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionParam>,
    ) -> Result<TypeFunctionParam<V>, V::Error> {
        Ok(TypeFunctionParam {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            bound: node
                .bound
                .as_ref()
                .map(|bound| visitor.visit_type(ctx, bound.ast_ref()))
                .transpose()?,
            default: node
                .default
                .as_ref()
                .map(|default| visitor.visit_type(ctx, default.ast_ref()))
                .transpose()?,
        })
    }

    pub struct TypeFunction<V: AstVisitor> {
        pub args: V::CollectionContainer<V::TypeFunctionParamRet>,
        pub return_ty: V::TypeRet,
    }

    pub fn walk_type_function<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunction>,
    ) -> Result<TypeFunction<V>, V::Error> {
        Ok(TypeFunction {
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter()
                    .map(|a| visitor.visit_type_function_param(ctx, a.ast_ref())),
            )?,
            return_ty: visitor.visit_type(ctx, node.return_ty.ast_ref())?,
        })
    }

    pub enum Type<V: AstVisitor> {
        Fn(V::FnTypeRet),
        Tuple(V::TupleTypeRet),
        List(V::ListTypeRet),
        Set(V::SetTypeRet),
        Map(V::MapTypeRet),
        Named(V::NamedTypeRet),
        Ref(V::RefTypeRet),
        Merged(V::MergedTypeRet),
        TypeFunction(V::TypeFunctionRet),
        TypeFunctionCall(V::TypeFunctionCallRet),
    }

    pub fn walk_type<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Type>,
    ) -> Result<Type<V>, V::Error> {
        Ok(match &*node {
            ast::Type::Fn(r) => Type::Fn(visitor.visit_function_type(ctx, node.with_body(r))?),
            ast::Type::Tuple(r) => Type::Tuple(visitor.visit_tuple_type(ctx, node.with_body(r))?),
            ast::Type::List(r) => Type::List(visitor.visit_list_type(ctx, node.with_body(r))?),
            ast::Type::Set(r) => Type::Set(visitor.visit_set_type(ctx, node.with_body(r))?),
            ast::Type::Map(r) => Type::Map(visitor.visit_map_type(ctx, node.with_body(r))?),
            ast::Type::Named(r) => Type::Named(visitor.visit_named_type(ctx, node.with_body(r))?),
            ast::Type::Ref(r) => Type::Ref(visitor.visit_ref_type(ctx, node.with_body(r))?),
            ast::Type::Merged(r) => {
                Type::Merged(visitor.visit_merged_type(ctx, node.with_body(r))?)
            }
            ast::Type::TypeFunction(r) => {
                Type::TypeFunction(visitor.visit_type_function(ctx, node.with_body(r))?)
            }
            ast::Type::TypeFunctionCall(r) => {
                Type::TypeFunctionCall(visitor.visit_type_function_call(ctx, node.with_body(r))?)
            }
        })
    }

    pub fn walk_type_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Type>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            FnTypeRet = Ret,
            TupleTypeRet = Ret,
            ListTypeRet = Ret,
            SetTypeRet = Ret,
            MapTypeRet = Ret,
            NamedTypeRet = Ret,
            RefTypeRet = Ret,
            MergedTypeRet = Ret,
            TypeFunctionRet = Ret,
            TypeFunctionCallRet = Ret,
        >,
    {
        Ok(match walk_type(visitor, ctx, node)? {
            Type::Fn(r) => r,
            Type::Tuple(r) => r,
            Type::List(r) => r,
            Type::Set(r) => r,
            Type::Map(r) => r,
            Type::Named(r) => r,
            Type::Ref(r) => r,
            Type::Merged(r) => r,
            Type::TypeFunction(r) => r,
            Type::TypeFunctionCall(r) => r,
        })
    }

    pub enum Pattern<V: AstVisitor> {
        Constructor(V::ConstructorPatternRet),
        Namespace(V::NamespacePatternRet),
        Tuple(V::TuplePatternRet),
        List(V::ListPatternRet),
        Literal(V::LiteralPatternRet),
        Or(V::OrPatternRet),
        If(V::IfPatternRet),
        Binding(V::BindingPatternRet),
        Spread(V::SpreadPatternRet),
        Ignore(V::IgnorePatternRet),
    }

    pub fn walk_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Pattern>,
    ) -> Result<Pattern<V>, V::Error> {
        Ok(match &*node {
            ast::Pattern::Constructor(r) => {
                Pattern::Constructor(visitor.visit_constructor_pattern(ctx, node.with_body(r))?)
            }
            ast::Pattern::Namespace(r) => {
                Pattern::Namespace(visitor.visit_namespace_pattern(ctx, node.with_body(r))?)
            }
            ast::Pattern::Tuple(r) => {
                Pattern::Tuple(visitor.visit_tuple_pattern(ctx, node.with_body(r))?)
            }
            ast::Pattern::List(r) => {
                Pattern::List(visitor.visit_list_pattern(ctx, node.with_body(r))?)
            }
            ast::Pattern::Literal(r) => {
                Pattern::Literal(visitor.visit_literal_pattern(ctx, node.with_body(r))?)
            }
            ast::Pattern::Or(r) => Pattern::Or(visitor.visit_or_pattern(ctx, node.with_body(r))?),
            ast::Pattern::If(r) => Pattern::If(visitor.visit_if_pattern(ctx, node.with_body(r))?),
            ast::Pattern::Binding(r) => {
                Pattern::Binding(visitor.visit_binding_pattern(ctx, node.with_body(r))?)
            }
            ast::Pattern::Spread(r) => {
                Pattern::Spread(visitor.visit_spread_pattern(ctx, node.with_body(r))?)
            }
            ast::Pattern::Ignore(r) => {
                Pattern::Ignore(visitor.visit_ignore_pattern(ctx, node.with_body(r))?)
            }
        })
    }

    pub fn walk_pattern_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Pattern>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            ConstructorPatternRet = Ret,
            NamespacePatternRet = Ret,
            TuplePatternRet = Ret,
            ListPatternRet = Ret,
            LiteralPatternRet = Ret,
            OrPatternRet = Ret,
            IfPatternRet = Ret,
            BindingPatternRet = Ret,
            SpreadPatternRet = Ret,
            IgnorePatternRet = Ret,
        >,
    {
        Ok(match walk_pattern(visitor, ctx, node)? {
            Pattern::Constructor(r) => r,
            Pattern::Namespace(r) => r,
            Pattern::Tuple(r) => r,
            Pattern::List(r) => r,
            Pattern::Literal(r) => r,
            Pattern::Or(r) => r,
            Pattern::If(r) => r,
            Pattern::Binding(r) => r,
            Pattern::Spread(r) => r,
            Pattern::Ignore(r) => r,
        })
    }

    pub struct OrPattern<V: AstVisitor> {
        pub variants: V::CollectionContainer<V::PatternRet>,
    }
    pub fn walk_or_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::OrPattern>,
    ) -> Result<OrPattern<V>, V::Error> {
        Ok(OrPattern {
            variants: V::try_collect_items(
                ctx,
                node.variants
                    .iter()
                    .map(|v| visitor.visit_pattern(ctx, v.ast_ref())),
            )?,
        })
    }

    pub struct ConstructorPattern<V: AstVisitor> {
        pub name: V::AccessNameRet,
        pub args: V::CollectionContainer<V::TuplePatternEntryRet>,
    }
    pub fn walk_constructor_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ConstructorPattern>,
    ) -> Result<ConstructorPattern<V>, V::Error> {
        Ok(ConstructorPattern {
            name: visitor.visit_access_name(ctx, node.name.ast_ref())?,
            args: V::try_collect_items(
                ctx,
                node.fields
                    .iter()
                    .map(|a| visitor.visit_tuple_pattern_entry(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct NamespacePattern<V: AstVisitor> {
        pub patterns: V::CollectionContainer<V::DestructuringPatternRet>,
    }
    pub fn walk_namespace_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::NamespacePattern>,
    ) -> Result<NamespacePattern<V>, V::Error> {
        Ok(NamespacePattern {
            patterns: V::try_collect_items(
                ctx,
                node.fields
                    .iter()
                    .map(|a| visitor.visit_destructuring_pattern(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct TuplePatternEntry<V: AstVisitor> {
        pub name: Option<V::NameRet>,
        pub pattern: V::PatternRet,
    }

    pub fn walk_tuple_pattern_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TuplePatternEntry>,
    ) -> Result<TuplePatternEntry<V>, V::Error> {
        Ok(TuplePatternEntry {
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
        })
    }

    pub struct TuplePattern<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::TuplePatternEntryRet>,
    }

    pub fn walk_tuple_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TuplePattern>,
    ) -> Result<TuplePattern<V>, V::Error> {
        Ok(TuplePattern {
            elements: V::try_collect_items(
                ctx,
                node.fields
                    .iter()
                    .map(|a| visitor.visit_tuple_pattern_entry(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct ListPattern<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::PatternRet>,
    }

    pub fn walk_list_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListPattern>,
    ) -> Result<ListPattern<V>, V::Error> {
        Ok(ListPattern {
            elements: V::try_collect_items(
                ctx,
                node.fields
                    .iter()
                    .map(|a| visitor.visit_pattern(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct IfPattern<V: AstVisitor> {
        pub pattern: V::PatternRet,
        pub condition: V::ExpressionRet,
    }
    pub fn walk_if_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::IfPattern>,
    ) -> Result<IfPattern<V>, V::Error> {
        Ok(IfPattern {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
            condition: visitor.visit_expression(ctx, node.condition.ast_ref())?,
        })
    }

    pub struct BindingPattern<V: AstVisitor> {
        pub name: V::NameRet,
        pub visibility: Option<V::VisibilityRet>,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_binding_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BindingPattern>,
    ) -> Result<BindingPattern<V>, V::Error> {
        Ok(BindingPattern {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            visibility: node
                .visibility
                .as_ref()
                .map(|inner| visitor.visit_visibility_modifier(ctx, inner.ast_ref()))
                .transpose()?,

            mutability: node
                .mutability
                .as_ref()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct SpreadPattern<V: AstVisitor> {
        pub name: Option<V::NameRet>,
    }

    pub fn walk_spread_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SpreadPattern>,
    ) -> Result<SpreadPattern<V>, V::Error> {
        Ok(SpreadPattern {
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
        })
    }

    pub enum LiteralPattern<V: AstVisitor> {
        Str(V::StrLiteralPatternRet),
        Char(V::CharLiteralPatternRet),
        Int(V::IntLiteralPatternRet),
        Float(V::FloatLiteralPatternRet),
        Bool(V::BoolLiteralPatternRet),
    }

    pub fn walk_literal_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<LiteralPattern<V>, V::Error> {
        Ok(match &*node {
            ast::LiteralPattern::Str(r) => {
                LiteralPattern::Str(visitor.visit_str_literal_pattern(ctx, node.with_body(r))?)
            }
            ast::LiteralPattern::Char(r) => {
                LiteralPattern::Char(visitor.visit_char_literal_pattern(ctx, node.with_body(r))?)
            }
            ast::LiteralPattern::Int(r) => {
                LiteralPattern::Int(visitor.visit_int_literal_pattern(ctx, node.with_body(r))?)
            }
            ast::LiteralPattern::Float(r) => {
                LiteralPattern::Float(visitor.visit_float_literal_pattern(ctx, node.with_body(r))?)
            }
            ast::LiteralPattern::Bool(r) => {
                LiteralPattern::Bool(visitor.visit_bool_literal_pattern(ctx, node.with_body(r))?)
            }
        })
    }

    pub fn walk_literal_pattern_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            StrLiteralPatternRet = Ret,
            CharLiteralPatternRet = Ret,
            IntLiteralPatternRet = Ret,
            FloatLiteralPatternRet = Ret,
            BoolLiteralPatternRet = Ret,
        >,
    {
        Ok(match walk_literal_pattern(visitor, ctx, node)? {
            LiteralPattern::Str(r) => r,
            LiteralPattern::Char(r) => r,
            LiteralPattern::Int(r) => r,
            LiteralPattern::Float(r) => r,
            LiteralPattern::Bool(r) => r,
        })
    }

    pub struct DestructuringPattern<V: AstVisitor> {
        pub name: V::NameRet,
        pub pattern: V::PatternRet,
    }
    pub fn walk_destructuring_pattern<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::DestructuringPattern>,
    ) -> Result<DestructuringPattern<V>, V::Error> {
        Ok(DestructuringPattern {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
        })
    }

    pub struct ReturnStatement<V: AstVisitor>(pub Option<V::ExpressionRet>);
    pub fn walk_return_statement<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ReturnStatement>,
    ) -> Result<ReturnStatement<V>, V::Error> {
        Ok(ReturnStatement(
            node.0
                .as_ref()
                .map(|n| visitor.visit_expression(ctx, n.ast_ref()))
                .transpose()?,
        ))
    }

    pub struct Declaration<V: AstVisitor> {
        pub pattern: V::PatternRet,
        pub ty: Option<V::TypeRet>,
        pub value: Option<V::ExpressionRet>,
    }

    pub fn walk_declaration<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Declaration<V>, V::Error> {
        Ok(Declaration {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
            ty: node
                .ty
                .as_ref()
                .map(|t| visitor.visit_type(ctx, t.ast_ref()))
                .transpose()?,
            value: node
                .value
                .as_ref()
                .map(|t| visitor.visit_expression(ctx, t.ast_ref()))
                .transpose()?,
        })
    }

    pub struct MergeDeclaration<V: AstVisitor> {
        pub decl: V::ExpressionRet,
        pub value: V::ExpressionRet,
    }

    pub fn walk_merge_declaration<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MergeDeclaration>,
    ) -> Result<MergeDeclaration<V>, V::Error> {
        Ok(MergeDeclaration {
            decl: visitor.visit_expression(ctx, node.decl.ast_ref())?,
            value: visitor.visit_expression(ctx, node.value.ast_ref())?,
        })
    }

    pub struct AssignStatement<V: AstVisitor> {
        pub lhs: V::ExpressionRet,
        pub rhs: V::ExpressionRet,
    }

    pub fn walk_assign_statement<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AssignExpression>,
    ) -> Result<AssignStatement<V>, V::Error> {
        Ok(AssignStatement {
            lhs: visitor.visit_expression(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_expression(ctx, node.rhs.ast_ref())?,
        })
    }

    pub struct AssignOpStatement<V: AstVisitor> {
        pub lhs: V::ExpressionRet,
        pub rhs: V::ExpressionRet,
        pub operator: V::BinaryOperatorRet,
    }
    pub fn walk_assign_op_statement<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AssignOpExpression>,
    ) -> Result<AssignOpStatement<V>, V::Error> {
        Ok(AssignOpStatement {
            lhs: visitor.visit_expression(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_expression(ctx, node.rhs.ast_ref())?,
            operator: visitor.visit_binary_operator(ctx, node.operator.ast_ref())?,
        })
    }

    pub struct BinaryExpression<V: AstVisitor> {
        pub lhs: V::ExpressionRet,
        pub rhs: V::ExpressionRet,
        pub operator: V::BinaryOperatorRet,
    }
    pub fn walk_binary_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BinaryExpression>,
    ) -> Result<BinaryExpression<V>, V::Error> {
        Ok(BinaryExpression {
            lhs: visitor.visit_expression(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_expression(ctx, node.rhs.ast_ref())?,
            operator: visitor.visit_binary_operator(ctx, node.operator.ast_ref())?,
        })
    }

    pub struct UnaryExpression<V: AstVisitor> {
        pub expr: V::ExpressionRet,
        pub operator: V::UnaryOperatorRet,
    }

    pub fn walk_unary_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::UnaryExpression>,
    ) -> Result<UnaryExpression<V>, V::Error> {
        Ok(UnaryExpression {
            expr: visitor.visit_expression(ctx, node.expr.ast_ref())?,
            operator: visitor.visit_unary_operator(ctx, node.operator.ast_ref())?,
        })
    }

    pub struct IndexExpr<V: AstVisitor> {
        pub subject: V::ExpressionRet,
        pub index_expr: V::ExpressionRet,
    }

    pub fn walk_index_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::IndexExpression>,
    ) -> Result<IndexExpr<V>, V::Error> {
        Ok(IndexExpr {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref())?,
            index_expr: visitor.visit_expression(ctx, node.index_expr.ast_ref())?,
        })
    }

    pub struct StructDefEntry<V: AstVisitor> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
        pub default: Option<V::ExpressionRet>,
    }
    pub fn walk_struct_def_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::StructDefEntry>,
    ) -> Result<StructDefEntry<V>, V::Error> {
        Ok(StructDefEntry {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            ty: node
                .ty
                .as_ref()
                .map(|t| visitor.visit_type(ctx, t.ast_ref()))
                .transpose()?,
            default: node
                .default
                .as_ref()
                .map(|d| visitor.visit_expression(ctx, d.ast_ref()))
                .transpose()?,
        })
    }

    pub struct StructDef<V: AstVisitor> {
        pub entries: V::CollectionContainer<V::StructDefEntryRet>,
    }
    pub fn walk_struct_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<StructDef<V>, V::Error> {
        Ok(StructDef {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter()
                    .map(|b| visitor.visit_struct_def_entry(ctx, b.ast_ref())),
            )?,
        })
    }

    pub struct EnumDefEntry<V: AstVisitor> {
        pub name: V::NameRet,
        pub args: V::CollectionContainer<V::TypeRet>,
    }
    pub fn walk_enum_def_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::EnumDefEntry>,
    ) -> Result<EnumDefEntry<V>, V::Error> {
        Ok(EnumDefEntry {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter()
                    .map(|b| visitor.visit_type(ctx, b.ast_ref())),
            )?,
        })
    }

    pub struct EnumDef<V: AstVisitor> {
        pub entries: V::CollectionContainer<V::EnumDefEntryRet>,
    }
    pub fn walk_enum_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<EnumDef<V>, V::Error> {
        Ok(EnumDef {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter()
                    .map(|b| visitor.visit_enum_def_entry(ctx, b.ast_ref())),
            )?,
        })
    }

    pub struct TypeFunctionDef<V: AstVisitor> {
        pub args: V::CollectionContainer<V::TypeFunctionDefArgRet>,
        pub return_ty: Option<V::TypeRet>,
        pub expression: V::ExpressionRet,
    }

    pub fn walk_type_function_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDef>,
    ) -> Result<TypeFunctionDef<V>, V::Error> {
        Ok(TypeFunctionDef {
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter()
                    .map(|t| visitor.visit_type_function_def_arg(ctx, t.ast_ref())),
            )?,
            return_ty: node
                .return_ty
                .as_ref()
                .map(|t| visitor.visit_type(ctx, t.ast_ref()))
                .transpose()?,
            expression: visitor.visit_expression(ctx, node.expr.ast_ref())?,
        })
    }

    pub struct TypeFunctionDefArg<V: AstVisitor> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
    }

    pub fn walk_type_function_def_arg<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDefArg>,
    ) -> Result<TypeFunctionDefArg<V>, V::Error> {
        Ok(TypeFunctionDefArg {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            ty: node
                .ty
                .as_ref()
                .map(|inner| visitor.visit_type(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct TraitDef<V: AstVisitor> {
        pub members: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_trait_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<TraitDef<V>, V::Error> {
        Ok(TraitDef {
            members: V::try_collect_items(
                ctx,
                node.members
                    .iter()
                    .map(|t| visitor.visit_expression(ctx, t.ast_ref())),
            )?,
        })
    }

    pub struct TraitImpl<V: AstVisitor> {
        pub ty: V::TypeRet,
        pub implementation: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_trait_impl<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TraitImpl>,
    ) -> Result<TraitImpl<V>, V::Error> {
        Ok(TraitImpl {
            ty: visitor.visit_type(ctx, node.ty.ast_ref())?,
            implementation: V::try_collect_items(
                ctx,
                node.implementation
                    .iter()
                    .map(|t| visitor.visit_expression(ctx, t.ast_ref())),
            )?,
        })
    }

    pub struct Module<V: AstVisitor> {
        pub contents: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_module<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Module<V>, V::Error> {
        Ok(Module {
            contents: V::try_collect_items(
                ctx,
                node.contents
                    .iter()
                    .map(|s| visitor.visit_expression(ctx, s.ast_ref())),
            )?,
        })
    }
}

pub mod walk_mut {
    use crate::ast::AstNodeRefMut;

    use super::{ast, AstVisitorMut};

    pub struct FunctionDefArg<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
        pub default: Option<V::ExpressionRet>,
    }

    pub fn walk_function_def_arg<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::FunctionDefArg>,
    ) -> Result<FunctionDefArg<V>, V::Error> {
        Ok(FunctionDefArg {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            ty: node
                .ty
                .as_mut()
                .map(|t| visitor.visit_type(ctx, t.ast_ref_mut()))
                .transpose()?,
            default: node
                .default
                .as_mut()
                .map(|t| visitor.visit_expression(ctx, t.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct FunctionDef<V: AstVisitorMut> {
        pub args: V::CollectionContainer<V::FunctionDefArgRet>,
        pub return_ty: Option<V::TypeRet>,
        pub fn_body: V::ExpressionRet,
    }

    pub fn walk_function_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::FunctionDef>,
    ) -> Result<FunctionDef<V>, V::Error> {
        Ok(FunctionDef {
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter_mut()
                    .map(|a| visitor.visit_function_def_arg(ctx, a.ast_ref_mut())),
            )?,
            return_ty: node
                .return_ty
                .as_mut()
                .map(|t| visitor.visit_type(ctx, t.ast_ref_mut()))
                .transpose()?,
            fn_body: visitor.visit_expression(ctx, node.fn_body.ast_ref_mut())?,
        })
    }

    pub enum Expression<V: AstVisitorMut> {
        FunctionCall(V::ConstructorCallExprRet),
        Directive(V::DirectiveExprRet),
        Declaration(V::DeclarationRet),
        Variable(V::VariableExprRet),
        PropertyAccess(V::PropertyAccessExprRet),
        Ref(V::RefExprRet),
        Deref(V::DerefExprRet),
        Unsafe(V::UnsafeExprRet),
        LiteralExpr(V::LiteralExprRet),
        Typed(V::CastExprRet),
        Block(V::BlockExprRet),
        Import(V::ImportExprRet),
        StructDef(V::StructDefRet),
        EnumDef(V::EnumDefRet),
        TypeFunctionDef(V::TypeFunctionDefRet),
        TraitDef(V::TraitDefRet),
        FunctionDef(V::FunctionDefRet),
        Type(V::TypeExprRet),
        Return(V::ReturnStatementRet),
        Break(V::BreakStatementRet),
        Continue(V::ContinueStatementRet),
        Assign(V::AssignExpressionRet),
        AssignOp(V::AssignOpExpressionRet),
        MergeDeclaration(V::MergeDeclarationRet),
        TraitImpl(V::TraitImplRet),
        BinaryExpr(V::BinaryExpressionRet),
        UnaryExpr(V::UnaryExpressionRet),
        Index(V::IndexExpressionRet),
    }

    pub fn walk_expression<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Expression>,
    ) -> Result<Expression<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut node.kind {
            ast::ExpressionKind::ConstructorCall(inner) => Expression::FunctionCall(
                visitor.visit_constructor_call_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::Type(inner) => {
                Expression::Type(visitor.visit_type_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExpressionKind::Directive(inner) => Expression::Directive(
                visitor.visit_directive_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::Declaration(inner) => Expression::Declaration(
                visitor.visit_declaration(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::MergeDeclaration(inner) => Expression::MergeDeclaration(
                visitor.visit_merge_declaration(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::Variable(inner) => Expression::Variable(
                visitor.visit_variable_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::PropertyAccess(inner) => Expression::PropertyAccess({
                visitor.visit_property_access_expr(ctx, AstNodeRefMut::new(inner, span, id))?
            }),
            ast::ExpressionKind::Ref(inner) => {
                Expression::Ref(visitor.visit_ref_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExpressionKind::Deref(inner) => Expression::Deref(
                visitor.visit_deref_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::Unsafe(inner) => Expression::Unsafe(
                visitor.visit_unsafe_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::LiteralExpr(inner) => Expression::LiteralExpr(
                visitor.visit_literal_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::As(inner) => Expression::Typed(
                visitor.visit_cast_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::Block(inner) => Expression::Block(
                visitor.visit_block_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::Import(inner) => Expression::Import(
                visitor.visit_import_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExpressionKind::StructDef(r) => Expression::StructDef(
                visitor.visit_struct_def(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::EnumDef(r) => {
                Expression::EnumDef(visitor.visit_enum_def(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExpressionKind::TypeFunctionDef(r) => Expression::TypeFunctionDef(
                visitor.visit_type_function_def(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::TraitDef(r) => {
                Expression::TraitDef(visitor.visit_trait_def(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExpressionKind::FunctionDef(r) => Expression::FunctionDef(
                visitor.visit_function_def(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::Return(r) => Expression::Return(
                visitor.visit_return_statement(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::Break(r) => Expression::Break(
                visitor.visit_break_statement(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::Continue(r) => Expression::Continue(
                visitor.visit_continue_statement(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::Assign(r) => {
                Expression::Assign(visitor.visit_assign_expr(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExpressionKind::AssignOp(r) => Expression::AssignOp(
                visitor.visit_assign_op_expr(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::TraitImpl(r) => Expression::TraitImpl(
                visitor.visit_trait_impl(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::BinaryExpr(r) => Expression::BinaryExpr(
                visitor.visit_binary_expr(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::UnaryExpr(r) => Expression::UnaryExpr(
                visitor.visit_unary_expr(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExpressionKind::Index(r) => {
                Expression::Index(visitor.visit_index_expr(ctx, AstNodeRefMut::new(r, span, id))?)
            }
        })
    }

    pub fn walk_expression_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Expression>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            ConstructorCallExprRet = Ret,
            DirectiveExprRet = Ret,
            DeclarationRet = Ret,
            MergeDeclarationRet = Ret,
            VariableExprRet = Ret,
            PropertyAccessExprRet = Ret,
            RefExprRet = Ret,
            DerefExprRet = Ret,
            UnsafeExprRet = Ret,
            LiteralExprRet = Ret,
            CastExprRet = Ret,
            BlockExprRet = Ret,
            ImportExprRet = Ret,
            StructDefRet = Ret,
            EnumDefRet = Ret,
            TypeFunctionDefRet = Ret,
            TraitDefRet = Ret,
            TraitImplRet = Ret,
            FunctionDefRet = Ret,
            TypeExprRet = Ret,
            ReturnStatementRet = Ret,
            BreakStatementRet = Ret,
            ContinueStatementRet = Ret,
            AssignExpressionRet = Ret,
            AssignOpExpressionRet = Ret,
            BinaryExpressionRet = Ret,
            UnaryExpressionRet = Ret,
            IndexExpressionRet = Ret,
        >,
    {
        Ok(match walk_expression(visitor, ctx, node)? {
            Expression::FunctionCall(r) => r,
            Expression::Directive(r) => r,
            Expression::Declaration(r) => r,
            Expression::MergeDeclaration(r) => r,
            Expression::Variable(r) => r,
            Expression::PropertyAccess(r) => r,
            Expression::Ref(r) => r,
            Expression::Deref(r) => r,
            Expression::Unsafe(r) => r,
            Expression::LiteralExpr(r) => r,
            Expression::Typed(r) => r,
            Expression::Block(r) => r,
            Expression::Import(r) => r,
            Expression::StructDef(r) => r,
            Expression::EnumDef(r) => r,
            Expression::TypeFunctionDef(r) => r,
            Expression::TraitDef(r) => r,
            Expression::TraitImpl(r) => r,
            Expression::FunctionDef(r) => r,
            Expression::Type(r) => r,
            Expression::Return(r) => r,
            Expression::Break(r) => r,
            Expression::Continue(r) => r,
            Expression::Assign(r) => r,
            Expression::AssignOp(r) => r,
            Expression::BinaryExpr(r) => r,
            Expression::UnaryExpr(r) => r,
            Expression::Index(r) => r,
        })
    }

    pub struct VariableExpr<V: AstVisitorMut> {
        pub name: V::AccessNameRet,
        pub type_args: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_variable_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::VariableExpr>,
    ) -> Result<VariableExpr<V>, V::Error> {
        Ok(VariableExpr {
            name: visitor.visit_access_name(ctx, node.name.ast_ref_mut())?,
            type_args: V::try_collect_items(
                ctx,
                node.type_args
                    .iter_mut()
                    .map(|t| visitor.visit_named_field_type(ctx, t.ast_ref_mut())),
            )?,
        })
    }

    pub struct DirectiveExpr<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub subject: V::ExpressionRet,
    }

    pub fn walk_directive_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::DirectiveExpr>,
    ) -> Result<DirectiveExpr<V>, V::Error> {
        Ok(DirectiveExpr {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            subject: visitor.visit_expression(ctx, node.subject.ast_ref_mut())?,
        })
    }

    pub struct ConstructorCallArg<V: AstVisitorMut> {
        pub name: Option<V::NameRet>,
        pub value: V::ExpressionRet,
    }

    pub fn walk_constructor_call_arg<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ConstructorCallArg>,
    ) -> Result<ConstructorCallArg<V>, V::Error> {
        Ok(ConstructorCallArg {
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
            value: visitor.visit_expression(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct ConstructorCallArgs<V: AstVisitorMut> {
        pub entries: V::CollectionContainer<V::ConstructorCallArgRet>,
    }

    pub fn walk_constructor_call_args<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ConstructorCallArgs>,
    ) -> Result<ConstructorCallArgs<V>, V::Error> {
        Ok(ConstructorCallArgs {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter_mut()
                    .map(|e| visitor.visit_constructor_call_arg(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct FunctionCallExpr<V: AstVisitorMut> {
        pub subject: V::ExpressionRet,
        pub args: V::ConstructorCallArgsRet,
    }

    pub fn walk_constructor_call_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ConstructorCallExpr>,
    ) -> Result<FunctionCallExpr<V>, V::Error> {
        Ok(FunctionCallExpr {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref_mut())?,
            args: visitor.visit_constructor_call_args(ctx, node.args.ast_ref_mut())?,
        })
    }

    pub struct PropertyAccessExpr<V: AstVisitorMut> {
        pub subject: V::ExpressionRet,
        pub property: V::NameRet,
    }

    pub fn walk_property_access_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::PropertyAccessExpr>,
    ) -> Result<PropertyAccessExpr<V>, V::Error> {
        Ok(PropertyAccessExpr {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref_mut())?,
            property: visitor.visit_name(ctx, node.property.ast_ref_mut())?,
        })
    }

    pub struct RefExpr<V: AstVisitorMut> {
        pub inner_expr: V::ExpressionRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::RefExpr>,
    ) -> Result<RefExpr<V>, V::Error> {
        Ok(RefExpr {
            inner_expr: visitor.visit_expression(ctx, node.inner_expr.ast_ref_mut())?,
            mutability: node
                .mutability
                .as_mut()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct DerefExpr<V: AstVisitorMut>(pub V::ExpressionRet);

    pub fn walk_deref_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::DerefExpr>,
    ) -> Result<DerefExpr<V>, V::Error> {
        Ok(DerefExpr(
            visitor.visit_expression(ctx, node.0.ast_ref_mut())?,
        ))
    }

    pub struct UnsafeExpr<V: AstVisitorMut>(pub V::ExpressionRet);

    pub fn walk_unsafe_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::UnsafeExpr>,
    ) -> Result<UnsafeExpr<V>, V::Error> {
        Ok(UnsafeExpr(
            visitor.visit_expression(ctx, node.0.ast_ref_mut())?,
        ))
    }

    pub struct LiteralExpr<V: AstVisitorMut>(pub V::LiteralRet);

    pub fn walk_literal_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::LiteralExpr>,
    ) -> Result<LiteralExpr<V>, V::Error> {
        Ok(LiteralExpr(
            visitor.visit_literal(ctx, node.0.ast_ref_mut())?,
        ))
    }

    pub struct AsExpr<V: AstVisitorMut> {
        pub ty: V::TypeRet,
        pub expr: V::ExpressionRet,
    }

    pub fn walk_cast_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::CastExpr>,
    ) -> Result<AsExpr<V>, V::Error> {
        Ok(AsExpr {
            ty: visitor.visit_type(ctx, node.ty.ast_ref_mut())?,
            expr: visitor.visit_expression(ctx, node.expr.ast_ref_mut())?,
        })
    }

    pub struct TypeExpr<V: AstVisitorMut>(pub V::TypeRet);

    pub fn walk_type_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TypeExpr>,
    ) -> Result<TypeExpr<V>, V::Error> {
        Ok(TypeExpr(visitor.visit_type(ctx, node.0.ast_ref_mut())?))
    }

    pub struct BlockExpr<V: AstVisitorMut>(pub V::BlockRet);

    pub fn walk_block_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::BlockExpr>,
    ) -> Result<BlockExpr<V>, V::Error> {
        Ok(BlockExpr(visitor.visit_block(ctx, node.0.ast_ref_mut())?))
    }

    pub struct ImportExpr<V: AstVisitorMut>(pub V::ImportRet);

    pub fn walk_import_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ImportExpr>,
    ) -> Result<ImportExpr<V>, V::Error> {
        Ok(ImportExpr(visitor.visit_import(ctx, node.0.ast_ref_mut())?))
    }

    pub enum Literal<V: AstVisitorMut> {
        Str(V::StrLiteralRet),
        Char(V::CharLiteralRet),
        Int(V::IntLiteralRet),
        Float(V::FloatLiteralRet),
        Bool(V::BoolLiteralRet),
        Set(V::SetLiteralRet),
        Map(V::MapLiteralRet),
        List(V::ListLiteralRet),
        Tuple(V::TupleLiteralRet),
    }

    pub fn walk_literal<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Literal>,
    ) -> Result<Literal<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut *node {
            ast::Literal::Str(r) => {
                Literal::Str(visitor.visit_str_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Literal::Char(r) => {
                Literal::Char(visitor.visit_char_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Literal::Int(r) => {
                Literal::Int(visitor.visit_int_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Literal::Float(r) => {
                Literal::Float(visitor.visit_float_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Literal::Bool(r) => {
                Literal::Bool(visitor.visit_bool_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Literal::Set(r) => {
                Literal::Set(visitor.visit_set_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Literal::Map(r) => {
                Literal::Map(visitor.visit_map_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Literal::List(r) => {
                Literal::List(visitor.visit_list_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Literal::Tuple(r) => {
                Literal::Tuple(visitor.visit_tuple_literal(ctx, AstNodeRefMut::new(r, span, id))?)
            }
        })
    }

    pub fn walk_literal_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Literal>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            StrLiteralRet = Ret,
            CharLiteralRet = Ret,
            IntLiteralRet = Ret,
            FloatLiteralRet = Ret,
            BoolLiteralRet = Ret,
            SetLiteralRet = Ret,
            MapLiteralRet = Ret,
            ListLiteralRet = Ret,
            TupleLiteralRet = Ret,
        >,
    {
        Ok(match walk_literal(visitor, ctx, node)? {
            Literal::Str(r) => r,
            Literal::Char(r) => r,
            Literal::Int(r) => r,
            Literal::Float(r) => r,
            Literal::Bool(r) => r,
            Literal::Set(r) => r,
            Literal::Map(r) => r,
            Literal::List(r) => r,
            Literal::Tuple(r) => r,
        })
    }

    pub struct MatchCase<V: AstVisitorMut> {
        pub pattern: V::PatternRet,
        pub expr: V::ExpressionRet,
    }

    pub fn walk_match_case<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MatchCase>,
    ) -> Result<MatchCase<V>, V::Error> {
        Ok(MatchCase {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref_mut())?,
            expr: visitor.visit_expression(ctx, node.expr.ast_ref_mut())?,
        })
    }

    pub struct MatchBlock<V: AstVisitorMut> {
        pub subject: V::ExpressionRet,
        pub cases: V::CollectionContainer<V::MatchCaseRet>,
    }

    pub fn walk_match_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MatchBlock>,
    ) -> Result<MatchBlock<V>, V::Error> {
        Ok(MatchBlock {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref_mut())?,
            cases: V::try_collect_items(
                ctx,
                node.cases
                    .iter_mut()
                    .map(|c| visitor.visit_match_case(ctx, c.ast_ref_mut())),
            )?,
        })
    }

    pub struct LoopBlock<V: AstVisitorMut>(pub V::BlockRet);

    pub fn walk_loop_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::LoopBlock>,
    ) -> Result<LoopBlock<V>, V::Error> {
        Ok(LoopBlock(visitor.visit_block(ctx, node.0.ast_ref_mut())?))
    }

    pub struct ForLoopBlock<V: AstVisitorMut> {
        pub pattern: V::PatternRet,
        pub iterator: V::ExpressionRet,
        pub body: V::BlockRet,
    }

    pub fn walk_for_loop_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ForLoopBlock>,
    ) -> Result<ForLoopBlock<V>, V::Error> {
        Ok(ForLoopBlock {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref_mut())?,
            iterator: visitor.visit_expression(ctx, node.iterator.ast_ref_mut())?,
            body: visitor.visit_block(ctx, node.body.ast_ref_mut())?,
        })
    }

    pub struct WhileLoopBlock<V: AstVisitorMut> {
        pub condition: V::ExpressionRet,
        pub body: V::BlockRet,
    }

    pub fn walk_while_loop_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::WhileLoopBlock>,
    ) -> Result<WhileLoopBlock<V>, V::Error> {
        Ok(WhileLoopBlock {
            condition: visitor.visit_expression(ctx, node.condition.ast_ref_mut())?,
            body: visitor.visit_block(ctx, node.body.ast_ref_mut())?,
        })
    }

    pub struct ModBlock<V: AstVisitorMut>(pub V::BodyBlockRet);

    pub fn walk_mod_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ModBlock>,
    ) -> Result<ModBlock<V>, V::Error> {
        Ok(ModBlock(
            visitor.visit_body_block(ctx, node.0.ast_ref_mut())?,
        ))
    }

    pub struct ImplBlock<V: AstVisitorMut>(pub V::BodyBlockRet);

    pub fn walk_impl_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ImplBlock>,
    ) -> Result<ImplBlock<V>, V::Error> {
        Ok(ImplBlock(
            visitor.visit_body_block(ctx, node.0.ast_ref_mut())?,
        ))
    }

    pub struct IfClause<V: AstVisitorMut> {
        pub condition: V::ExpressionRet,
        pub body: V::BlockRet,
    }

    pub fn walk_if_clause<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::IfClause>,
    ) -> Result<IfClause<V>, V::Error> {
        Ok(IfClause {
            condition: visitor.visit_expression(ctx, node.condition.ast_ref_mut())?,
            body: visitor.visit_block(ctx, node.body.ast_ref_mut())?,
        })
    }

    pub struct IfBlock<V: AstVisitorMut> {
        pub clauses: V::CollectionContainer<V::IfClauseRet>,
        pub otherwise: Option<V::BlockRet>,
    }

    pub fn walk_if_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::IfBlock>,
    ) -> Result<IfBlock<V>, V::Error> {
        Ok(IfBlock {
            clauses: V::try_collect_items(
                ctx,
                node.clauses
                    .iter_mut()
                    .map(|clause| visitor.visit_if_clause(ctx, clause.ast_ref_mut())),
            )?,
            otherwise: node
                .otherwise
                .as_mut()
                .map(|body| visitor.visit_block(ctx, body.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct BodyBlock<V: AstVisitorMut> {
        pub statements: V::CollectionContainer<V::ExpressionRet>,
        pub expr: Option<V::ExpressionRet>,
    }

    pub fn walk_body_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::BodyBlock>,
    ) -> Result<BodyBlock<V>, V::Error> {
        Ok(BodyBlock {
            statements: V::try_collect_items(
                ctx,
                node.statements
                    .iter_mut()
                    .map(|s| visitor.visit_expression(ctx, s.ast_ref_mut())),
            )?,
            expr: node
                .expr
                .as_mut()
                .map(|e| visitor.visit_expression(ctx, e.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub enum Block<V: AstVisitorMut> {
        Match(V::MatchBlockRet),
        Loop(V::LoopBlockRet),
        For(V::ForLoopBlockRet),
        While(V::WhileLoopBlockRet),
        Mod(V::ModBlockRet),
        Body(V::BodyBlockRet),
        Impl(V::ImplBlockRet),
        If(V::IfBlockRet),
    }

    pub fn walk_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Block>,
    ) -> Result<Block<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut *node {
            ast::Block::Match(r) => {
                Block::Match(visitor.visit_match_block(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Block::Loop(r) => {
                Block::Loop(visitor.visit_loop_block(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Block::For(r) => {
                Block::For(visitor.visit_for_loop_block(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Block::While(r) => {
                Block::While(visitor.visit_while_loop_block(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Block::Mod(r) => {
                Block::Mod(visitor.visit_mod_block(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Block::Body(r) => {
                Block::Body(visitor.visit_body_block(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Block::Impl(r) => {
                Block::Impl(visitor.visit_impl_block(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Block::If(r) => {
                Block::If(visitor.visit_if_block(ctx, AstNodeRefMut::new(r, span, id))?)
            }
        })
    }

    pub fn walk_block_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Block>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            MatchBlockRet = Ret,
            LoopBlockRet = Ret,
            ForLoopBlockRet = Ret,
            WhileLoopBlockRet = Ret,
            ModBlockRet = Ret,
            BodyBlockRet = Ret,
            IfBlockRet = Ret,
            ImplBlockRet = Ret,
        >,
    {
        Ok(match walk_block(visitor, ctx, node)? {
            Block::Match(r) => r,
            Block::Loop(r) => r,
            Block::For(r) => r,
            Block::If(r) => r,
            Block::While(r) => r,
            Block::Mod(r) => r,
            Block::Body(r) => r,
            Block::Impl(r) => r,
        })
    }

    pub struct SetLiteral<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_set_literal<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::SetLiteral>,
    ) -> Result<SetLiteral<V>, V::Error> {
        Ok(SetLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter_mut()
                    .map(|e| visitor.visit_expression(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct MapLiteralEntry<V: AstVisitorMut> {
        pub key: V::ExpressionRet,
        pub value: V::ExpressionRet,
    }

    pub fn walk_map_literal_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MapLiteralEntry>,
    ) -> Result<MapLiteralEntry<V>, V::Error> {
        Ok(MapLiteralEntry {
            key: visitor.visit_expression(ctx, node.key.ast_ref_mut())?,
            value: visitor.visit_expression(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct MapLiteral<V: AstVisitorMut> {
        pub entries: V::CollectionContainer<V::MapLiteralEntryRet>,
    }

    pub fn walk_map_literal<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MapLiteral>,
    ) -> Result<MapLiteral<V>, V::Error> {
        Ok(MapLiteral {
            entries: V::try_collect_items(
                ctx,
                node.elements
                    .iter_mut()
                    .map(|e| visitor.visit_map_literal_entry(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct ListLiteral<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_list_literal<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ListLiteral>,
    ) -> Result<ListLiteral<V>, V::Error> {
        Ok(ListLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter_mut()
                    .map(|e| visitor.visit_expression(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct TupleLiteralEntry<V: AstVisitorMut> {
        pub name: Option<V::NameRet>,
        pub ty: Option<V::TypeRet>,
        pub value: V::ExpressionRet,
    }

    pub fn walk_tuple_literal_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TupleLiteralEntry>,
    ) -> Result<TupleLiteralEntry<V>, V::Error> {
        Ok(TupleLiteralEntry {
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
            ty: node
                .ty
                .as_mut()
                .map(|t| visitor.visit_type(ctx, t.ast_ref_mut()))
                .transpose()?,
            value: visitor.visit_expression(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct TupleLiteral<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::TupleLiteralEntryRet>,
    }

    pub fn walk_tuple_literal<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TupleLiteral>,
    ) -> Result<TupleLiteral<V>, V::Error> {
        Ok(TupleLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter_mut()
                    .map(|e| visitor.visit_tuple_literal_entry(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct NamedFieldTypeEntry<V: AstVisitorMut> {
        pub ty: V::TypeRet,
        pub name: Option<V::NameRet>,
    }

    pub fn walk_named_field_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::NamedFieldTypeEntry>,
    ) -> Result<NamedFieldTypeEntry<V>, V::Error> {
        Ok(NamedFieldTypeEntry {
            ty: visitor.visit_type(ctx, node.ty.ast_ref_mut())?,
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct FnType<V: AstVisitorMut> {
        pub args: V::CollectionContainer<V::NamedFieldTypeRet>,
        pub return_ty: V::TypeRet,
    }

    pub fn walk_function_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::FnType>,
    ) -> Result<FnType<V>, V::Error> {
        Ok(FnType {
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter_mut()
                    .map(|e| visitor.visit_named_field_type(ctx, e.ast_ref_mut())),
            )?,
            return_ty: visitor.visit_type(ctx, node.return_ty.ast_ref_mut())?,
        })
    }

    pub struct TupleType<V: AstVisitorMut> {
        pub entries: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_tuple_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TupleType>,
    ) -> Result<TupleType<V>, V::Error> {
        Ok(TupleType {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter_mut()
                    .map(|e| visitor.visit_named_field_type(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct ListType<V: AstVisitorMut> {
        pub inner: V::TypeRet,
    }

    pub fn walk_list_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ListType>,
    ) -> Result<ListType<V>, V::Error> {
        Ok(ListType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref_mut())?,
        })
    }

    pub struct SetType<V: AstVisitorMut> {
        pub inner: V::TypeRet,
    }

    pub fn walk_set_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::SetType>,
    ) -> Result<SetType<V>, V::Error> {
        Ok(SetType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref_mut())?,
        })
    }

    pub struct MapType<V: AstVisitorMut> {
        pub key: V::TypeRet,
        pub value: V::TypeRet,
    }

    pub fn walk_map_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MapType>,
    ) -> Result<MapType<V>, V::Error> {
        Ok(MapType {
            key: visitor.visit_type(ctx, node.key.ast_ref_mut())?,
            value: visitor.visit_type(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct NamedType<V: AstVisitorMut> {
        pub name: V::AccessNameRet,
    }

    pub fn walk_named_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::NamedType>,
    ) -> Result<NamedType<V>, V::Error> {
        Ok(NamedType {
            name: visitor.visit_access_name(ctx, node.name.ast_ref_mut())?,
        })
    }

    pub struct RefType<V: AstVisitorMut> {
        pub inner: V::TypeRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::RefType>,
    ) -> Result<RefType<V>, V::Error> {
        Ok(RefType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref_mut())?,
            mutability: node
                .mutability
                .as_mut()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct MergedType<V: AstVisitorMut>(pub V::CollectionContainer<V::TypeRet>);

    pub fn walk_merged_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MergedType>,
    ) -> Result<MergedType<V>, V::Error> {
        Ok(MergedType(V::try_collect_items(
            ctx,
            node.0
                .iter_mut()
                .map(|a| visitor.visit_type(ctx, a.ast_ref_mut())),
        )?))
    }

    pub struct TypeFunctionCall<V: AstVisitorMut> {
        pub subject: V::TypeRet,
        pub args: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_type_function_call<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TypeFunctionCall>,
    ) -> Result<TypeFunctionCall<V>, V::Error> {
        Ok(TypeFunctionCall {
            subject: visitor.visit_type(ctx, node.subject.ast_ref_mut())?,
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter_mut()
                    .map(|a| visitor.visit_named_field_type(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct TypeFunctionParam<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub bound: Option<V::TypeRet>,
        pub default: Option<V::TypeRet>,
    }

    pub fn walk_type_function_param<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TypeFunctionParam>,
    ) -> Result<TypeFunctionParam<V>, V::Error> {
        Ok(TypeFunctionParam {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            bound: node
                .bound
                .as_mut()
                .map(|bound| visitor.visit_type(ctx, bound.ast_ref_mut()))
                .transpose()?,
            default: node
                .default
                .as_mut()
                .map(|default| visitor.visit_type(ctx, default.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct TypeFunction<V: AstVisitorMut> {
        pub args: V::CollectionContainer<V::TypeFunctionParamRet>,
        pub return_ty: V::TypeRet,
    }

    pub fn walk_type_function<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TypeFunction>,
    ) -> Result<TypeFunction<V>, V::Error> {
        Ok(TypeFunction {
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter_mut()
                    .map(|a| visitor.visit_type_function_param(ctx, a.ast_ref_mut())),
            )?,
            return_ty: visitor.visit_type(ctx, node.return_ty.ast_ref_mut())?,
        })
    }

    pub enum Type<V: AstVisitorMut> {
        Fn(V::FnTypeRet),
        Tuple(V::TupleTypeRet),
        List(V::ListTypeRet),
        Set(V::SetTypeRet),
        Map(V::MapTypeRet),
        Named(V::NamedTypeRet),
        Ref(V::RefTypeRet),
        Merged(V::MergedTypeRet),
        TypeFunction(V::TypeFunctionRet),
        TypeFunctionCall(V::TypeFunctionCallRet),
    }

    pub fn walk_type<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Type>,
    ) -> Result<Type<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut *node {
            ast::Type::Fn(r) => {
                Type::Fn(visitor.visit_function_type(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Type::Tuple(r) => {
                Type::Tuple(visitor.visit_tuple_type(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Type::List(r) => {
                Type::List(visitor.visit_list_type(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Type::Set(r) => {
                Type::Set(visitor.visit_set_type(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Type::Map(r) => {
                Type::Map(visitor.visit_map_type(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Type::Named(r) => {
                Type::Named(visitor.visit_named_type(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Type::Ref(r) => {
                Type::Ref(visitor.visit_ref_type(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Type::Merged(r) => {
                Type::Merged(visitor.visit_merged_type(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Type::TypeFunction(r) => Type::TypeFunction(
                visitor.visit_type_function(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::Type::TypeFunctionCall(r) => Type::TypeFunctionCall(
                visitor.visit_type_function_call(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
        })
    }

    pub fn walk_type_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Type>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            FnTypeRet = Ret,
            TupleTypeRet = Ret,
            ListTypeRet = Ret,
            SetTypeRet = Ret,
            MapTypeRet = Ret,
            NamedTypeRet = Ret,
            RefTypeRet = Ret,
            MergedTypeRet = Ret,
            TypeFunctionRet = Ret,
            TypeFunctionCallRet = Ret,
        >,
    {
        Ok(match walk_type(visitor, ctx, node)? {
            Type::Fn(r) => r,
            Type::Tuple(r) => r,
            Type::List(r) => r,
            Type::Set(r) => r,
            Type::Map(r) => r,
            Type::Named(r) => r,
            Type::Ref(r) => r,
            Type::Merged(r) => r,
            Type::TypeFunction(r) => r,
            Type::TypeFunctionCall(r) => r,
        })
    }

    pub enum Pattern<V: AstVisitorMut> {
        Constructor(V::ConstructorPatternRet),
        Namespace(V::NamespacePatternRet),
        Tuple(V::TuplePatternRet),
        List(V::ListPatternRet),
        Literal(V::LiteralPatternRet),
        Or(V::OrPatternRet),
        If(V::IfPatternRet),
        Binding(V::BindingPatternRet),
        Spread(V::SpreadPatternRet),
        Ignore(V::IgnorePatternRet),
    }

    pub fn walk_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Pattern>,
    ) -> Result<Pattern<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut *node {
            ast::Pattern::Constructor(r) => Pattern::Constructor(
                visitor.visit_constructor_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::Pattern::Namespace(r) => Pattern::Namespace(
                visitor.visit_namespace_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::Pattern::Tuple(r) => {
                Pattern::Tuple(visitor.visit_tuple_pattern(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pattern::List(r) => {
                Pattern::List(visitor.visit_list_pattern(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pattern::Literal(r) => Pattern::Literal(
                visitor.visit_literal_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::Pattern::Or(r) => {
                Pattern::Or(visitor.visit_or_pattern(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pattern::If(r) => {
                Pattern::If(visitor.visit_if_pattern(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pattern::Binding(r) => Pattern::Binding(
                visitor.visit_binding_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::Pattern::Spread(r) => {
                Pattern::Spread(visitor.visit_spread_pattern(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pattern::Ignore(r) => {
                Pattern::Ignore(visitor.visit_ignore_pattern(ctx, AstNodeRefMut::new(r, span, id))?)
            }
        })
    }

    pub fn walk_pattern_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Pattern>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            ConstructorPatternRet = Ret,
            NamespacePatternRet = Ret,
            TuplePatternRet = Ret,
            ListPatternRet = Ret,
            LiteralPatternRet = Ret,
            OrPatternRet = Ret,
            IfPatternRet = Ret,
            BindingPatternRet = Ret,
            SpreadPatternRet = Ret,
            IgnorePatternRet = Ret,
        >,
    {
        Ok(match walk_pattern(visitor, ctx, node)? {
            Pattern::Constructor(r) => r,
            Pattern::Namespace(r) => r,
            Pattern::Tuple(r) => r,
            Pattern::List(r) => r,
            Pattern::Literal(r) => r,
            Pattern::Or(r) => r,
            Pattern::If(r) => r,
            Pattern::Binding(r) => r,
            Pattern::Spread(r) => r,
            Pattern::Ignore(r) => r,
        })
    }

    pub struct OrPattern<V: AstVisitorMut> {
        pub variants: V::CollectionContainer<V::PatternRet>,
    }
    pub fn walk_or_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::OrPattern>,
    ) -> Result<OrPattern<V>, V::Error> {
        Ok(OrPattern {
            variants: V::try_collect_items(
                ctx,
                node.variants
                    .iter_mut()
                    .map(|v| visitor.visit_pattern(ctx, v.ast_ref_mut())),
            )?,
        })
    }

    pub struct ConstructorPattern<V: AstVisitorMut> {
        pub name: V::AccessNameRet,
        pub args: V::CollectionContainer<V::TuplePatternEntryRet>,
    }
    pub fn walk_constructor_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ConstructorPattern>,
    ) -> Result<ConstructorPattern<V>, V::Error> {
        Ok(ConstructorPattern {
            name: visitor.visit_access_name(ctx, node.name.ast_ref_mut())?,
            args: V::try_collect_items(
                ctx,
                node.fields
                    .iter_mut()
                    .map(|a| visitor.visit_tuple_pattern_entry(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct NamespacePattern<V: AstVisitorMut> {
        pub patterns: V::CollectionContainer<V::DestructuringPatternRet>,
    }
    pub fn walk_namespace_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::NamespacePattern>,
    ) -> Result<NamespacePattern<V>, V::Error> {
        Ok(NamespacePattern {
            patterns: V::try_collect_items(
                ctx,
                node.fields
                    .iter_mut()
                    .map(|a| visitor.visit_destructuring_pattern(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct TuplePatternEntry<V: AstVisitorMut> {
        pub name: Option<V::NameRet>,
        pub pattern: V::PatternRet,
    }

    pub fn walk_tuple_pattern_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TuplePatternEntry>,
    ) -> Result<TuplePatternEntry<V>, V::Error> {
        Ok(TuplePatternEntry {
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref_mut())?,
        })
    }

    pub struct TuplePattern<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::TuplePatternEntryRet>,
    }

    pub fn walk_tuple_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TuplePattern>,
    ) -> Result<TuplePattern<V>, V::Error> {
        Ok(TuplePattern {
            elements: V::try_collect_items(
                ctx,
                node.fields
                    .iter_mut()
                    .map(|a| visitor.visit_tuple_pattern_entry(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct ListPattern<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::PatternRet>,
    }

    pub fn walk_list_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ListPattern>,
    ) -> Result<ListPattern<V>, V::Error> {
        Ok(ListPattern {
            elements: V::try_collect_items(
                ctx,
                node.fields
                    .iter_mut()
                    .map(|a| visitor.visit_pattern(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct IfPattern<V: AstVisitorMut> {
        pub pattern: V::PatternRet,
        pub condition: V::ExpressionRet,
    }
    pub fn walk_if_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::IfPattern>,
    ) -> Result<IfPattern<V>, V::Error> {
        Ok(IfPattern {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref_mut())?,
            condition: visitor.visit_expression(ctx, node.condition.ast_ref_mut())?,
        })
    }

    pub struct BindingPattern<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub visibility: Option<V::VisibilityRet>,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_binding_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::BindingPattern>,
    ) -> Result<BindingPattern<V>, V::Error> {
        Ok(BindingPattern {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            visibility: node
                .visibility
                .as_mut()
                .map(|inner| visitor.visit_visibility_modifier(ctx, inner.ast_ref_mut()))
                .transpose()?,

            mutability: node
                .mutability
                .as_mut()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct SpreadPattern<V: AstVisitorMut> {
        pub name: Option<V::NameRet>,
    }

    pub fn walk_spread_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::SpreadPattern>,
    ) -> Result<SpreadPattern<V>, V::Error> {
        Ok(SpreadPattern {
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub enum LiteralPattern<V: AstVisitorMut> {
        Str(V::StrLiteralPatternRet),
        Char(V::CharLiteralPatternRet),
        Int(V::IntLiteralPatternRet),
        Float(V::FloatLiteralPatternRet),
        Bool(V::BoolLiteralPatternRet),
    }

    pub fn walk_literal_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::LiteralPattern>,
    ) -> Result<LiteralPattern<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut *node {
            ast::LiteralPattern::Str(r) => LiteralPattern::Str(
                visitor.visit_str_literal_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::LiteralPattern::Char(r) => LiteralPattern::Char(
                visitor.visit_char_literal_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::LiteralPattern::Int(r) => LiteralPattern::Int(
                visitor.visit_int_literal_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::LiteralPattern::Float(r) => LiteralPattern::Float(
                visitor.visit_float_literal_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::LiteralPattern::Bool(r) => LiteralPattern::Bool(
                visitor.visit_bool_literal_pattern(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
        })
    }

    pub fn walk_literal_pattern_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::LiteralPattern>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            StrLiteralPatternRet = Ret,
            CharLiteralPatternRet = Ret,
            IntLiteralPatternRet = Ret,
            FloatLiteralPatternRet = Ret,
            BoolLiteralPatternRet = Ret,
        >,
    {
        Ok(match walk_literal_pattern(visitor, ctx, node)? {
            LiteralPattern::Str(r) => r,
            LiteralPattern::Char(r) => r,
            LiteralPattern::Int(r) => r,
            LiteralPattern::Float(r) => r,
            LiteralPattern::Bool(r) => r,
        })
    }

    pub struct DestructuringPattern<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub pattern: V::PatternRet,
    }
    pub fn walk_destructuring_pattern<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::DestructuringPattern>,
    ) -> Result<DestructuringPattern<V>, V::Error> {
        Ok(DestructuringPattern {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref_mut())?,
        })
    }

    pub struct ReturnStatement<V: AstVisitorMut>(pub Option<V::ExpressionRet>);
    pub fn walk_return_statement<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ReturnStatement>,
    ) -> Result<ReturnStatement<V>, V::Error> {
        Ok(ReturnStatement(
            node.0
                .as_mut()
                .map(|n| visitor.visit_expression(ctx, n.ast_ref_mut()))
                .transpose()?,
        ))
    }

    pub struct Declaration<V: AstVisitorMut> {
        pub pattern: V::PatternRet,
        pub ty: Option<V::TypeRet>,
        pub value: Option<V::ExpressionRet>,
    }

    pub fn walk_declaration<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Declaration>,
    ) -> Result<Declaration<V>, V::Error> {
        Ok(Declaration {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref_mut())?,
            ty: node
                .ty
                .as_mut()
                .map(|t| visitor.visit_type(ctx, t.ast_ref_mut()))
                .transpose()?,
            value: node
                .value
                .as_mut()
                .map(|t| visitor.visit_expression(ctx, t.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct MergeDeclaration<V: AstVisitorMut> {
        pub decl: V::ExpressionRet,
        pub value: V::ExpressionRet,
    }

    pub fn walk_merge_declaration<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MergeDeclaration>,
    ) -> Result<MergeDeclaration<V>, V::Error> {
        Ok(MergeDeclaration {
            decl: visitor.visit_expression(ctx, node.decl.ast_ref_mut())?,
            value: visitor.visit_expression(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct AssignStatement<V: AstVisitorMut> {
        pub lhs: V::ExpressionRet,
        pub rhs: V::ExpressionRet,
    }

    pub fn walk_assign_statement<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::AssignExpression>,
    ) -> Result<AssignStatement<V>, V::Error> {
        Ok(AssignStatement {
            lhs: visitor.visit_expression(ctx, node.lhs.ast_ref_mut())?,
            rhs: visitor.visit_expression(ctx, node.rhs.ast_ref_mut())?,
        })
    }

    pub struct AssignOpStatement<V: AstVisitorMut> {
        pub lhs: V::ExpressionRet,
        pub rhs: V::ExpressionRet,
        pub operator: V::BinaryOperatorRet,
    }
    pub fn walk_assign_op_statement<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::AssignOpExpression>,
    ) -> Result<AssignOpStatement<V>, V::Error> {
        Ok(AssignOpStatement {
            lhs: visitor.visit_expression(ctx, node.lhs.ast_ref_mut())?,
            rhs: visitor.visit_expression(ctx, node.rhs.ast_ref_mut())?,
            operator: visitor.visit_binary_operator(ctx, node.operator.ast_ref_mut())?,
        })
    }

    pub struct BinaryExpression<V: AstVisitorMut> {
        pub lhs: V::ExpressionRet,
        pub rhs: V::ExpressionRet,
        pub operator: V::BinaryOperatorRet,
    }
    pub fn walk_binary_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::BinaryExpression>,
    ) -> Result<BinaryExpression<V>, V::Error> {
        Ok(BinaryExpression {
            lhs: visitor.visit_expression(ctx, node.lhs.ast_ref_mut())?,
            rhs: visitor.visit_expression(ctx, node.rhs.ast_ref_mut())?,
            operator: visitor.visit_binary_operator(ctx, node.operator.ast_ref_mut())?,
        })
    }

    pub struct UnaryExpression<V: AstVisitorMut> {
        pub expr: V::ExpressionRet,
        pub operator: V::UnaryOperatorRet,
    }

    pub fn walk_unary_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::UnaryExpression>,
    ) -> Result<UnaryExpression<V>, V::Error> {
        Ok(UnaryExpression {
            expr: visitor.visit_expression(ctx, node.expr.ast_ref_mut())?,
            operator: visitor.visit_unary_operator(ctx, node.operator.ast_ref_mut())?,
        })
    }

    pub struct IndexExpr<V: AstVisitorMut> {
        pub subject: V::ExpressionRet,
        pub index_expr: V::ExpressionRet,
    }

    pub fn walk_index_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::IndexExpression>,
    ) -> Result<IndexExpr<V>, V::Error> {
        Ok(IndexExpr {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref_mut())?,
            index_expr: visitor.visit_expression(ctx, node.index_expr.ast_ref_mut())?,
        })
    }

    pub struct StructDefEntry<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
        pub default: Option<V::ExpressionRet>,
    }
    pub fn walk_struct_def_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::StructDefEntry>,
    ) -> Result<StructDefEntry<V>, V::Error> {
        Ok(StructDefEntry {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            ty: node
                .ty
                .as_mut()
                .map(|t| visitor.visit_type(ctx, t.ast_ref_mut()))
                .transpose()?,
            default: node
                .default
                .as_mut()
                .map(|d| visitor.visit_expression(ctx, d.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct StructDef<V: AstVisitorMut> {
        pub entries: V::CollectionContainer<V::StructDefEntryRet>,
    }
    pub fn walk_struct_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::StructDef>,
    ) -> Result<StructDef<V>, V::Error> {
        Ok(StructDef {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter_mut()
                    .map(|b| visitor.visit_struct_def_entry(ctx, b.ast_ref_mut())),
            )?,
        })
    }

    pub struct EnumDefEntry<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub args: V::CollectionContainer<V::TypeRet>,
    }
    pub fn walk_enum_def_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::EnumDefEntry>,
    ) -> Result<EnumDefEntry<V>, V::Error> {
        Ok(EnumDefEntry {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter_mut()
                    .map(|b| visitor.visit_type(ctx, b.ast_ref_mut())),
            )?,
        })
    }

    pub struct EnumDef<V: AstVisitorMut> {
        pub entries: V::CollectionContainer<V::EnumDefEntryRet>,
    }
    pub fn walk_enum_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::EnumDef>,
    ) -> Result<EnumDef<V>, V::Error> {
        Ok(EnumDef {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter_mut()
                    .map(|b| visitor.visit_enum_def_entry(ctx, b.ast_ref_mut())),
            )?,
        })
    }

    pub struct TypeFunctionDef<V: AstVisitorMut> {
        pub args: V::CollectionContainer<V::TypeFunctionDefArgRet>,
        pub return_ty: Option<V::TypeRet>,
        pub expression: V::ExpressionRet,
    }

    pub fn walk_type_function_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TypeFunctionDef>,
    ) -> Result<TypeFunctionDef<V>, V::Error> {
        Ok(TypeFunctionDef {
            args: V::try_collect_items(
                ctx,
                node.args
                    .iter_mut()
                    .map(|t| visitor.visit_type_function_def_arg(ctx, t.ast_ref_mut())),
            )?,
            return_ty: node
                .return_ty
                .as_mut()
                .map(|t| visitor.visit_type(ctx, t.ast_ref_mut()))
                .transpose()?,
            expression: visitor.visit_expression(ctx, node.expr.ast_ref_mut())?,
        })
    }

    pub struct TypeFunctionDefArg<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
    }

    pub fn walk_type_function_def_arg<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TypeFunctionDefArg>,
    ) -> Result<TypeFunctionDefArg<V>, V::Error> {
        Ok(TypeFunctionDefArg {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            ty: node
                .ty
                .as_mut()
                .map(|inner| visitor.visit_type(ctx, inner.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct TraitDef<V: AstVisitorMut> {
        pub members: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_trait_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TraitDef>,
    ) -> Result<TraitDef<V>, V::Error> {
        Ok(TraitDef {
            members: V::try_collect_items(
                ctx,
                node.members
                    .iter_mut()
                    .map(|t| visitor.visit_expression(ctx, t.ast_ref_mut())),
            )?,
        })
    }

    pub struct TraitImpl<V: AstVisitorMut> {
        pub ty: V::TypeRet,
        pub implementation: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_trait_impl<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TraitImpl>,
    ) -> Result<TraitImpl<V>, V::Error> {
        Ok(TraitImpl {
            ty: visitor.visit_type(ctx, node.ty.ast_ref_mut())?,
            implementation: V::try_collect_items(
                ctx,
                node.implementation
                    .iter_mut()
                    .map(|t| visitor.visit_expression(ctx, t.ast_ref_mut())),
            )?,
        })
    }

    pub struct Module<V: AstVisitorMut> {
        pub contents: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_module<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Module>,
    ) -> Result<Module<V>, V::Error> {
        Ok(Module {
            contents: V::try_collect_items(
                ctx,
                node.contents
                    .iter_mut()
                    .map(|s| visitor.visit_expression(ctx, s.ast_ref_mut())),
            )?,
        })
    }
}
