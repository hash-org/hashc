//! Visitor implementation for [crate::ast] nodes.
//!
//! All rights reserved 2022 (c) The Hash Language authors
use crate::ast;
use std::convert::Infallible;

/// The main visitor trait for [crate::ast] nodes.
///
/// This contains a method for each AST structure, as well as a dedicated return type for it.
/// These can be implemented using the functions defined in [walk] that can traverse the children
/// of each node.
pub trait AstVisitor<'c>: Sized {
    /// Context type immutably passed to each visitor method for separating mutable from immutable context.
    type Ctx: 'c;

    /// What container to use to collect multiple children, used by [walk].
    type CollectionContainer<T: 'c>: Sized + 'c;

    /// Try collect an iterator of results into a container specified by [Self::CollectionContainer].
    fn try_collect_items<T: 'c, E, I: Iterator<Item = Result<T, E>>>(
        ctx: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E>;

    /// Collect an iterator of items into a container specified by [Self::CollectionContainer].
    fn collect_items<T: 'c, E, I: Iterator<Item = T>>(
        ctx: &Self::Ctx,
        items: I,
    ) -> Self::CollectionContainer<T> {
        Self::try_collect_items::<T, Infallible, _>(ctx, items.map(|item| Ok(item))).unwrap()
    }

    /// The error type to use for each visit method.
    type Error: 'c;

    type ImportRet: 'c;
    fn visit_import(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error>;

    type NameRet: 'c;
    fn visit_name(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Name>,
    ) -> Result<Self::NameRet, Self::Error>;

    type AccessNameRet: 'c;
    fn visit_access_name(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AccessName<'c>>,
    ) -> Result<Self::AccessNameRet, Self::Error>;

    type LiteralRet: 'c;
    fn visit_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Literal<'c>>,
    ) -> Result<Self::LiteralRet, Self::Error>;

    type ExpressionRet: 'c;
    fn visit_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Result<Self::ExpressionRet, Self::Error>;

    type VariableExprRet: 'c;
    fn visit_variable_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> Result<Self::VariableExprRet, Self::Error>;

    type DirectiveExprRet: 'c;
    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DirectiveExpr<'c>>,
    ) -> Result<Self::DirectiveExprRet, Self::Error>;

    type FunctionCallArgRet: 'c;
    fn visit_function_call_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallArg<'c>>,
    ) -> Result<Self::FunctionCallArgRet, Self::Error>;

    type FunctionCallArgsRet: 'c;
    fn visit_function_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> Result<Self::FunctionCallArgsRet, Self::Error>;

    type FunctionCallExprRet: 'c;
    fn visit_function_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallExpr<'c>>,
    ) -> Result<Self::FunctionCallExprRet, Self::Error>;

    type PropertyAccessExprRet: 'c;
    fn visit_property_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::PropertyAccessExpr<'c>>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error>;

    type RefExprRet: 'c;
    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefExpr<'c>>,
    ) -> Result<Self::RefExprRet, Self::Error>;

    type DerefExprRet: 'c;
    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DerefExpr<'c>>,
    ) -> Result<Self::DerefExprRet, Self::Error>;

    type UnsafeExprRet: 'c;
    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::UnsafeExpr<'c>>,
    ) -> Result<Self::UnsafeExprRet, Self::Error>;

    type LiteralExprRet: 'c;
    fn visit_literal_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralExpr<'c>>,
    ) -> Result<Self::LiteralExprRet, Self::Error>;

    type AsExprRet: 'c;
    fn visit_as_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AsExpr<'c>>,
    ) -> Result<Self::AsExprRet, Self::Error>;

    type TypeExprRet: 'c;
    fn visit_type_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeExpr<'c>>,
    ) -> Result<Self::TypeExprRet, Self::Error>;

    type BlockExprRet: 'c;
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BlockExpr<'c>>,
    ) -> Result<Self::BlockExprRet, Self::Error>;

    type ImportExprRet: 'c;
    fn visit_import_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ImportExpr<'c>>,
    ) -> Result<Self::ImportExprRet, Self::Error>;

    type TypeRet: 'c;
    fn visit_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Type<'c>>,
    ) -> Result<Self::TypeRet, Self::Error>;

    type NamedFieldTypeRet: 'c;
    fn visit_named_field_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedFieldTypeEntry<'c>>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error>;

    type FnTypeRet: 'c;
    fn visit_function_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FnType<'c>>,
    ) -> Result<Self::FnTypeRet, Self::Error>;

    type TypeFunctionParamRet: 'c;
    fn visit_type_function_param(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionParam<'c>>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error>;

    type TypeFunctionRet: 'c;
    fn visit_type_function(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunction<'c>>,
    ) -> Result<Self::TypeFunctionRet, Self::Error>;

    type TypeFunctionCallRet: 'c;
    fn visit_type_function_call(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionCall<'c>>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error>;

    type NamedTypeRet: 'c;
    fn visit_named_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedType<'c>>,
    ) -> Result<Self::NamedTypeRet, Self::Error>;

    type RefTypeRet: 'c;
    fn visit_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefType<'c>>,
    ) -> Result<Self::RefTypeRet, Self::Error>;

    type MergedTypeRet: 'c;
    fn visit_merged_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MergedType<'c>>,
    ) -> Result<Self::MergedTypeRet, Self::Error>;

    type ExistentialTypeRet: 'c;
    fn visit_existential_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ExistentialType>,
    ) -> Result<Self::ExistentialTypeRet, Self::Error>;

    type InferTypeRet: 'c;
    fn visit_infer_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::InferType>,
    ) -> Result<Self::InferTypeRet, Self::Error>;

    type MapLiteralRet: 'c;
    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLiteral<'c>>,
    ) -> Result<Self::MapLiteralRet, Self::Error>;

    type MapLiteralEntryRet: 'c;
    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLiteralEntry<'c>>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error>;

    type ListLiteralRet: 'c;
    fn visit_list_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListLiteral<'c>>,
    ) -> Result<Self::ListLiteralRet, Self::Error>;

    type SetLiteralRet: 'c;
    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetLiteral<'c>>,
    ) -> Result<Self::SetLiteralRet, Self::Error>;

    type TupleLiteralEntryRet: 'c;
    fn visit_tuple_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteralEntry<'c>>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error>;

    type TupleLiteralRet: 'c;
    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteral<'c>>,
    ) -> Result<Self::TupleLiteralRet, Self::Error>;

    type StrLiteralRet: 'c;
    fn visit_str_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error>;

    type CharLiteralRet: 'c;
    fn visit_char_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error>;

    type FloatLiteralRet: 'c;
    fn visit_float_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error>;

    type BoolLiteralRet: 'c;
    fn visit_bool_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error>;

    type IntLiteralRet: 'c;
    fn visit_int_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error>;

    type FunctionDefRet: 'c;
    fn visit_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDef<'c>>,
    ) -> Result<Self::FunctionDefRet, Self::Error>;

    type FunctionDefArgRet: 'c;
    fn visit_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDefArg<'c>>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error>;

    type BlockRet: 'c;
    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Block<'c>>,
    ) -> Result<Self::BlockRet, Self::Error>;

    type MatchCaseRet: 'c;
    fn visit_match_case(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MatchCase<'c>>,
    ) -> Result<Self::MatchCaseRet, Self::Error>;

    type MatchBlockRet: 'c;
    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MatchBlock<'c>>,
    ) -> Result<Self::MatchBlockRet, Self::Error>;

    type LoopBlockRet: 'c;
    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LoopBlock<'c>>,
    ) -> Result<Self::LoopBlockRet, Self::Error>;

    type ModBlockRet: 'c;
    fn visit_mod_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ModBlock<'c>>,
    ) -> Result<Self::ModBlockRet, Self::Error>;

    type ImplBlockRet: 'c;
    fn visit_impl_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ImplBlock<'c>>,
    ) -> Result<Self::ImplBlockRet, Self::Error>;

    type BodyBlockRet: 'c;
    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BodyBlock<'c>>,
    ) -> Result<Self::BodyBlockRet, Self::Error>;

    type ReturnStatementRet: 'c;
    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ReturnStatement<'c>>,
    ) -> Result<Self::ReturnStatementRet, Self::Error>;

    type BreakStatementRet: 'c;
    fn visit_break_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error>;

    type ContinueStatementRet: 'c;
    fn visit_continue_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error>;

    type VisibilityRet: 'c;
    fn visit_visibility_modifier(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error>;

    type MutabilityRet: 'c;
    fn visit_mutability_modifier(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error>;

    type DeclarationRet: 'c;
    fn visit_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Declaration<'c>>,
    ) -> Result<Self::DeclarationRet, Self::Error>;

    type MergeDeclarationRet: 'c;
    fn visit_merge_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MergeDeclaration<'c>>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error>;

    type AssignExpressionRet: 'c;
    fn visit_assign_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AssignExpression<'c>>,
    ) -> Result<Self::AssignExpressionRet, Self::Error>;

    type StructDefEntryRet: 'c;
    fn visit_struct_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructDefEntry<'c>>,
    ) -> Result<Self::StructDefEntryRet, Self::Error>;

    type StructDefRet: 'c;
    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructDef<'c>>,
    ) -> Result<Self::StructDefRet, Self::Error>;

    type EnumDefEntryRet: 'c;
    fn visit_enum_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::EnumDefEntry<'c>>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error>;

    type EnumDefRet: 'c;
    fn visit_enum_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::EnumDef<'c>>,
    ) -> Result<Self::EnumDefRet, Self::Error>;

    type TraitDefRet: 'c;
    fn visit_trait_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitDef<'c>>,
    ) -> Result<Self::TraitDefRet, Self::Error>;

    type PatternRet: 'c;
    fn visit_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Pattern<'c>>,
    ) -> Result<Self::PatternRet, Self::Error>;

    type TraitImplRet: 'c;
    fn visit_trait_impl(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitImpl<'c>>,
    ) -> Result<Self::TraitImplRet, Self::Error>;

    type TypeFunctionDefRet: 'c;
    fn visit_type_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDef<'c>>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error>;

    type TypeFunctionDefArgRet: 'c;
    fn visit_type_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDefArg<'c>>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error>;

    type ConstructorPatternRet: 'c;
    fn visit_constructor_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ConstructorPattern<'c>>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error>;

    type NamespacePatternRet: 'c;
    fn visit_namespace_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> Result<Self::NamespacePatternRet, Self::Error>;

    type TuplePatternEntryRet: 'c;
    fn visit_tuple_pattern_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePatternEntry<'c>>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error>;

    type TuplePatternRet: 'c;
    fn visit_tuple_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Result<Self::TuplePatternRet, Self::Error>;

    type ListPatternRet: 'c;
    fn visit_list_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListPattern<'c>>,
    ) -> Result<Self::ListPatternRet, Self::Error>;

    type TupleTypeRet: 'c;
    fn visit_tuple_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleType<'c>>,
    ) -> Result<Self::TupleTypeRet, Self::Error>;

    type ListTypeRet: 'c;
    fn visit_list_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListType<'c>>,
    ) -> Result<Self::ListTypeRet, Self::Error>;

    type SetTypeRet: 'c;
    fn visit_set_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetType<'c>>,
    ) -> Result<Self::SetTypeRet, Self::Error>;

    type MapTypeRet: 'c;
    fn visit_map_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapType<'c>>,
    ) -> Result<Self::MapTypeRet, Self::Error>;

    type StrLiteralPatternRet: 'c;
    fn visit_str_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error>;

    type CharLiteralPatternRet: 'c;
    fn visit_char_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error>;

    type IntLiteralPatternRet: 'c;
    fn visit_int_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error>;

    type FloatLiteralPatternRet: 'c;
    fn visit_float_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error>;

    type BoolLiteralPatternRet: 'c;
    fn visit_bool_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error>;

    type LiteralPatternRet: 'c;
    fn visit_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error>;

    type OrPatternRet: 'c;
    fn visit_or_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::OrPattern<'c>>,
    ) -> Result<Self::OrPatternRet, Self::Error>;

    type IfPatternRet: 'c;
    fn visit_if_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IfPattern<'c>>,
    ) -> Result<Self::IfPatternRet, Self::Error>;

    type BindingPatternRet: 'c;
    fn visit_binding_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BindingPattern<'c>>,
    ) -> Result<Self::BindingPatternRet, Self::Error>;

    type SpreadPatternRet: 'c;
    fn visit_spread_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SpreadPattern<'c>>,
    ) -> Result<Self::SpreadPatternRet, Self::Error>;

    type IgnorePatternRet: 'c;
    fn visit_ignore_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error>;

    type DestructuringPatternRet: 'c;
    fn visit_destructuring_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DestructuringPattern<'c>>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error>;

    type ModuleRet: 'c;
    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Module<'c>>,
    ) -> Result<Self::ModuleRet, Self::Error>;
}

/// Contains helper functions and structures to traverse AST nodes using a given visitor.
///
/// Structures are defined which mirror the layout of the AST nodes, but instead of having AST
/// nodes as children, they have the [AstVisitor] output type for each node.
///
/// For enums, there is an additional `*_same_children` function, which traverses the member of
/// each variant and returns the inner type, given that all variants have the same declared type
/// within the visitor.
pub mod walk {
    use super::ast;
    use super::AstVisitor;

    pub struct FunctionDefArg<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
        pub default: Option<V::ExpressionRet>,
    }

    pub fn walk_function_def_arg<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FunctionDefArg<'c>>,
    ) -> Result<FunctionDefArg<'c, V>, V::Error> {
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

    pub struct FunctionDef<'c, V: AstVisitor<'c>> {
        pub args: V::CollectionContainer<V::FunctionDefArgRet>,
        pub return_ty: Option<V::TypeRet>,
        pub fn_body: V::ExpressionRet,
    }

    pub fn walk_function_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FunctionDef<'c>>,
    ) -> Result<FunctionDef<'c, V>, V::Error> {
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

    pub enum Expression<'c, V: AstVisitor<'c>> {
        FunctionCall(V::FunctionCallExprRet),
        Directive(V::DirectiveExprRet),
        Declaration(V::DeclarationRet),
        Variable(V::VariableExprRet),
        PropertyAccess(V::PropertyAccessExprRet),
        Ref(V::RefExprRet),
        Deref(V::DerefExprRet),
        Unsafe(V::UnsafeExprRet),
        LiteralExpr(V::LiteralExprRet),
        Typed(V::AsExprRet),
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
        MergeDeclaration(V::MergeDeclarationRet),
        TraitImpl(V::TraitImplRet),
    }

    pub fn walk_expression<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Result<Expression<'c, V>, V::Error> {
        Ok(match node.kind() {
            ast::ExpressionKind::FunctionCall(inner) => Expression::FunctionCall(
                visitor.visit_function_call_expr(ctx, node.with_body(inner))?,
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
                Expression::Typed(visitor.visit_as_expr(ctx, node.with_body(inner))?)
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
                Expression::Assign(visitor.visit_assign_expression(ctx, node.with_body(r))?)
            }
            ast::ExpressionKind::TraitImpl(r) => {
                Expression::TraitImpl(visitor.visit_trait_impl(ctx, node.with_body(r))?)
            }
        })
    }

    pub fn walk_expression_same_children<'c, V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            'c,
            FunctionCallExprRet = Ret,
            DirectiveExprRet = Ret,
            DeclarationRet = Ret,
            MergeDeclarationRet = Ret,
            VariableExprRet = Ret,
            PropertyAccessExprRet = Ret,
            RefExprRet = Ret,
            DerefExprRet = Ret,
            UnsafeExprRet = Ret,
            LiteralExprRet = Ret,
            AsExprRet = Ret,
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
        })
    }

    pub struct VariableExpr<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
        pub type_args: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_variable_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> Result<VariableExpr<'c, V>, V::Error> {
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

    pub struct DirectiveExpr<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub subject: V::ExpressionRet,
    }

    pub fn walk_directive_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::DirectiveExpr<'c>>,
    ) -> Result<DirectiveExpr<'c, V>, V::Error> {
        Ok(DirectiveExpr {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            subject: visitor.visit_expression(ctx, node.subject.ast_ref())?,
        })
    }

    pub struct FunctionCallArg<'c, V: AstVisitor<'c>> {
        pub name: Option<V::NameRet>,
        pub value: V::ExpressionRet,
    }

    pub fn walk_function_call_arg<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallArg<'c>>,
    ) -> Result<FunctionCallArg<'c, V>, V::Error> {
        Ok(FunctionCallArg {
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
            value: visitor.visit_expression(ctx, node.value.ast_ref())?,
        })
    }

    pub struct FunctionCallArgs<'c, V: AstVisitor<'c>> {
        pub entries: V::CollectionContainer<V::FunctionCallArgRet>,
    }

    pub fn walk_function_call_args<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> Result<FunctionCallArgs<'c, V>, V::Error> {
        Ok(FunctionCallArgs {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter()
                    .map(|e| visitor.visit_function_call_arg(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct FunctionCallExpr<'c, V: AstVisitor<'c>> {
        pub subject: V::ExpressionRet,
        pub args: V::FunctionCallArgsRet,
    }

    pub fn walk_function_call_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallExpr<'c>>,
    ) -> Result<FunctionCallExpr<'c, V>, V::Error> {
        Ok(FunctionCallExpr {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref())?,
            args: visitor.visit_function_call_args(ctx, node.args.ast_ref())?,
        })
    }

    pub struct PropertyAccessExpr<'c, V: AstVisitor<'c>> {
        pub subject: V::ExpressionRet,
        pub property: V::NameRet,
    }

    pub fn walk_property_access_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::PropertyAccessExpr<'c>>,
    ) -> Result<PropertyAccessExpr<'c, V>, V::Error> {
        Ok(PropertyAccessExpr {
            subject: visitor.visit_expression(ctx, node.subject.ast_ref())?,
            property: visitor.visit_name(ctx, node.property.ast_ref())?,
        })
    }

    pub struct RefExpr<'c, V: AstVisitor<'c>> {
        pub inner_expr: V::ExpressionRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::RefExpr<'c>>,
    ) -> Result<RefExpr<'c, V>, V::Error> {
        Ok(RefExpr {
            inner_expr: visitor.visit_expression(ctx, node.inner_expr.ast_ref())?,
            mutability: node
                .mutability
                .as_ref()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct DerefExpr<'c, V: AstVisitor<'c>>(pub V::ExpressionRet);

    pub fn walk_deref_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::DerefExpr<'c>>,
    ) -> Result<DerefExpr<'c, V>, V::Error> {
        Ok(DerefExpr(visitor.visit_expression(ctx, node.0.ast_ref())?))
    }

    pub struct UnsafeExpr<'c, V: AstVisitor<'c>>(pub V::ExpressionRet);

    pub fn walk_unsafe_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::UnsafeExpr<'c>>,
    ) -> Result<UnsafeExpr<'c, V>, V::Error> {
        Ok(UnsafeExpr(visitor.visit_expression(ctx, node.0.ast_ref())?))
    }

    pub struct LiteralExpr<'c, V: AstVisitor<'c>>(pub V::LiteralRet);

    pub fn walk_literal_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LiteralExpr<'c>>,
    ) -> Result<LiteralExpr<'c, V>, V::Error> {
        Ok(LiteralExpr(visitor.visit_literal(ctx, node.0.ast_ref())?))
    }

    pub struct AsExpr<'c, V: AstVisitor<'c>> {
        pub ty: V::TypeRet,
        pub expr: V::ExpressionRet,
    }

    pub fn walk_as_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AsExpr<'c>>,
    ) -> Result<AsExpr<'c, V>, V::Error> {
        Ok(AsExpr {
            ty: visitor.visit_type(ctx, node.ty.ast_ref())?,
            expr: visitor.visit_expression(ctx, node.expr.ast_ref())?,
        })
    }

    pub struct TypeExpr<'c, V: AstVisitor<'c>>(pub V::TypeRet);

    pub fn walk_type_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeExpr<'c>>,
    ) -> Result<TypeExpr<'c, V>, V::Error> {
        Ok(TypeExpr(visitor.visit_type(ctx, node.0.ast_ref())?))
    }

    pub struct BlockExpr<'c, V: AstVisitor<'c>>(pub V::BlockRet);

    pub fn walk_block_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BlockExpr<'c>>,
    ) -> Result<BlockExpr<'c, V>, V::Error> {
        Ok(BlockExpr(visitor.visit_block(ctx, node.0.ast_ref())?))
    }

    pub struct ImportExpr<'c, V: AstVisitor<'c>>(pub V::ImportRet);

    pub fn walk_import_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ImportExpr<'c>>,
    ) -> Result<ImportExpr<'c, V>, V::Error> {
        Ok(ImportExpr(visitor.visit_import(ctx, node.0.ast_ref())?))
    }

    pub enum Literal<'c, V: AstVisitor<'c>> {
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

    pub fn walk_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Literal<'c>>,
    ) -> Result<Literal<'c, V>, V::Error> {
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

    pub fn walk_literal_same_children<'c, V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Literal<'c>>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            'c,
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

    pub struct MatchCase<'c, V: AstVisitor<'c>> {
        pub pattern: V::PatternRet,
        pub expr: V::ExpressionRet,
    }

    pub fn walk_match_case<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MatchCase<'c>>,
    ) -> Result<MatchCase<'c, V>, V::Error> {
        Ok(MatchCase {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
            expr: visitor.visit_expression(ctx, node.expr.ast_ref())?,
        })
    }

    pub struct MatchBlock<'c, V: AstVisitor<'c>> {
        pub subject: V::ExpressionRet,
        pub cases: V::CollectionContainer<V::MatchCaseRet>,
    }

    pub fn walk_match_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MatchBlock<'c>>,
    ) -> Result<MatchBlock<'c, V>, V::Error> {
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

    pub struct LoopBlock<'c, V: AstVisitor<'c>>(pub V::BlockRet);

    pub fn walk_loop_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LoopBlock<'c>>,
    ) -> Result<LoopBlock<'c, V>, V::Error> {
        Ok(LoopBlock(visitor.visit_block(ctx, node.0.ast_ref())?))
    }

    pub struct ModBlock<'c, V: AstVisitor<'c>>(pub V::BlockRet);

    pub fn walk_mod_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ModBlock<'c>>,
    ) -> Result<ModBlock<'c, V>, V::Error> {
        Ok(ModBlock(visitor.visit_block(ctx, node.0.ast_ref())?))
    }

    pub struct ImplBlock<'c, V: AstVisitor<'c>>(pub V::BlockRet);

    pub fn walk_impl_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ImplBlock<'c>>,
    ) -> Result<ImplBlock<'c, V>, V::Error> {
        Ok(ImplBlock(visitor.visit_block(ctx, node.0.ast_ref())?))
    }

    pub struct BodyBlock<'c, V: AstVisitor<'c>> {
        pub statements: V::CollectionContainer<V::ExpressionRet>,
        pub expr: Option<V::ExpressionRet>,
    }

    pub fn walk_body_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BodyBlock<'c>>,
    ) -> Result<BodyBlock<'c, V>, V::Error> {
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

    pub enum Block<'c, V: AstVisitor<'c>> {
        Match(V::MatchBlockRet),
        Loop(V::LoopBlockRet),
        Mod(V::ModBlockRet),
        Body(V::BodyBlockRet),
        Impl(V::ImplBlockRet),
    }

    pub fn walk_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Block<'c>>,
    ) -> Result<Block<'c, V>, V::Error> {
        Ok(match &*node {
            ast::Block::Match(r) => {
                Block::Match(visitor.visit_match_block(ctx, node.with_body(r))?)
            }
            ast::Block::Loop(r) => Block::Loop(visitor.visit_loop_block(ctx, node.with_body(r))?),
            ast::Block::Mod(r) => Block::Mod(visitor.visit_mod_block(ctx, node.with_body(r))?),
            ast::Block::Body(r) => Block::Body(visitor.visit_body_block(ctx, node.with_body(r))?),
            ast::Block::Impl(r) => Block::Impl(visitor.visit_impl_block(ctx, node.with_body(r))?),
        })
    }

    pub fn walk_block_same_children<'c, V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Block<'c>>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            'c,
            MatchBlockRet = Ret,
            LoopBlockRet = Ret,
            ModBlockRet = Ret,
            BodyBlockRet = Ret,
            ImplBlockRet = Ret,
        >,
    {
        Ok(match walk_block(visitor, ctx, node)? {
            Block::Match(r) => r,
            Block::Loop(r) => r,
            Block::Mod(r) => r,
            Block::Body(r) => r,
            Block::Impl(r) => r,
        })
    }

    pub struct SetLiteral<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_set_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SetLiteral<'c>>,
    ) -> Result<SetLiteral<'c, V>, V::Error> {
        Ok(SetLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter()
                    .map(|e| visitor.visit_expression(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct MapLiteralEntry<'c, V: AstVisitor<'c>> {
        pub key: V::ExpressionRet,
        pub value: V::ExpressionRet,
    }

    pub fn walk_map_literal_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapLiteralEntry<'c>>,
    ) -> Result<MapLiteralEntry<'c, V>, V::Error> {
        Ok(MapLiteralEntry {
            key: visitor.visit_expression(ctx, node.key.ast_ref())?,
            value: visitor.visit_expression(ctx, node.value.ast_ref())?,
        })
    }

    pub struct MapLiteral<'c, V: AstVisitor<'c>> {
        pub entries: V::CollectionContainer<V::MapLiteralEntryRet>,
    }

    pub fn walk_map_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapLiteral<'c>>,
    ) -> Result<MapLiteral<'c, V>, V::Error> {
        Ok(MapLiteral {
            entries: V::try_collect_items(
                ctx,
                node.elements
                    .iter()
                    .map(|e| visitor.visit_map_literal_entry(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct ListLiteral<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_list_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListLiteral<'c>>,
    ) -> Result<ListLiteral<'c, V>, V::Error> {
        Ok(ListLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter()
                    .map(|e| visitor.visit_expression(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct TupleLiteralEntry<'c, V: AstVisitor<'c>> {
        pub name: Option<V::NameRet>,
        pub ty: Option<V::TypeRet>,
        pub value: V::ExpressionRet,
    }

    pub fn walk_tuple_literal_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteralEntry<'c>>,
    ) -> Result<TupleLiteralEntry<'c, V>, V::Error> {
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

    pub struct TupleLiteral<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::TupleLiteralEntryRet>,
    }

    pub fn walk_tuple_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteral<'c>>,
    ) -> Result<TupleLiteral<'c, V>, V::Error> {
        Ok(TupleLiteral {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter()
                    .map(|e| visitor.visit_tuple_literal_entry(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct NamedFieldTypeEntry<'c, V: AstVisitor<'c>> {
        pub ty: V::TypeRet,
        pub name: Option<V::NameRet>,
    }

    pub fn walk_named_field_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::NamedFieldTypeEntry<'c>>,
    ) -> Result<NamedFieldTypeEntry<'c, V>, V::Error> {
        Ok(NamedFieldTypeEntry {
            ty: visitor.visit_type(ctx, node.ty.ast_ref())?,
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
        })
    }

    pub struct FnType<'c, V: AstVisitor<'c>> {
        pub args: V::CollectionContainer<V::NamedFieldTypeRet>,
        pub return_ty: V::TypeRet,
    }

    pub fn walk_function_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FnType<'c>>,
    ) -> Result<FnType<'c, V>, V::Error> {
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

    pub struct TupleType<'c, V: AstVisitor<'c>> {
        pub entries: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_tuple_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleType<'c>>,
    ) -> Result<TupleType<'c, V>, V::Error> {
        Ok(TupleType {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter()
                    .map(|e| visitor.visit_named_field_type(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct ListType<'c, V: AstVisitor<'c>> {
        pub inner: V::TypeRet,
    }

    pub fn walk_list_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListType<'c>>,
    ) -> Result<ListType<'c, V>, V::Error> {
        Ok(ListType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref())?,
        })
    }

    pub struct SetType<'c, V: AstVisitor<'c>> {
        pub inner: V::TypeRet,
    }

    pub fn walk_set_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SetType<'c>>,
    ) -> Result<SetType<'c, V>, V::Error> {
        Ok(SetType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref())?,
        })
    }

    pub struct MapType<'c, V: AstVisitor<'c>> {
        pub key: V::TypeRet,
        pub value: V::TypeRet,
    }

    pub fn walk_map_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapType<'c>>,
    ) -> Result<MapType<'c, V>, V::Error> {
        Ok(MapType {
            key: visitor.visit_type(ctx, node.key.ast_ref())?,
            value: visitor.visit_type(ctx, node.value.ast_ref())?,
        })
    }

    pub struct NamedType<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
    }

    pub fn walk_named_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::NamedType<'c>>,
    ) -> Result<NamedType<'c, V>, V::Error> {
        Ok(NamedType {
            name: visitor.visit_access_name(ctx, node.name.ast_ref())?,
        })
    }

    pub struct RefType<'c, V: AstVisitor<'c>> {
        pub inner: V::TypeRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::RefType<'c>>,
    ) -> Result<RefType<'c, V>, V::Error> {
        Ok(RefType {
            inner: visitor.visit_type(ctx, node.inner.ast_ref())?,
            mutability: node
                .mutability
                .as_ref()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct MergedType<'c, V: AstVisitor<'c>>(pub V::CollectionContainer<V::TypeRet>);

    pub fn walk_merged_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MergedType<'c>>,
    ) -> Result<MergedType<'c, V>, V::Error> {
        Ok(MergedType(V::try_collect_items(
            ctx,
            node.0.iter().map(|a| visitor.visit_type(ctx, a.ast_ref())),
        )?))
    }

    pub struct TypeFunctionCall<'c, V: AstVisitor<'c>> {
        pub subject: V::TypeRet,
        pub args: V::CollectionContainer<V::NamedFieldTypeRet>,
    }

    pub fn walk_type_function_call<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionCall<'c>>,
    ) -> Result<TypeFunctionCall<'c, V>, V::Error> {
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

    pub struct TypeFunctionParam<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub bound: Option<V::TypeRet>,
        pub default: Option<V::TypeRet>,
    }

    pub fn walk_type_function_param<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionParam<'c>>,
    ) -> Result<TypeFunctionParam<'c, V>, V::Error> {
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

    pub struct TypeFunction<'c, V: AstVisitor<'c>> {
        pub args: V::CollectionContainer<V::TypeFunctionParamRet>,
        pub return_ty: V::TypeRet,
    }

    pub fn walk_type_function<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunction<'c>>,
    ) -> Result<TypeFunction<'c, V>, V::Error> {
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

    pub enum Type<'c, V: AstVisitor<'c>> {
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

    pub fn walk_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Type<'c>>,
    ) -> Result<Type<'c, V>, V::Error> {
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

    pub fn walk_type_same_children<'c, V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Type<'c>>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            'c,
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

    pub enum Pattern<'c, V: AstVisitor<'c>> {
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

    pub fn walk_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Pattern<'c>>,
    ) -> Result<Pattern<'c, V>, V::Error> {
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

    pub fn walk_pattern_same_children<'c, V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Pattern<'c>>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            'c,
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

    pub struct OrPattern<'c, V: AstVisitor<'c>> {
        pub variants: V::CollectionContainer<V::PatternRet>,
    }
    pub fn walk_or_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::OrPattern<'c>>,
    ) -> Result<OrPattern<'c, V>, V::Error> {
        Ok(OrPattern {
            variants: V::try_collect_items(
                ctx,
                node.variants
                    .iter()
                    .map(|v| visitor.visit_pattern(ctx, v.ast_ref())),
            )?,
        })
    }

    pub struct ConstructorPattern<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
        pub args: V::CollectionContainer<V::TuplePatternEntryRet>,
    }
    pub fn walk_constructor_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ConstructorPattern<'c>>,
    ) -> Result<ConstructorPattern<'c, V>, V::Error> {
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

    pub struct NamespacePattern<'c, V: AstVisitor<'c>> {
        pub patterns: V::CollectionContainer<V::DestructuringPatternRet>,
    }
    pub fn walk_namespace_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> Result<NamespacePattern<'c, V>, V::Error> {
        Ok(NamespacePattern {
            patterns: V::try_collect_items(
                ctx,
                node.fields
                    .iter()
                    .map(|a| visitor.visit_destructuring_pattern(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct TuplePatternEntry<'c, V: AstVisitor<'c>> {
        pub name: Option<V::NameRet>,
        pub pattern: V::PatternRet,
    }

    pub fn walk_tuple_pattern_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TuplePatternEntry<'c>>,
    ) -> Result<TuplePatternEntry<'c, V>, V::Error> {
        Ok(TuplePatternEntry {
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
        })
    }

    pub struct TuplePattern<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::TuplePatternEntryRet>,
    }

    pub fn walk_tuple_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Result<TuplePattern<'c, V>, V::Error> {
        Ok(TuplePattern {
            elements: V::try_collect_items(
                ctx,
                node.fields
                    .iter()
                    .map(|a| visitor.visit_tuple_pattern_entry(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct ListPattern<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::PatternRet>,
    }

    pub fn walk_list_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListPattern<'c>>,
    ) -> Result<ListPattern<'c, V>, V::Error> {
        Ok(ListPattern {
            elements: V::try_collect_items(
                ctx,
                node.fields
                    .iter()
                    .map(|a| visitor.visit_pattern(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct IfPattern<'c, V: AstVisitor<'c>> {
        pub pattern: V::PatternRet,
        pub condition: V::ExpressionRet,
    }
    pub fn walk_if_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::IfPattern<'c>>,
    ) -> Result<IfPattern<'c, V>, V::Error> {
        Ok(IfPattern {
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
            condition: visitor.visit_expression(ctx, node.condition.ast_ref())?,
        })
    }

    pub struct BindingPattern<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub visibility: Option<V::VisibilityRet>,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_binding_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BindingPattern<'c>>,
    ) -> Result<BindingPattern<'c, V>, V::Error> {
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

    pub struct SpreadPattern<'c, V: AstVisitor<'c>> {
        pub name: Option<V::NameRet>,
    }

    pub fn walk_spread_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SpreadPattern<'c>>,
    ) -> Result<SpreadPattern<'c, V>, V::Error> {
        Ok(SpreadPattern {
            name: node
                .name
                .as_ref()
                .map(|t| visitor.visit_name(ctx, t.ast_ref()))
                .transpose()?,
        })
    }

    pub enum LiteralPattern<'c, V: AstVisitor<'c>> {
        Str(V::StrLiteralPatternRet),
        Char(V::CharLiteralPatternRet),
        Int(V::IntLiteralPatternRet),
        Float(V::FloatLiteralPatternRet),
        Bool(V::BoolLiteralPatternRet),
    }

    pub fn walk_literal_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<LiteralPattern<'c, V>, V::Error> {
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

    pub fn walk_literal_pattern_same_children<'c, V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            'c,
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

    pub struct DestructuringPattern<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub pattern: V::PatternRet,
    }
    pub fn walk_destructuring_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::DestructuringPattern<'c>>,
    ) -> Result<DestructuringPattern<'c, V>, V::Error> {
        Ok(DestructuringPattern {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            pattern: visitor.visit_pattern(ctx, node.pattern.ast_ref())?,
        })
    }

    pub struct ReturnStatement<'c, V: AstVisitor<'c>>(pub Option<V::ExpressionRet>);
    pub fn walk_return_statement<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ReturnStatement<'c>>,
    ) -> Result<ReturnStatement<'c, V>, V::Error> {
        Ok(ReturnStatement(
            node.0
                .as_ref()
                .map(|n| visitor.visit_expression(ctx, n.ast_ref()))
                .transpose()?,
        ))
    }

    pub struct Declaration<'c, V: AstVisitor<'c>> {
        pub pattern: V::PatternRet,
        pub ty: Option<V::TypeRet>,
        pub value: Option<V::ExpressionRet>,
    }

    pub fn walk_declaration<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Declaration<'c>>,
    ) -> Result<Declaration<'c, V>, V::Error> {
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

    pub struct MergeDeclaration<'c, V: AstVisitor<'c>> {
        pub decl: V::ExpressionRet,
        pub value: V::ExpressionRet,
    }

    pub fn walk_merge_declaration<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MergeDeclaration<'c>>,
    ) -> Result<MergeDeclaration<'c, V>, V::Error> {
        Ok(MergeDeclaration {
            decl: visitor.visit_expression(ctx, node.decl.ast_ref())?,
            value: visitor.visit_expression(ctx, node.value.ast_ref())?,
        })
    }

    pub struct AssignStatement<'c, V: AstVisitor<'c>> {
        pub lhs: V::ExpressionRet,
        pub rhs: V::ExpressionRet,
    }
    pub fn walk_assign_statement<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AssignExpression<'c>>,
    ) -> Result<AssignStatement<'c, V>, V::Error> {
        Ok(AssignStatement {
            lhs: visitor.visit_expression(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_expression(ctx, node.rhs.ast_ref())?,
        })
    }

    pub struct StructDefEntry<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
        pub default: Option<V::ExpressionRet>,
    }
    pub fn walk_struct_def_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::StructDefEntry<'c>>,
    ) -> Result<StructDefEntry<'c, V>, V::Error> {
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

    pub struct StructDef<'c, V: AstVisitor<'c>> {
        pub entries: V::CollectionContainer<V::StructDefEntryRet>,
    }
    pub fn walk_struct_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::StructDef<'c>>,
    ) -> Result<StructDef<'c, V>, V::Error> {
        Ok(StructDef {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter()
                    .map(|b| visitor.visit_struct_def_entry(ctx, b.ast_ref())),
            )?,
        })
    }

    pub struct EnumDefEntry<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub args: V::CollectionContainer<V::TypeRet>,
    }
    pub fn walk_enum_def_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::EnumDefEntry<'c>>,
    ) -> Result<EnumDefEntry<'c, V>, V::Error> {
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

    pub struct EnumDef<'c, V: AstVisitor<'c>> {
        pub entries: V::CollectionContainer<V::EnumDefEntryRet>,
    }
    pub fn walk_enum_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::EnumDef<'c>>,
    ) -> Result<EnumDef<'c, V>, V::Error> {
        Ok(EnumDef {
            entries: V::try_collect_items(
                ctx,
                node.entries
                    .iter()
                    .map(|b| visitor.visit_enum_def_entry(ctx, b.ast_ref())),
            )?,
        })
    }

    pub struct TypeFunctionDef<'c, V: AstVisitor<'c>> {
        pub args: V::CollectionContainer<V::TypeFunctionDefArgRet>,
        pub return_ty: Option<V::TypeRet>,
        pub expression: V::ExpressionRet,
    }

    pub fn walk_type_function_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDef<'c>>,
    ) -> Result<TypeFunctionDef<'c, V>, V::Error> {
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

    pub struct TypeFunctionDefArg<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
    }

    pub fn walk_type_function_def_arg<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDefArg<'c>>,
    ) -> Result<TypeFunctionDefArg<'c, V>, V::Error> {
        Ok(TypeFunctionDefArg {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            ty: node
                .ty
                .as_ref()
                .map(|inner| visitor.visit_type(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct TraitDef<'c, V: AstVisitor<'c>> {
        pub members: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_trait_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TraitDef<'c>>,
    ) -> Result<TraitDef<'c, V>, V::Error> {
        Ok(TraitDef {
            members: V::try_collect_items(
                ctx,
                node.members
                    .iter()
                    .map(|t| visitor.visit_expression(ctx, t.ast_ref())),
            )?,
        })
    }

    pub struct TraitImpl<'c, V: AstVisitor<'c>> {
        pub trait_name: V::VariableExprRet,
        pub implementation: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_trait_impl<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TraitImpl<'c>>,
    ) -> Result<TraitImpl<'c, V>, V::Error> {
        Ok(TraitImpl {
            trait_name: visitor.visit_variable_expr(ctx, node.name.ast_ref())?,
            implementation: V::try_collect_items(
                ctx,
                node.implementation
                    .iter()
                    .map(|t| visitor.visit_expression(ctx, t.ast_ref())),
            )?,
        })
    }

    pub struct Module<'c, V: AstVisitor<'c>> {
        pub contents: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_module<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Module<'c>>,
    ) -> Result<Module<'c, V>, V::Error> {
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
