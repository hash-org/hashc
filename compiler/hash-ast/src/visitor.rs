//! Visitor implementation for [crate::ast] nodes.

use std::convert::Infallible;

use crate::ast;

/// A visitor [crate::ast] nodes that takes `&mut self`.
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

    type NameRet;
    fn visit_name(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Name>,
    ) -> Result<Self::NameRet, Self::Error>;

    type LitRet;
    fn visit_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Lit>,
    ) -> Result<Self::LitRet, Self::Error>;

    type MapLitRet;
    fn visit_map_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLit>,
    ) -> Result<Self::MapLitRet, Self::Error>;

    type MapLitEntryRet;
    fn visit_map_lit_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLitEntry>,
    ) -> Result<Self::MapLitEntryRet, Self::Error>;

    type ListLitRet;
    fn visit_list_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListLit>,
    ) -> Result<Self::ListLitRet, Self::Error>;

    type SetLitRet;
    fn visit_set_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetLit>,
    ) -> Result<Self::SetLitRet, Self::Error>;

    type TupleLitEntryRet;
    fn visit_tuple_lit_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitEntryRet, Self::Error>;

    type TupleLitRet;
    fn visit_tuple_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error>;

    type StrLitRet;
    fn visit_str_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error>;

    type CharLitRet;
    fn visit_char_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error>;

    type FloatLitRet;
    fn visit_float_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error>;

    type BoolLitRet;
    fn visit_bool_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error>;

    type IntLitRet;
    fn visit_int_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error>;

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

    type ExprRet;
    fn visit_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Expr>,
    ) -> Result<Self::ExprRet, Self::Error>;

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

    type AccessExprRet;
    fn visit_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error>;

    type AccessKindRet;
    fn visit_access_kind(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AccessKind,
    ) -> Result<Self::AccessKindRet, Self::Error>;

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

    type LitExprRet;
    fn visit_lit_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LitExpr>,
    ) -> Result<Self::LitExprRet, Self::Error>;

    type CastExprRet;
    fn visit_cast_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error>;

    type TyExprRet;
    fn visit_ty_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error>;

    type BlockExprRet;
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error>;

    type ImportRet;
    fn visit_import(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error>;

    type ImportExprRet;
    fn visit_import_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error>;

    type TyRet;
    fn visit_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Ty>,
    ) -> Result<Self::TyRet, Self::Error>;

    type TupleTyRet;
    fn visit_tuple_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error>;

    type ListTyRet;
    fn visit_list_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListTy>,
    ) -> Result<Self::ListTyRet, Self::Error>;

    type SetTyRet;
    fn visit_set_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetTy>,
    ) -> Result<Self::SetTyRet, Self::Error>;

    type MapTyRet;
    fn visit_map_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapTy>,
    ) -> Result<Self::MapTyRet, Self::Error>;

    type TyArgRet;
    fn visit_ty_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error>;

    type FnTyRet;
    fn visit_fn_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FnTy>,
    ) -> Result<Self::FnTyRet, Self::Error>;

    type TyFnRet;
    fn visit_ty_fn_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TyFn>,
    ) -> Result<Self::TyFnRet, Self::Error>;

    type TyFnCallRet;
    fn visit_ty_fn_call(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error>;

    type NamedTyRet;
    fn visit_named_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error>;

    type AccessTyRet;
    fn visit_access_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error>;

    type RefTyRet;
    fn visit_ref_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error>;

    type MergeTyRet;
    fn visit_merge_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error>;

    type UnionTyRet;
    fn visit_union_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error>;

    type TyFnDefRet;
    fn visit_ty_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error>;

    type FnDefRet;
    fn visit_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error>;

    type ParamRet;
    fn visit_param(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error>;

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

    type RefKindRet;
    fn visit_ref_kind(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefKind>,
    ) -> Result<Self::RefKindRet, Self::Error>;

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

    type AssignExprRet;
    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error>;

    type AssignOpExprRet;
    fn visit_assign_op_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error>;

    type BinaryExprRet;
    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error>;

    type UnaryExprRet;
    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error>;

    type IndexExprRet;
    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error>;

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

    type TraitImplRet;
    fn visit_trait_impl(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error>;

    type PatRet;
    fn visit_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Pat>,
    ) -> Result<Self::PatRet, Self::Error>;

    type AccessPatRet;
    fn visit_access_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error>;

    type ConstructorPatRet;
    fn visit_constructor_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error>;

    type TuplePatEntryRet;
    fn visit_tuple_pat_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePatEntry>,
    ) -> Result<Self::TuplePatEntryRet, Self::Error>;

    type TuplePatRet;
    fn visit_tuple_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error>;

    type ListPatRet;
    fn visit_list_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListPat>,
    ) -> Result<Self::ListPatRet, Self::Error>;

    type SpreadPatRet;
    fn visit_spread_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error>;

    type LitPatRet;
    fn visit_lit_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LitPat>,
    ) -> Result<Self::LitPatRet, Self::Error>;

    type OrPatRet;
    fn visit_or_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error>;

    type IfPatRet;
    fn visit_if_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error>;

    type BindingPatRet;
    fn visit_binding_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error>;

    type WildPatRet;
    fn visit_wild_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error>;

    type ModulePatEntryRet;
    fn visit_module_pat_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error>;

    type ModulePatRet;
    fn visit_module_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error>;

    type ModuleRet;
    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error>;
}

/// A visitor [crate::ast] nodes that takes `&mut self` and mutable node
/// references.
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

    type NameRet;
    fn visit_name(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Name>,
    ) -> Result<Self::NameRet, Self::Error>;

    type LitRet;
    fn visit_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Lit>,
    ) -> Result<Self::LitRet, Self::Error>;

    type MapLitRet;
    fn visit_map_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MapLit>,
    ) -> Result<Self::MapLitRet, Self::Error>;

    type MapLitEntryRet;
    fn visit_map_lit_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MapLitEntry>,
    ) -> Result<Self::MapLitEntryRet, Self::Error>;

    type ListLitRet;
    fn visit_list_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ListLit>,
    ) -> Result<Self::ListLitRet, Self::Error>;

    type SetLitRet;
    fn visit_set_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::SetLit>,
    ) -> Result<Self::SetLitRet, Self::Error>;

    type TupleLitEntryRet;
    fn visit_tuple_lit_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitEntryRet, Self::Error>;

    type TupleLitRet;
    fn visit_tuple_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error>;

    type StrLitRet;
    fn visit_str_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error>;

    type CharLitRet;
    fn visit_char_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error>;

    type FloatLitRet;
    fn visit_float_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error>;

    type BoolLitRet;
    fn visit_bool_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error>;

    type IntLitRet;
    fn visit_int_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error>;

    type BinOpRet;
    fn visit_bin_op(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BinOp>,
    ) -> Result<Self::BinOpRet, Self::Error>;

    type UnOpRet;
    fn visit_un_op(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::UnOp>,
    ) -> Result<Self::UnOpRet, Self::Error>;

    type ExprRet;
    fn visit_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Expr>,
    ) -> Result<Self::ExprRet, Self::Error>;

    type ImportRet;
    fn visit_import(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error>;

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

    type AccessExprRet;
    fn visit_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error>;

    type AccessKindRet;
    fn visit_access_kind(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AccessKind,
    ) -> Result<Self::AccessKindRet, Self::Error>;

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

    type LitExprRet;
    fn visit_lit_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::LitExpr>,
    ) -> Result<Self::LitExprRet, Self::Error>;

    type CastExprRet;
    fn visit_cast_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error>;

    type TyExprRet;
    fn visit_ty_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error>;

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

    type TyRet;
    fn visit_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Ty>,
    ) -> Result<Self::TyRet, Self::Error>;

    type TupleTyRet;
    fn visit_tuple_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error>;

    type ListTyRet;
    fn visit_list_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ListTy>,
    ) -> Result<Self::ListTyRet, Self::Error>;

    type SetTyRet;
    fn visit_set_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::SetTy>,
    ) -> Result<Self::SetTyRet, Self::Error>;

    type MapTyRet;
    fn visit_map_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MapTy>,
    ) -> Result<Self::MapTyRet, Self::Error>;

    type TyArgRet;
    fn visit_ty_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error>;

    type FnTyRet;
    fn visit_fn_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::FnTy>,
    ) -> Result<Self::FnTyRet, Self::Error>;

    type TyFnRet;
    fn visit_ty_fn_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TyFn>,
    ) -> Result<Self::TyFnRet, Self::Error>;

    type TyFnCallRet;
    fn visit_ty_fn_call(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error>;

    type NamedTyRet;
    fn visit_named_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error>;

    type AccessTyRet;
    fn visit_access_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error>;

    type RefTyRet;
    fn visit_ref_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error>;

    type MergeTyRet;
    fn visit_merge_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error>;

    type UnionTyRet;
    fn visit_union_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error>;

    type TyFnDefRet;
    fn visit_ty_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error>;

    type FnDefRet;
    fn visit_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error>;

    type ParamRet;
    fn visit_param(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error>;

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

    type AssignExprRet;
    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error>;

    type AssignOpExprRet;
    fn visit_assign_op_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error>;

    type BinaryExprRet;
    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error>;

    type UnaryExprRet;
    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error>;

    type IndexExprRet;
    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error>;

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

    type TraitImplRet;
    fn visit_trait_impl(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error>;

    type PatRet;
    fn visit_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::Pat>,
    ) -> Result<Self::PatRet, Self::Error>;

    type AccessPatRet;
    fn visit_access_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error>;

    type ConstructorPatRet;
    fn visit_constructor_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error>;

    type TuplePatEntryRet;
    fn visit_tuple_pat_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TuplePatEntry>,
    ) -> Result<Self::TuplePatEntryRet, Self::Error>;

    type TuplePatRet;
    fn visit_tuple_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error>;

    type ListPatRet;
    fn visit_list_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ListPat>,
    ) -> Result<Self::ListPatRet, Self::Error>;

    type SpreadPatRet;
    fn visit_spread_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error>;

    type LitPatRet;
    fn visit_lit_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::LitPat>,
    ) -> Result<Self::LitPatRet, Self::Error>;

    type OrPatRet;
    fn visit_or_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error>;

    type IfPatRet;
    fn visit_if_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error>;

    type BindingPatRet;
    fn visit_binding_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error>;

    type WildPatRet;
    fn visit_wild_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error>;

    type ModulePatEntryRet;
    fn visit_module_pat_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error>;

    type ModulePatRet;
    fn visit_module_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRefMut<ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error>;

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

    pub struct Param<V: AstVisitor> {
        pub name: V::NameRet,
        pub ty: Option<V::TyRet>,
        pub default: Option<V::ExprRet>,
    }

    pub fn walk_param<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Param>,
    ) -> Result<Param<V>, V::Error> {
        Ok(Param {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            ty: node.ty.as_ref().map(|t| visitor.visit_ty(ctx, t.ast_ref())).transpose()?,
            default: node
                .default
                .as_ref()
                .map(|t| visitor.visit_expr(ctx, t.ast_ref()))
                .transpose()?,
        })
    }

    pub struct FnDef<V: AstVisitor> {
        pub args: V::CollectionContainer<V::ParamRet>,
        pub return_ty: Option<V::TyRet>,
        pub fn_body: V::ExprRet,
    }

    pub fn walk_fn_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<FnDef<V>, V::Error> {
        Ok(FnDef {
            args: V::try_collect_items(
                ctx,
                node.params.iter().map(|a| visitor.visit_param(ctx, a.ast_ref())),
            )?,
            return_ty: node
                .return_ty
                .as_ref()
                .map(|t| visitor.visit_ty(ctx, t.ast_ref()))
                .transpose()?,
            fn_body: visitor.visit_expr(ctx, node.fn_body.ast_ref())?,
        })
    }

    pub enum Expr<V: AstVisitor> {
        ConstructorCall(V::ConstructorCallExprRet),
        Directive(V::DirectiveExprRet),
        Declaration(V::DeclarationRet),
        Variable(V::VariableExprRet),
        Access(V::AccessExprRet),
        Ref(V::RefExprRet),
        Deref(V::DerefExprRet),
        Unsafe(V::UnsafeExprRet),
        LitExpr(V::LitExprRet),
        Cast(V::CastExprRet),
        Block(V::BlockExprRet),
        Import(V::ImportExprRet),
        StructDef(V::StructDefRet),
        EnumDef(V::EnumDefRet),
        TyFnDef(V::TyFnDefRet),
        TraitDef(V::TraitDefRet),
        FnDef(V::FnDefRet),
        Ty(V::TyExprRet),
        Return(V::ReturnStatementRet),
        Break(V::BreakStatementRet),
        Continue(V::ContinueStatementRet),
        Assign(V::AssignExprRet),
        AssignOp(V::AssignOpExprRet),
        MergeDeclaration(V::MergeDeclarationRet),
        TraitImpl(V::TraitImplRet),
        BinaryExpr(V::BinaryExprRet),
        UnaryExpr(V::UnaryExprRet),
        Index(V::IndexExprRet),
    }

    pub fn walk_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Expr>,
    ) -> Result<Expr<V>, V::Error> {
        Ok(match node.kind() {
            ast::ExprKind::ConstructorCall(inner) => Expr::ConstructorCall(
                visitor.visit_constructor_call_expr(ctx, node.with_body(inner))?,
            ),
            ast::ExprKind::Ty(inner) => {
                Expr::Ty(visitor.visit_ty_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Directive(inner) => {
                Expr::Directive(visitor.visit_directive_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Declaration(inner) => {
                Expr::Declaration(visitor.visit_declaration(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::MergeDeclaration(inner) => {
                Expr::MergeDeclaration(visitor.visit_merge_declaration(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Variable(inner) => {
                Expr::Variable(visitor.visit_variable_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Access(inner) => {
                Expr::Access(visitor.visit_access_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Ref(inner) => {
                Expr::Ref(visitor.visit_ref_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Deref(inner) => {
                Expr::Deref(visitor.visit_deref_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Unsafe(inner) => {
                Expr::Unsafe(visitor.visit_unsafe_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::LitExpr(inner) => {
                Expr::LitExpr(visitor.visit_lit_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Cast(inner) => {
                Expr::Cast(visitor.visit_cast_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Block(inner) => {
                Expr::Block(visitor.visit_block_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::Import(inner) => {
                Expr::Import(visitor.visit_import_expr(ctx, node.with_body(inner))?)
            }
            ast::ExprKind::StructDef(r) => {
                Expr::StructDef(visitor.visit_struct_def(ctx, node.with_body(r))?)
            }
            ast::ExprKind::EnumDef(r) => {
                Expr::EnumDef(visitor.visit_enum_def(ctx, node.with_body(r))?)
            }
            ast::ExprKind::TyFnDef(r) => {
                Expr::TyFnDef(visitor.visit_ty_fn_def(ctx, node.with_body(r))?)
            }
            ast::ExprKind::TraitDef(r) => {
                Expr::TraitDef(visitor.visit_trait_def(ctx, node.with_body(r))?)
            }
            ast::ExprKind::FnDef(r) => Expr::FnDef(visitor.visit_fn_def(ctx, node.with_body(r))?),
            ast::ExprKind::Return(r) => {
                Expr::Return(visitor.visit_return_statement(ctx, node.with_body(r))?)
            }
            ast::ExprKind::Break(r) => {
                Expr::Break(visitor.visit_break_statement(ctx, node.with_body(r))?)
            }
            ast::ExprKind::Continue(r) => {
                Expr::Continue(visitor.visit_continue_statement(ctx, node.with_body(r))?)
            }
            ast::ExprKind::Assign(r) => {
                Expr::Assign(visitor.visit_assign_expr(ctx, node.with_body(r))?)
            }
            ast::ExprKind::AssignOp(r) => {
                Expr::AssignOp(visitor.visit_assign_op_expr(ctx, node.with_body(r))?)
            }
            ast::ExprKind::TraitImpl(r) => {
                Expr::TraitImpl(visitor.visit_trait_impl(ctx, node.with_body(r))?)
            }
            ast::ExprKind::BinaryExpr(r) => {
                Expr::BinaryExpr(visitor.visit_binary_expr(ctx, node.with_body(r))?)
            }
            ast::ExprKind::UnaryExpr(r) => {
                Expr::UnaryExpr(visitor.visit_unary_expr(ctx, node.with_body(r))?)
            }
            ast::ExprKind::Index(r) => {
                Expr::Index(visitor.visit_index_expr(ctx, node.with_body(r))?)
            }
        })
    }

    pub fn walk_expr_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Expr>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            ConstructorCallExprRet = Ret,
            DirectiveExprRet = Ret,
            DeclarationRet = Ret,
            MergeDeclarationRet = Ret,
            VariableExprRet = Ret,
            AccessExprRet = Ret,
            RefExprRet = Ret,
            DerefExprRet = Ret,
            UnsafeExprRet = Ret,
            LitExprRet = Ret,
            CastExprRet = Ret,
            BlockExprRet = Ret,
            ImportExprRet = Ret,
            StructDefRet = Ret,
            EnumDefRet = Ret,
            TyFnDefRet = Ret,
            TraitDefRet = Ret,
            TraitImplRet = Ret,
            FnDefRet = Ret,
            TyExprRet = Ret,
            ReturnStatementRet = Ret,
            BreakStatementRet = Ret,
            ContinueStatementRet = Ret,
            AssignExprRet = Ret,
            AssignOpExprRet = Ret,
            BinaryExprRet = Ret,
            UnaryExprRet = Ret,
            IndexExprRet = Ret,
        >,
    {
        Ok(match walk_expr(visitor, ctx, node)? {
            Expr::ConstructorCall(r) => r,
            Expr::Directive(r) => r,
            Expr::Declaration(r) => r,
            Expr::MergeDeclaration(r) => r,
            Expr::Variable(r) => r,
            Expr::Access(r) => r,
            Expr::Ref(r) => r,
            Expr::Deref(r) => r,
            Expr::Unsafe(r) => r,
            Expr::LitExpr(r) => r,
            Expr::Cast(r) => r,
            Expr::Block(r) => r,
            Expr::Import(r) => r,
            Expr::StructDef(r) => r,
            Expr::EnumDef(r) => r,
            Expr::TyFnDef(r) => r,
            Expr::TraitDef(r) => r,
            Expr::TraitImpl(r) => r,
            Expr::FnDef(r) => r,
            Expr::Ty(r) => r,
            Expr::Return(r) => r,
            Expr::Break(r) => r,
            Expr::Continue(r) => r,
            Expr::Assign(r) => r,
            Expr::AssignOp(r) => r,
            Expr::BinaryExpr(r) => r,
            Expr::UnaryExpr(r) => r,
            Expr::Index(r) => r,
        })
    }

    pub struct VariableExpr<V: AstVisitor> {
        pub name: V::NameRet,
    }

    pub fn walk_variable_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::VariableExpr>,
    ) -> Result<VariableExpr<V>, V::Error> {
        Ok(VariableExpr { name: visitor.visit_name(ctx, node.name.ast_ref())? })
    }

    pub struct DirectiveExpr<V: AstVisitor> {
        pub name: V::NameRet,
        pub subject: V::ExprRet,
    }

    pub fn walk_directive_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::DirectiveExpr>,
    ) -> Result<DirectiveExpr<V>, V::Error> {
        Ok(DirectiveExpr {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            subject: visitor.visit_expr(ctx, node.subject.ast_ref())?,
        })
    }

    pub struct ConstructorCallArg<V: AstVisitor> {
        pub name: Option<V::NameRet>,
        pub value: V::ExprRet,
    }

    pub fn walk_constructor_call_arg<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ConstructorCallArg>,
    ) -> Result<ConstructorCallArg<V>, V::Error> {
        Ok(ConstructorCallArg {
            name: node.name.as_ref().map(|t| visitor.visit_name(ctx, t.ast_ref())).transpose()?,
            value: visitor.visit_expr(ctx, node.value.ast_ref())?,
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
                node.entries.iter().map(|e| visitor.visit_constructor_call_arg(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct ConstructorCallExpr<V: AstVisitor> {
        pub subject: V::ExprRet,
        pub args: V::ConstructorCallArgsRet,
    }

    pub fn walk_constructor_call_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ConstructorCallExpr>,
    ) -> Result<ConstructorCallExpr<V>, V::Error> {
        Ok(ConstructorCallExpr {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref())?,
            args: visitor.visit_constructor_call_args(ctx, node.args.ast_ref())?,
        })
    }

    pub struct AccessExpr<V: AstVisitor> {
        pub subject: V::ExprRet,
        pub property: V::NameRet,
        pub kind: V::AccessKindRet,
    }

    pub fn walk_access_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AccessExpr>,
    ) -> Result<AccessExpr<V>, V::Error> {
        Ok(AccessExpr {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref())?,
            property: visitor.visit_name(ctx, node.property.ast_ref())?,
            kind: visitor.visit_access_kind(ctx, node.kind)?,
        })
    }

    pub struct RefExpr<V: AstVisitor> {
        pub inner_expr: V::ExprRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::RefExpr>,
    ) -> Result<RefExpr<V>, V::Error> {
        Ok(RefExpr {
            inner_expr: visitor.visit_expr(ctx, node.inner_expr.ast_ref())?,
            mutability: node
                .mutability
                .as_ref()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct DerefExpr<V: AstVisitor>(pub V::ExprRet);

    pub fn walk_deref_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::DerefExpr>,
    ) -> Result<DerefExpr<V>, V::Error> {
        Ok(DerefExpr(visitor.visit_expr(ctx, node.0.ast_ref())?))
    }

    pub struct UnsafeExpr<V: AstVisitor>(pub V::ExprRet);

    pub fn walk_unsafe_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::UnsafeExpr>,
    ) -> Result<UnsafeExpr<V>, V::Error> {
        Ok(UnsafeExpr(visitor.visit_expr(ctx, node.0.ast_ref())?))
    }

    pub struct LitExpr<V: AstVisitor>(pub V::LitRet);

    pub fn walk_lit_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LitExpr>,
    ) -> Result<LitExpr<V>, V::Error> {
        Ok(LitExpr(visitor.visit_lit(ctx, node.0.ast_ref())?))
    }

    pub struct CastExpr<V: AstVisitor> {
        pub expr: V::ExprRet,
        pub ty: V::TyRet,
    }

    pub fn walk_cast_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::CastExpr>,
    ) -> Result<CastExpr<V>, V::Error> {
        Ok(CastExpr {
            ty: visitor.visit_ty(ctx, node.ty.ast_ref())?,
            expr: visitor.visit_expr(ctx, node.expr.ast_ref())?,
        })
    }

    pub struct TyExpr<V: AstVisitor>(pub V::TyRet);

    pub fn walk_ty_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TyExpr>,
    ) -> Result<TyExpr<V>, V::Error> {
        Ok(TyExpr(visitor.visit_ty(ctx, node.0.ast_ref())?))
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

    pub enum Lit<V: AstVisitor> {
        Str(V::StrLitRet),
        Char(V::CharLitRet),
        Int(V::IntLitRet),
        Float(V::FloatLitRet),
        Bool(V::BoolLitRet),
        Set(V::SetLitRet),
        Map(V::MapLitRet),
        List(V::ListLitRet),
        Tuple(V::TupleLitRet),
    }

    pub fn walk_lit<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Lit>,
    ) -> Result<Lit<V>, V::Error> {
        Ok(match &*node {
            ast::Lit::Str(r) => Lit::Str(visitor.visit_str_lit(ctx, node.with_body(r))?),
            ast::Lit::Char(r) => Lit::Char(visitor.visit_char_lit(ctx, node.with_body(r))?),
            ast::Lit::Int(r) => Lit::Int(visitor.visit_int_lit(ctx, node.with_body(r))?),
            ast::Lit::Float(r) => Lit::Float(visitor.visit_float_lit(ctx, node.with_body(r))?),
            ast::Lit::Bool(r) => Lit::Bool(visitor.visit_bool_lit(ctx, node.with_body(r))?),
            ast::Lit::Set(r) => Lit::Set(visitor.visit_set_lit(ctx, node.with_body(r))?),
            ast::Lit::Map(r) => Lit::Map(visitor.visit_map_lit(ctx, node.with_body(r))?),
            ast::Lit::List(r) => Lit::List(visitor.visit_list_lit(ctx, node.with_body(r))?),
            ast::Lit::Tuple(r) => Lit::Tuple(visitor.visit_tuple_lit(ctx, node.with_body(r))?),
        })
    }

    pub fn walk_lit_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Lit>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            StrLitRet = Ret,
            CharLitRet = Ret,
            IntLitRet = Ret,
            FloatLitRet = Ret,
            BoolLitRet = Ret,
            SetLitRet = Ret,
            MapLitRet = Ret,
            ListLitRet = Ret,
            TupleLitRet = Ret,
        >,
    {
        Ok(match walk_lit(visitor, ctx, node)? {
            Lit::Str(r) => r,
            Lit::Char(r) => r,
            Lit::Int(r) => r,
            Lit::Float(r) => r,
            Lit::Bool(r) => r,
            Lit::Set(r) => r,
            Lit::Map(r) => r,
            Lit::List(r) => r,
            Lit::Tuple(r) => r,
        })
    }

    pub struct MatchCase<V: AstVisitor> {
        pub pat: V::PatRet,
        pub expr: V::ExprRet,
    }

    pub fn walk_match_case<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<MatchCase<V>, V::Error> {
        Ok(MatchCase {
            pat: visitor.visit_pat(ctx, node.pat.ast_ref())?,
            expr: visitor.visit_expr(ctx, node.expr.ast_ref())?,
        })
    }

    pub struct MatchBlock<V: AstVisitor> {
        pub subject: V::ExprRet,
        pub cases: V::CollectionContainer<V::MatchCaseRet>,
    }

    pub fn walk_match_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MatchBlock>,
    ) -> Result<MatchBlock<V>, V::Error> {
        Ok(MatchBlock {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref())?,
            cases: V::try_collect_items(
                ctx,
                node.cases.iter().map(|c| visitor.visit_match_case(ctx, c.ast_ref())),
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
        pub pat: V::PatRet,
        pub iterator: V::ExprRet,
        pub body: V::BlockRet,
    }

    pub fn walk_for_loop_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ForLoopBlock>,
    ) -> Result<ForLoopBlock<V>, V::Error> {
        Ok(ForLoopBlock {
            pat: visitor.visit_pat(ctx, node.pat.ast_ref())?,
            iterator: visitor.visit_expr(ctx, node.iterator.ast_ref())?,
            body: visitor.visit_block(ctx, node.body.ast_ref())?,
        })
    }

    pub struct WhileLoopBlock<V: AstVisitor> {
        pub condition: V::ExprRet,
        pub body: V::BlockRet,
    }

    pub fn walk_while_loop_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::WhileLoopBlock>,
    ) -> Result<WhileLoopBlock<V>, V::Error> {
        Ok(WhileLoopBlock {
            condition: visitor.visit_expr(ctx, node.condition.ast_ref())?,
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
        pub condition: V::ExprRet,
        pub body: V::BlockRet,
    }

    pub fn walk_if_clause<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::IfClause>,
    ) -> Result<IfClause<V>, V::Error> {
        Ok(IfClause {
            condition: visitor.visit_expr(ctx, node.condition.ast_ref())?,
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
                node.clauses.iter().map(|clause| visitor.visit_if_clause(ctx, clause.ast_ref())),
            )?,
            otherwise: node
                .otherwise
                .as_ref()
                .map(|body| visitor.visit_block(ctx, body.ast_ref()))
                .transpose()?,
        })
    }

    pub struct BodyBlock<V: AstVisitor> {
        pub statements: V::CollectionContainer<V::ExprRet>,
        pub expr: Option<V::ExprRet>,
    }

    pub fn walk_body_block<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<BodyBlock<V>, V::Error> {
        Ok(BodyBlock {
            statements: V::try_collect_items(
                ctx,
                node.statements.iter().map(|s| visitor.visit_expr(ctx, s.ast_ref())),
            )?,
            expr: node.expr.as_ref().map(|e| visitor.visit_expr(ctx, e.ast_ref())).transpose()?,
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

    pub struct SetLit<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_set_lit<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SetLit>,
    ) -> Result<SetLit<V>, V::Error> {
        Ok(SetLit {
            elements: V::try_collect_items(
                ctx,
                node.elements.iter().map(|e| visitor.visit_expr(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct MapLitEntry<V: AstVisitor> {
        pub key: V::ExprRet,
        pub value: V::ExprRet,
    }

    pub fn walk_map_lit_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapLitEntry>,
    ) -> Result<MapLitEntry<V>, V::Error> {
        Ok(MapLitEntry {
            key: visitor.visit_expr(ctx, node.key.ast_ref())?,
            value: visitor.visit_expr(ctx, node.value.ast_ref())?,
        })
    }

    pub struct MapLit<V: AstVisitor> {
        pub entries: V::CollectionContainer<V::MapLitEntryRet>,
    }

    pub fn walk_map_lit<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapLit>,
    ) -> Result<MapLit<V>, V::Error> {
        Ok(MapLit {
            entries: V::try_collect_items(
                ctx,
                node.elements.iter().map(|e| visitor.visit_map_lit_entry(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct ListLit<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_list_lit<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListLit>,
    ) -> Result<ListLit<V>, V::Error> {
        Ok(ListLit {
            elements: V::try_collect_items(
                ctx,
                node.elements.iter().map(|e| visitor.visit_expr(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct TupleLitEntry<V: AstVisitor> {
        pub name: Option<V::NameRet>,
        pub ty: Option<V::TyRet>,
        pub value: V::ExprRet,
    }

    pub fn walk_tuple_lit_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleLitEntry>,
    ) -> Result<TupleLitEntry<V>, V::Error> {
        Ok(TupleLitEntry {
            name: node.name.as_ref().map(|t| visitor.visit_name(ctx, t.ast_ref())).transpose()?,
            ty: node.ty.as_ref().map(|t| visitor.visit_ty(ctx, t.ast_ref())).transpose()?,
            value: visitor.visit_expr(ctx, node.value.ast_ref())?,
        })
    }

    pub struct TupleLit<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::TupleLitEntryRet>,
    }

    pub fn walk_tuple_lit<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleLit>,
    ) -> Result<TupleLit<V>, V::Error> {
        Ok(TupleLit {
            elements: V::try_collect_items(
                ctx,
                node.elements.iter().map(|e| visitor.visit_tuple_lit_entry(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct TyArg<V: AstVisitor> {
        pub ty: V::TyRet,
        pub name: Option<V::NameRet>,
    }

    pub fn walk_ty_arg<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TyArg>,
    ) -> Result<TyArg<V>, V::Error> {
        Ok(TyArg {
            ty: visitor.visit_ty(ctx, node.ty.ast_ref())?,
            name: node.name.as_ref().map(|t| visitor.visit_name(ctx, t.ast_ref())).transpose()?,
        })
    }

    pub struct FnTy<V: AstVisitor> {
        pub params: V::CollectionContainer<V::TyArgRet>,
        pub return_ty: V::TyRet,
    }

    pub fn walk_fn_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::FnTy>,
    ) -> Result<FnTy<V>, V::Error> {
        Ok(FnTy {
            params: V::try_collect_items(
                ctx,
                node.params.iter().map(|e| visitor.visit_ty_arg(ctx, e.ast_ref())),
            )?,
            return_ty: visitor.visit_ty(ctx, node.return_ty.ast_ref())?,
        })
    }

    pub struct TupleTy<V: AstVisitor> {
        pub entries: V::CollectionContainer<V::TyArgRet>,
    }

    pub fn walk_tuple_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TupleTy>,
    ) -> Result<TupleTy<V>, V::Error> {
        Ok(TupleTy {
            entries: V::try_collect_items(
                ctx,
                node.entries.iter().map(|e| visitor.visit_ty_arg(ctx, e.ast_ref())),
            )?,
        })
    }

    pub struct ListTy<V: AstVisitor> {
        pub inner: V::TyRet,
    }

    pub fn walk_list_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListTy>,
    ) -> Result<ListTy<V>, V::Error> {
        Ok(ListTy { inner: visitor.visit_ty(ctx, node.inner.ast_ref())? })
    }

    pub struct SetTy<V: AstVisitor> {
        pub inner: V::TyRet,
    }

    pub fn walk_set_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SetTy>,
    ) -> Result<SetTy<V>, V::Error> {
        Ok(SetTy { inner: visitor.visit_ty(ctx, node.inner.ast_ref())? })
    }

    pub struct MapTy<V: AstVisitor> {
        pub key: V::TyRet,
        pub value: V::TyRet,
    }

    pub fn walk_map_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MapTy>,
    ) -> Result<MapTy<V>, V::Error> {
        Ok(MapTy {
            key: visitor.visit_ty(ctx, node.key.ast_ref())?,
            value: visitor.visit_ty(ctx, node.value.ast_ref())?,
        })
    }

    pub struct NamedTy<V: AstVisitor> {
        pub name: V::NameRet,
    }

    pub fn walk_named_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::NamedTy>,
    ) -> Result<NamedTy<V>, V::Error> {
        Ok(NamedTy { name: visitor.visit_name(ctx, node.name.ast_ref())? })
    }

    pub struct AccessTy<V: AstVisitor> {
        pub subject: V::TyRet,
        pub property: V::NameRet,
    }

    pub fn walk_access_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AccessTy>,
    ) -> Result<AccessTy<V>, V::Error> {
        Ok(AccessTy {
            subject: visitor.visit_ty(ctx, node.subject.ast_ref())?,
            property: visitor.visit_name(ctx, node.property.ast_ref())?,
        })
    }

    pub struct RefTy<V: AstVisitor> {
        pub inner: V::TyRet,
        pub mutability: Option<V::MutabilityRet>,
        pub kind: Option<V::RefKindRet>,
    }

    pub fn walk_ref_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::RefTy>,
    ) -> Result<RefTy<V>, V::Error> {
        Ok(RefTy {
            inner: visitor.visit_ty(ctx, node.inner.ast_ref())?,
            kind: node
                .kind
                .as_ref()
                .map(|inner| visitor.visit_ref_kind(ctx, inner.ast_ref()))
                .transpose()?,
            mutability: node
                .mutability
                .as_ref()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref()))
                .transpose()?,
        })
    }

    pub struct MergeTy<V: AstVisitor> {
        pub lhs: V::TyRet,
        pub rhs: V::TyRet,
    }

    pub fn walk_merge_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MergeTy>,
    ) -> Result<MergeTy<V>, V::Error> {
        Ok(MergeTy {
            lhs: visitor.visit_ty(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_ty(ctx, node.rhs.ast_ref())?,
        })
    }

    pub struct UnionTy<V: AstVisitor> {
        pub lhs: V::TyRet,
        pub rhs: V::TyRet,
    }

    pub fn walk_union_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::UnionTy>,
    ) -> Result<UnionTy<V>, V::Error> {
        Ok(UnionTy {
            lhs: visitor.visit_ty(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_ty(ctx, node.rhs.ast_ref())?,
        })
    }
    pub struct TyFnCall<V: AstVisitor> {
        pub subject: V::ExprRet,
        pub args: V::CollectionContainer<V::TyArgRet>,
    }

    pub fn walk_ty_fn_call<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TyFnCall>,
    ) -> Result<TyFnCall<V>, V::Error> {
        Ok(TyFnCall {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref())?,
            args: V::try_collect_items(
                ctx,
                node.args.iter().map(|a| visitor.visit_ty_arg(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct TyFn<V: AstVisitor> {
        pub params: V::CollectionContainer<V::ParamRet>,
        pub return_ty: V::TyRet,
    }

    pub fn walk_ty_fn<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TyFn>,
    ) -> Result<TyFn<V>, V::Error> {
        Ok(TyFn {
            params: V::try_collect_items(
                ctx,
                node.params.iter().map(|a| visitor.visit_param(ctx, a.ast_ref())),
            )?,
            return_ty: visitor.visit_ty(ctx, node.return_ty.ast_ref())?,
        })
    }

    pub enum Ty<V: AstVisitor> {
        Access(V::AccessTyRet),
        Fn(V::FnTyRet),
        Tuple(V::TupleTyRet),
        List(V::ListTyRet),
        Set(V::SetTyRet),
        Map(V::MapTyRet),
        Named(V::NamedTyRet),
        Ref(V::RefTyRet),
        Merge(V::MergeTyRet),
        Union(V::UnionTyRet),
        TyFn(V::TyFnRet),
        TyFnCall(V::TyFnCallRet),
    }

    pub fn walk_ty<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Ty>,
    ) -> Result<Ty<V>, V::Error> {
        Ok(match &*node {
            ast::Ty::Access(r) => Ty::Access(visitor.visit_access_ty(ctx, node.with_body(r))?),
            ast::Ty::Fn(r) => Ty::Fn(visitor.visit_fn_ty(ctx, node.with_body(r))?),
            ast::Ty::Tuple(r) => Ty::Tuple(visitor.visit_tuple_ty(ctx, node.with_body(r))?),
            ast::Ty::List(r) => Ty::List(visitor.visit_list_ty(ctx, node.with_body(r))?),
            ast::Ty::Set(r) => Ty::Set(visitor.visit_set_ty(ctx, node.with_body(r))?),
            ast::Ty::Map(r) => Ty::Map(visitor.visit_map_ty(ctx, node.with_body(r))?),
            ast::Ty::Named(r) => Ty::Named(visitor.visit_named_ty(ctx, node.with_body(r))?),
            ast::Ty::Ref(r) => Ty::Ref(visitor.visit_ref_ty(ctx, node.with_body(r))?),
            ast::Ty::Merge(r) => Ty::Merge(visitor.visit_merge_ty(ctx, node.with_body(r))?),
            ast::Ty::Union(r) => Ty::Union(visitor.visit_union_ty(ctx, node.with_body(r))?),
            ast::Ty::TyFn(r) => Ty::TyFn(visitor.visit_ty_fn_ty(ctx, node.with_body(r))?),
            ast::Ty::TyFnCall(r) => Ty::TyFnCall(visitor.visit_ty_fn_call(ctx, node.with_body(r))?),
        })
    }

    pub fn walk_ty_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Ty>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            AccessTyRet = Ret,
            FnTyRet = Ret,
            TupleTyRet = Ret,
            ListTyRet = Ret,
            SetTyRet = Ret,
            MapTyRet = Ret,
            NamedTyRet = Ret,
            RefTyRet = Ret,
            MergeTyRet = Ret,
            UnionTyRet = Ret,
            TyFnRet = Ret,
            TyFnCallRet = Ret,
        >,
    {
        Ok(match walk_ty(visitor, ctx, node)? {
            Ty::Access(r) => r,
            Ty::Fn(r) => r,
            Ty::Tuple(r) => r,
            Ty::List(r) => r,
            Ty::Set(r) => r,
            Ty::Map(r) => r,
            Ty::Named(r) => r,
            Ty::Ref(r) => r,
            Ty::Merge(r) => r,
            Ty::Union(r) => r,
            Ty::TyFn(r) => r,
            Ty::TyFnCall(r) => r,
        })
    }

    pub enum Pat<V: AstVisitor> {
        Access(V::AccessPatRet),
        Constructor(V::ConstructorPatRet),
        Module(V::ModulePatRet),
        Tuple(V::TuplePatRet),
        List(V::ListPatRet),
        Lit(V::LitPatRet),
        Or(V::OrPatRet),
        If(V::IfPatRet),
        Binding(V::BindingPatRet),
        Spread(V::SpreadPatRet),
        Wild(V::WildPatRet),
    }

    pub fn walk_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Pat>,
    ) -> Result<Pat<V>, V::Error> {
        Ok(match &*node {
            ast::Pat::Access(r) => Pat::Access(visitor.visit_access_pat(ctx, node.with_body(r))?),
            ast::Pat::Constructor(r) => {
                Pat::Constructor(visitor.visit_constructor_pat(ctx, node.with_body(r))?)
            }
            ast::Pat::Module(r) => Pat::Module(visitor.visit_module_pat(ctx, node.with_body(r))?),
            ast::Pat::Tuple(r) => Pat::Tuple(visitor.visit_tuple_pat(ctx, node.with_body(r))?),
            ast::Pat::List(r) => Pat::List(visitor.visit_list_pat(ctx, node.with_body(r))?),
            ast::Pat::Lit(r) => Pat::Lit(visitor.visit_lit_pat(ctx, node.with_body(r))?),
            ast::Pat::Or(r) => Pat::Or(visitor.visit_or_pat(ctx, node.with_body(r))?),
            ast::Pat::If(r) => Pat::If(visitor.visit_if_pat(ctx, node.with_body(r))?),
            ast::Pat::Binding(r) => {
                Pat::Binding(visitor.visit_binding_pat(ctx, node.with_body(r))?)
            }
            ast::Pat::Spread(r) => Pat::Spread(visitor.visit_spread_pat(ctx, node.with_body(r))?),
            ast::Pat::Wild(r) => Pat::Wild(visitor.visit_wild_pat(ctx, node.with_body(r))?),
        })
    }

    pub fn walk_pat_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Pat>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitor<
            AccessPatRet = Ret,
            ConstructorPatRet = Ret,
            ModulePatRet = Ret,
            TuplePatRet = Ret,
            ListPatRet = Ret,
            LitPatRet = Ret,
            OrPatRet = Ret,
            IfPatRet = Ret,
            BindingPatRet = Ret,
            SpreadPatRet = Ret,
            WildPatRet = Ret,
        >,
    {
        Ok(match walk_pat(visitor, ctx, node)? {
            Pat::Access(r) => r,
            Pat::Constructor(r) => r,
            Pat::Module(r) => r,
            Pat::Tuple(r) => r,
            Pat::List(r) => r,
            Pat::Lit(r) => r,
            Pat::Or(r) => r,
            Pat::If(r) => r,
            Pat::Binding(r) => r,
            Pat::Spread(r) => r,
            Pat::Wild(r) => r,
        })
    }

    pub struct OrPat<V: AstVisitor> {
        pub variants: V::CollectionContainer<V::PatRet>,
    }
    pub fn walk_or_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::OrPat>,
    ) -> Result<OrPat<V>, V::Error> {
        Ok(OrPat {
            variants: V::try_collect_items(
                ctx,
                node.variants.iter().map(|v| visitor.visit_pat(ctx, v.ast_ref())),
            )?,
        })
    }

    pub struct AccessPat<V: AstVisitor> {
        pub subject: V::PatRet,
        pub property: V::NameRet,
    }

    pub fn walk_access_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AccessPat>,
    ) -> Result<AccessPat<V>, V::Error> {
        Ok(AccessPat {
            subject: visitor.visit_pat(ctx, node.subject.ast_ref())?,
            property: visitor.visit_name(ctx, node.property.ast_ref())?,
        })
    }

    pub struct ConstructorPat<V: AstVisitor> {
        pub subject: V::PatRet,
        pub args: V::CollectionContainer<V::TuplePatEntryRet>,
    }
    pub fn walk_constructor_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ConstructorPat>,
    ) -> Result<ConstructorPat<V>, V::Error> {
        Ok(ConstructorPat {
            subject: visitor.visit_pat(ctx, node.subject.ast_ref())?,
            args: V::try_collect_items(
                ctx,
                node.fields.iter().map(|a| visitor.visit_tuple_pat_entry(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct ModulePat<V: AstVisitor> {
        pub fields: V::CollectionContainer<V::ModulePatEntryRet>,
    }
    pub fn walk_module_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ModulePat>,
    ) -> Result<ModulePat<V>, V::Error> {
        Ok(ModulePat {
            fields: V::try_collect_items(
                ctx,
                node.fields.iter().map(|a| visitor.visit_module_pat_entry(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct TuplePatEntry<V: AstVisitor> {
        pub name: Option<V::NameRet>,
        pub pat: V::PatRet,
    }

    pub fn walk_tuple_pat_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TuplePatEntry>,
    ) -> Result<TuplePatEntry<V>, V::Error> {
        Ok(TuplePatEntry {
            name: node.name.as_ref().map(|t| visitor.visit_name(ctx, t.ast_ref())).transpose()?,
            pat: visitor.visit_pat(ctx, node.pat.ast_ref())?,
        })
    }

    pub struct TuplePat<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::TuplePatEntryRet>,
    }

    pub fn walk_tuple_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TuplePat>,
    ) -> Result<TuplePat<V>, V::Error> {
        Ok(TuplePat {
            elements: V::try_collect_items(
                ctx,
                node.fields.iter().map(|a| visitor.visit_tuple_pat_entry(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct ListPat<V: AstVisitor> {
        pub elements: V::CollectionContainer<V::PatRet>,
    }

    pub fn walk_list_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ListPat>,
    ) -> Result<ListPat<V>, V::Error> {
        Ok(ListPat {
            elements: V::try_collect_items(
                ctx,
                node.fields.iter().map(|a| visitor.visit_pat(ctx, a.ast_ref())),
            )?,
        })
    }

    pub struct IfPat<V: AstVisitor> {
        pub pat: V::PatRet,
        pub condition: V::ExprRet,
    }
    pub fn walk_if_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::IfPat>,
    ) -> Result<IfPat<V>, V::Error> {
        Ok(IfPat {
            pat: visitor.visit_pat(ctx, node.pat.ast_ref())?,
            condition: visitor.visit_expr(ctx, node.condition.ast_ref())?,
        })
    }

    pub struct BindingPat<V: AstVisitor> {
        pub name: V::NameRet,
        pub visibility: Option<V::VisibilityRet>,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_binding_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BindingPat>,
    ) -> Result<BindingPat<V>, V::Error> {
        Ok(BindingPat {
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

    pub struct SpreadPat<V: AstVisitor> {
        pub name: Option<V::NameRet>,
    }

    pub fn walk_spread_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::SpreadPat>,
    ) -> Result<SpreadPat<V>, V::Error> {
        Ok(SpreadPat {
            name: node.name.as_ref().map(|t| visitor.visit_name(ctx, t.ast_ref())).transpose()?,
        })
    }

    pub struct LitPat<V: AstVisitor> {
        pub lit: V::LitRet,
    }

    pub fn walk_lit_pat<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::LitPat>,
    ) -> Result<LitPat<V>, V::Error> {
        Ok(LitPat { lit: visitor.visit_lit(ctx, node.lit.ast_ref())? })
    }

    pub struct ModulePatEntry<V: AstVisitor> {
        pub name: V::NameRet,
        pub pat: V::PatRet,
    }
    pub fn walk_module_pat_entry<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ModulePatEntry>,
    ) -> Result<ModulePatEntry<V>, V::Error> {
        Ok(ModulePatEntry {
            name: visitor.visit_name(ctx, node.name.ast_ref())?,
            pat: visitor.visit_pat(ctx, node.pat.ast_ref())?,
        })
    }

    pub struct ReturnStatement<V: AstVisitor>(pub Option<V::ExprRet>);
    pub fn walk_return_statement<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::ReturnStatement>,
    ) -> Result<ReturnStatement<V>, V::Error> {
        Ok(ReturnStatement(
            node.0.as_ref().map(|n| visitor.visit_expr(ctx, n.ast_ref())).transpose()?,
        ))
    }

    pub struct Declaration<V: AstVisitor> {
        pub pat: V::PatRet,
        pub ty: Option<V::TyRet>,
        pub value: Option<V::ExprRet>,
    }

    pub fn walk_declaration<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Declaration<V>, V::Error> {
        Ok(Declaration {
            pat: visitor.visit_pat(ctx, node.pat.ast_ref())?,
            ty: node.ty.as_ref().map(|t| visitor.visit_ty(ctx, t.ast_ref())).transpose()?,
            value: node.value.as_ref().map(|t| visitor.visit_expr(ctx, t.ast_ref())).transpose()?,
        })
    }

    pub struct MergeDeclaration<V: AstVisitor> {
        pub decl: V::ExprRet,
        pub value: V::ExprRet,
    }

    pub fn walk_merge_declaration<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::MergeDeclaration>,
    ) -> Result<MergeDeclaration<V>, V::Error> {
        Ok(MergeDeclaration {
            decl: visitor.visit_expr(ctx, node.decl.ast_ref())?,
            value: visitor.visit_expr(ctx, node.value.ast_ref())?,
        })
    }

    pub struct AssignExpr<V: AstVisitor> {
        pub lhs: V::ExprRet,
        pub rhs: V::ExprRet,
    }

    pub fn walk_assign_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AssignExpr>,
    ) -> Result<AssignExpr<V>, V::Error> {
        Ok(AssignExpr {
            lhs: visitor.visit_expr(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_expr(ctx, node.rhs.ast_ref())?,
        })
    }

    pub struct AssignOpStatement<V: AstVisitor> {
        pub lhs: V::ExprRet,
        pub rhs: V::ExprRet,
        pub operator: V::BinaryOperatorRet,
    }
    pub fn walk_assign_op_statement<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::AssignOpExpr>,
    ) -> Result<AssignOpStatement<V>, V::Error> {
        Ok(AssignOpStatement {
            lhs: visitor.visit_expr(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_expr(ctx, node.rhs.ast_ref())?,
            operator: visitor.visit_binary_operator(ctx, node.operator.ast_ref())?,
        })
    }

    pub struct BinaryExpr<V: AstVisitor> {
        pub lhs: V::ExprRet,
        pub rhs: V::ExprRet,
        pub operator: V::BinaryOperatorRet,
    }
    pub fn walk_binary_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::BinaryExpr>,
    ) -> Result<BinaryExpr<V>, V::Error> {
        Ok(BinaryExpr {
            lhs: visitor.visit_expr(ctx, node.lhs.ast_ref())?,
            rhs: visitor.visit_expr(ctx, node.rhs.ast_ref())?,
            operator: visitor.visit_binary_operator(ctx, node.operator.ast_ref())?,
        })
    }

    pub struct UnaryExpr<V: AstVisitor> {
        pub expr: V::ExprRet,
        pub operator: V::UnaryOperatorRet,
    }

    pub fn walk_unary_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::UnaryExpr>,
    ) -> Result<UnaryExpr<V>, V::Error> {
        Ok(UnaryExpr {
            expr: visitor.visit_expr(ctx, node.expr.ast_ref())?,
            operator: visitor.visit_unary_operator(ctx, node.operator.ast_ref())?,
        })
    }

    pub struct IndexExpr<V: AstVisitor> {
        pub subject: V::ExprRet,
        pub index_expr: V::ExprRet,
    }

    pub fn walk_index_expr<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::IndexExpr>,
    ) -> Result<IndexExpr<V>, V::Error> {
        Ok(IndexExpr {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref())?,
            index_expr: visitor.visit_expr(ctx, node.index_expr.ast_ref())?,
        })
    }

    pub struct StructDef<V: AstVisitor> {
        pub entries: V::CollectionContainer<V::ParamRet>,
    }
    pub fn walk_struct_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<StructDef<V>, V::Error> {
        Ok(StructDef {
            entries: V::try_collect_items(
                ctx,
                node.entries.iter().map(|b| visitor.visit_param(ctx, b.ast_ref())),
            )?,
        })
    }

    pub struct EnumDefEntry<V: AstVisitor> {
        pub name: V::NameRet,
        pub args: V::CollectionContainer<V::TyRet>,
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
                node.args.iter().map(|b| visitor.visit_ty(ctx, b.ast_ref())),
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
                node.entries.iter().map(|b| visitor.visit_enum_def_entry(ctx, b.ast_ref())),
            )?,
        })
    }

    pub struct TyFnDef<V: AstVisitor> {
        pub params: V::CollectionContainer<V::ParamRet>,
        pub return_ty: Option<V::TyRet>,
        pub body: V::ExprRet,
    }

    pub fn walk_ty_fn_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TyFnDef>,
    ) -> Result<TyFnDef<V>, V::Error> {
        Ok(TyFnDef {
            params: V::try_collect_items(
                ctx,
                node.params.iter().map(|t| visitor.visit_param(ctx, t.ast_ref())),
            )?,
            return_ty: node
                .return_ty
                .as_ref()
                .map(|t| visitor.visit_ty(ctx, t.ast_ref()))
                .transpose()?,
            body: visitor.visit_expr(ctx, node.body.ast_ref())?,
        })
    }

    pub struct TraitDef<V: AstVisitor> {
        pub members: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_trait_def<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<TraitDef<V>, V::Error> {
        Ok(TraitDef {
            members: V::try_collect_items(
                ctx,
                node.members.iter().map(|t| visitor.visit_expr(ctx, t.ast_ref())),
            )?,
        })
    }

    pub struct TraitImpl<V: AstVisitor> {
        pub ty: V::TyRet,
        pub implementation: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_trait_impl<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::TraitImpl>,
    ) -> Result<TraitImpl<V>, V::Error> {
        Ok(TraitImpl {
            ty: visitor.visit_ty(ctx, node.ty.ast_ref())?,
            implementation: V::try_collect_items(
                ctx,
                node.implementation.iter().map(|t| visitor.visit_expr(ctx, t.ast_ref())),
            )?,
        })
    }

    pub struct Module<V: AstVisitor> {
        pub contents: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_module<V: AstVisitor>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Module<V>, V::Error> {
        Ok(Module {
            contents: V::try_collect_items(
                ctx,
                node.contents.iter().map(|s| visitor.visit_expr(ctx, s.ast_ref())),
            )?,
        })
    }
}

pub mod walk_mut {
    use super::{ast, AstVisitorMut};
    use crate::ast::AstNodeRefMut;

    pub struct Param<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub ty: Option<V::TyRet>,
        pub default: Option<V::ExprRet>,
    }

    pub fn walk_param<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Param>,
    ) -> Result<Param<V>, V::Error> {
        Ok(Param {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            ty: node.ty.as_mut().map(|t| visitor.visit_ty(ctx, t.ast_ref_mut())).transpose()?,
            default: node
                .default
                .as_mut()
                .map(|t| visitor.visit_expr(ctx, t.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct FnDef<V: AstVisitorMut> {
        pub params: V::CollectionContainer<V::ParamRet>,
        pub return_ty: Option<V::TyRet>,
        pub fn_body: V::ExprRet,
    }

    pub fn walk_fn_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::FnDef>,
    ) -> Result<FnDef<V>, V::Error> {
        Ok(FnDef {
            params: V::try_collect_items(
                ctx,
                node.params.iter_mut().map(|a| visitor.visit_param(ctx, a.ast_ref_mut())),
            )?,
            return_ty: node
                .return_ty
                .as_mut()
                .map(|t| visitor.visit_ty(ctx, t.ast_ref_mut()))
                .transpose()?,
            fn_body: visitor.visit_expr(ctx, node.fn_body.ast_ref_mut())?,
        })
    }

    pub enum Expr<V: AstVisitorMut> {
        ConstructorCall(V::ConstructorCallExprRet),
        Directive(V::DirectiveExprRet),
        Declaration(V::DeclarationRet),
        Variable(V::VariableExprRet),
        Access(V::AccessExprRet),
        Ref(V::RefExprRet),
        Deref(V::DerefExprRet),
        Unsafe(V::UnsafeExprRet),
        LitExpr(V::LitExprRet),
        Cast(V::CastExprRet),
        Block(V::BlockExprRet),
        Import(V::ImportExprRet),
        StructDef(V::StructDefRet),
        EnumDef(V::EnumDefRet),
        TyFnDef(V::TyFnDefRet),
        TraitDef(V::TraitDefRet),
        FnDef(V::FnDefRet),
        Ty(V::TyExprRet),
        Return(V::ReturnStatementRet),
        Break(V::BreakStatementRet),
        Continue(V::ContinueStatementRet),
        Assign(V::AssignExprRet),
        AssignOp(V::AssignOpExprRet),
        MergeDeclaration(V::MergeDeclarationRet),
        TraitImpl(V::TraitImplRet),
        BinaryExpr(V::BinaryExprRet),
        UnaryExpr(V::UnaryExprRet),
        Index(V::IndexExprRet),
    }

    pub fn walk_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Expr>,
    ) -> Result<Expr<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut node.kind {
            ast::ExprKind::ConstructorCall(inner) => Expr::ConstructorCall(
                visitor.visit_constructor_call_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExprKind::Ty(inner) => {
                Expr::Ty(visitor.visit_ty_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExprKind::Directive(inner) => Expr::Directive(
                visitor.visit_directive_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExprKind::Declaration(inner) => Expr::Declaration(
                visitor.visit_declaration(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExprKind::MergeDeclaration(inner) => Expr::MergeDeclaration(
                visitor.visit_merge_declaration(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExprKind::Variable(inner) => Expr::Variable(
                visitor.visit_variable_expr(ctx, AstNodeRefMut::new(inner, span, id))?,
            ),
            ast::ExprKind::Access(inner) => Expr::Access({
                visitor.visit_access_expr(ctx, AstNodeRefMut::new(inner, span, id))?
            }),
            ast::ExprKind::Ref(inner) => {
                Expr::Ref(visitor.visit_ref_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExprKind::Deref(inner) => {
                Expr::Deref(visitor.visit_deref_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExprKind::Unsafe(inner) => {
                Expr::Unsafe(visitor.visit_unsafe_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExprKind::LitExpr(inner) => {
                Expr::LitExpr(visitor.visit_lit_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExprKind::Cast(inner) => {
                Expr::Cast(visitor.visit_cast_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExprKind::Block(inner) => {
                Expr::Block(visitor.visit_block_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExprKind::Import(inner) => {
                Expr::Import(visitor.visit_import_expr(ctx, AstNodeRefMut::new(inner, span, id))?)
            }
            ast::ExprKind::StructDef(r) => {
                Expr::StructDef(visitor.visit_struct_def(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::EnumDef(r) => {
                Expr::EnumDef(visitor.visit_enum_def(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::TyFnDef(r) => {
                Expr::TyFnDef(visitor.visit_ty_fn_def(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::TraitDef(r) => {
                Expr::TraitDef(visitor.visit_trait_def(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::FnDef(r) => {
                Expr::FnDef(visitor.visit_fn_def(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::Return(r) => {
                Expr::Return(visitor.visit_return_statement(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::Break(r) => {
                Expr::Break(visitor.visit_break_statement(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::Continue(r) => Expr::Continue(
                visitor.visit_continue_statement(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::ExprKind::Assign(r) => {
                Expr::Assign(visitor.visit_assign_expr(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::AssignOp(r) => {
                Expr::AssignOp(visitor.visit_assign_op_expr(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::TraitImpl(r) => {
                Expr::TraitImpl(visitor.visit_trait_impl(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::BinaryExpr(r) => {
                Expr::BinaryExpr(visitor.visit_binary_expr(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::UnaryExpr(r) => {
                Expr::UnaryExpr(visitor.visit_unary_expr(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::ExprKind::Index(r) => {
                Expr::Index(visitor.visit_index_expr(ctx, AstNodeRefMut::new(r, span, id))?)
            }
        })
    }

    pub fn walk_expr_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Expr>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            ConstructorCallExprRet = Ret,
            DirectiveExprRet = Ret,
            DeclarationRet = Ret,
            MergeDeclarationRet = Ret,
            VariableExprRet = Ret,
            AccessExprRet = Ret,
            RefExprRet = Ret,
            DerefExprRet = Ret,
            UnsafeExprRet = Ret,
            LitExprRet = Ret,
            CastExprRet = Ret,
            BlockExprRet = Ret,
            ImportExprRet = Ret,
            StructDefRet = Ret,
            EnumDefRet = Ret,
            TyFnDefRet = Ret,
            TraitDefRet = Ret,
            TraitImplRet = Ret,
            FnDefRet = Ret,
            TyExprRet = Ret,
            ReturnStatementRet = Ret,
            BreakStatementRet = Ret,
            ContinueStatementRet = Ret,
            AssignExprRet = Ret,
            AssignOpExprRet = Ret,
            BinaryExprRet = Ret,
            UnaryExprRet = Ret,
            IndexExprRet = Ret,
        >,
    {
        Ok(match walk_expr(visitor, ctx, node)? {
            Expr::ConstructorCall(r) => r,
            Expr::Directive(r) => r,
            Expr::Declaration(r) => r,
            Expr::MergeDeclaration(r) => r,
            Expr::Variable(r) => r,
            Expr::Access(r) => r,
            Expr::Ref(r) => r,
            Expr::Deref(r) => r,
            Expr::Unsafe(r) => r,
            Expr::LitExpr(r) => r,
            Expr::Cast(r) => r,
            Expr::Block(r) => r,
            Expr::Import(r) => r,
            Expr::StructDef(r) => r,
            Expr::EnumDef(r) => r,
            Expr::TyFnDef(r) => r,
            Expr::TraitDef(r) => r,
            Expr::TraitImpl(r) => r,
            Expr::FnDef(r) => r,
            Expr::Ty(r) => r,
            Expr::Return(r) => r,
            Expr::Break(r) => r,
            Expr::Continue(r) => r,
            Expr::Assign(r) => r,
            Expr::AssignOp(r) => r,
            Expr::BinaryExpr(r) => r,
            Expr::UnaryExpr(r) => r,
            Expr::Index(r) => r,
        })
    }

    pub struct VariableExpr<V: AstVisitorMut> {
        pub name: V::NameRet,
    }

    pub fn walk_variable_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::VariableExpr>,
    ) -> Result<VariableExpr<V>, V::Error> {
        Ok(VariableExpr { name: visitor.visit_name(ctx, node.name.ast_ref_mut())? })
    }

    pub struct DirectiveExpr<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub subject: V::ExprRet,
    }

    pub fn walk_directive_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::DirectiveExpr>,
    ) -> Result<DirectiveExpr<V>, V::Error> {
        Ok(DirectiveExpr {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            subject: visitor.visit_expr(ctx, node.subject.ast_ref_mut())?,
        })
    }

    pub struct ConstructorCallArg<V: AstVisitorMut> {
        pub name: Option<V::NameRet>,
        pub value: V::ExprRet,
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
            value: visitor.visit_expr(ctx, node.value.ast_ref_mut())?,
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

    pub struct ConstructorCallExpr<V: AstVisitorMut> {
        pub subject: V::ExprRet,
        pub args: V::ConstructorCallArgsRet,
    }

    pub fn walk_constructor_call_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ConstructorCallExpr>,
    ) -> Result<ConstructorCallExpr<V>, V::Error> {
        Ok(ConstructorCallExpr {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref_mut())?,
            args: visitor.visit_constructor_call_args(ctx, node.args.ast_ref_mut())?,
        })
    }

    pub struct AccessExpr<V: AstVisitorMut> {
        pub subject: V::ExprRet,
        pub property: V::NameRet,
    }

    pub fn walk_access_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::AccessExpr>,
    ) -> Result<AccessExpr<V>, V::Error> {
        Ok(AccessExpr {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref_mut())?,
            property: visitor.visit_name(ctx, node.property.ast_ref_mut())?,
        })
    }

    pub struct RefExpr<V: AstVisitorMut> {
        pub inner_expr: V::ExprRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::RefExpr>,
    ) -> Result<RefExpr<V>, V::Error> {
        Ok(RefExpr {
            inner_expr: visitor.visit_expr(ctx, node.inner_expr.ast_ref_mut())?,
            mutability: node
                .mutability
                .as_mut()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct DerefExpr<V: AstVisitorMut>(pub V::ExprRet);

    pub fn walk_deref_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::DerefExpr>,
    ) -> Result<DerefExpr<V>, V::Error> {
        Ok(DerefExpr(visitor.visit_expr(ctx, node.0.ast_ref_mut())?))
    }

    pub struct UnsafeExpr<V: AstVisitorMut>(pub V::ExprRet);

    pub fn walk_unsafe_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::UnsafeExpr>,
    ) -> Result<UnsafeExpr<V>, V::Error> {
        Ok(UnsafeExpr(visitor.visit_expr(ctx, node.0.ast_ref_mut())?))
    }

    pub struct LitExpr<V: AstVisitorMut>(pub V::LitRet);

    pub fn walk_lit_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::LitExpr>,
    ) -> Result<LitExpr<V>, V::Error> {
        Ok(LitExpr(visitor.visit_lit(ctx, node.0.ast_ref_mut())?))
    }

    pub struct CastExpr<V: AstVisitorMut> {
        pub expr: V::ExprRet,
        pub ty: V::TyRet,
    }

    pub fn walk_cast_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::CastExpr>,
    ) -> Result<CastExpr<V>, V::Error> {
        Ok(CastExpr {
            ty: visitor.visit_ty(ctx, node.ty.ast_ref_mut())?,
            expr: visitor.visit_expr(ctx, node.expr.ast_ref_mut())?,
        })
    }

    pub struct TyExpr<V: AstVisitorMut>(pub V::TyRet);

    pub fn walk_ty_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TyExpr>,
    ) -> Result<TyExpr<V>, V::Error> {
        Ok(TyExpr(visitor.visit_ty(ctx, node.0.ast_ref_mut())?))
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

    pub enum Lit<V: AstVisitorMut> {
        Str(V::StrLitRet),
        Char(V::CharLitRet),
        Int(V::IntLitRet),
        Float(V::FloatLitRet),
        Bool(V::BoolLitRet),
        Set(V::SetLitRet),
        Map(V::MapLitRet),
        List(V::ListLitRet),
        Tuple(V::TupleLitRet),
    }

    pub fn walk_lit<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Lit>,
    ) -> Result<Lit<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut *node {
            ast::Lit::Str(r) => {
                Lit::Str(visitor.visit_str_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Lit::Char(r) => {
                Lit::Char(visitor.visit_char_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Lit::Int(r) => {
                Lit::Int(visitor.visit_int_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Lit::Float(r) => {
                Lit::Float(visitor.visit_float_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Lit::Bool(r) => {
                Lit::Bool(visitor.visit_bool_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Lit::Set(r) => {
                Lit::Set(visitor.visit_set_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Lit::Map(r) => {
                Lit::Map(visitor.visit_map_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Lit::List(r) => {
                Lit::List(visitor.visit_list_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Lit::Tuple(r) => {
                Lit::Tuple(visitor.visit_tuple_lit(ctx, AstNodeRefMut::new(r, span, id))?)
            }
        })
    }

    pub fn walk_lit_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Lit>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            StrLitRet = Ret,
            CharLitRet = Ret,
            IntLitRet = Ret,
            FloatLitRet = Ret,
            BoolLitRet = Ret,
            SetLitRet = Ret,
            MapLitRet = Ret,
            ListLitRet = Ret,
            TupleLitRet = Ret,
        >,
    {
        Ok(match walk_lit(visitor, ctx, node)? {
            Lit::Str(r) => r,
            Lit::Char(r) => r,
            Lit::Int(r) => r,
            Lit::Float(r) => r,
            Lit::Bool(r) => r,
            Lit::Set(r) => r,
            Lit::Map(r) => r,
            Lit::List(r) => r,
            Lit::Tuple(r) => r,
        })
    }

    pub struct MatchCase<V: AstVisitorMut> {
        pub pat: V::PatRet,
        pub expr: V::ExprRet,
    }

    pub fn walk_match_case<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MatchCase>,
    ) -> Result<MatchCase<V>, V::Error> {
        Ok(MatchCase {
            pat: visitor.visit_pat(ctx, node.pat.ast_ref_mut())?,
            expr: visitor.visit_expr(ctx, node.expr.ast_ref_mut())?,
        })
    }

    pub struct MatchBlock<V: AstVisitorMut> {
        pub subject: V::ExprRet,
        pub cases: V::CollectionContainer<V::MatchCaseRet>,
    }

    pub fn walk_match_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MatchBlock>,
    ) -> Result<MatchBlock<V>, V::Error> {
        Ok(MatchBlock {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref_mut())?,
            cases: V::try_collect_items(
                ctx,
                node.cases.iter_mut().map(|c| visitor.visit_match_case(ctx, c.ast_ref_mut())),
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
        pub pat: V::PatRet,
        pub iterator: V::ExprRet,
        pub body: V::BlockRet,
    }

    pub fn walk_for_loop_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ForLoopBlock>,
    ) -> Result<ForLoopBlock<V>, V::Error> {
        Ok(ForLoopBlock {
            pat: visitor.visit_pat(ctx, node.pat.ast_ref_mut())?,
            iterator: visitor.visit_expr(ctx, node.iterator.ast_ref_mut())?,
            body: visitor.visit_block(ctx, node.body.ast_ref_mut())?,
        })
    }

    pub struct WhileLoopBlock<V: AstVisitorMut> {
        pub condition: V::ExprRet,
        pub body: V::BlockRet,
    }

    pub fn walk_while_loop_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::WhileLoopBlock>,
    ) -> Result<WhileLoopBlock<V>, V::Error> {
        Ok(WhileLoopBlock {
            condition: visitor.visit_expr(ctx, node.condition.ast_ref_mut())?,
            body: visitor.visit_block(ctx, node.body.ast_ref_mut())?,
        })
    }

    pub struct ModBlock<V: AstVisitorMut>(pub V::BodyBlockRet);

    pub fn walk_mod_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ModBlock>,
    ) -> Result<ModBlock<V>, V::Error> {
        Ok(ModBlock(visitor.visit_body_block(ctx, node.0.ast_ref_mut())?))
    }

    pub struct ImplBlock<V: AstVisitorMut>(pub V::BodyBlockRet);

    pub fn walk_impl_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ImplBlock>,
    ) -> Result<ImplBlock<V>, V::Error> {
        Ok(ImplBlock(visitor.visit_body_block(ctx, node.0.ast_ref_mut())?))
    }

    pub struct IfClause<V: AstVisitorMut> {
        pub condition: V::ExprRet,
        pub body: V::BlockRet,
    }

    pub fn walk_if_clause<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::IfClause>,
    ) -> Result<IfClause<V>, V::Error> {
        Ok(IfClause {
            condition: visitor.visit_expr(ctx, node.condition.ast_ref_mut())?,
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
        pub statements: V::CollectionContainer<V::ExprRet>,
        pub expr: Option<V::ExprRet>,
    }

    pub fn walk_body_block<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::BodyBlock>,
    ) -> Result<BodyBlock<V>, V::Error> {
        Ok(BodyBlock {
            statements: V::try_collect_items(
                ctx,
                node.statements.iter_mut().map(|s| visitor.visit_expr(ctx, s.ast_ref_mut())),
            )?,
            expr: node
                .expr
                .as_mut()
                .map(|e| visitor.visit_expr(ctx, e.ast_ref_mut()))
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

    pub struct SetLit<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_set_lit<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::SetLit>,
    ) -> Result<SetLit<V>, V::Error> {
        Ok(SetLit {
            elements: V::try_collect_items(
                ctx,
                node.elements.iter_mut().map(|e| visitor.visit_expr(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct MapLitEntry<V: AstVisitorMut> {
        pub key: V::ExprRet,
        pub value: V::ExprRet,
    }

    pub fn walk_map_lit_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MapLitEntry>,
    ) -> Result<MapLitEntry<V>, V::Error> {
        Ok(MapLitEntry {
            key: visitor.visit_expr(ctx, node.key.ast_ref_mut())?,
            value: visitor.visit_expr(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct MapLit<V: AstVisitorMut> {
        pub entries: V::CollectionContainer<V::MapLitEntryRet>,
    }

    pub fn walk_map_lit<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MapLit>,
    ) -> Result<MapLit<V>, V::Error> {
        Ok(MapLit {
            entries: V::try_collect_items(
                ctx,
                node.elements.iter_mut().map(|e| visitor.visit_map_lit_entry(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct ListLit<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_list_lit<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ListLit>,
    ) -> Result<ListLit<V>, V::Error> {
        Ok(ListLit {
            elements: V::try_collect_items(
                ctx,
                node.elements.iter_mut().map(|e| visitor.visit_expr(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct TupleLitEntry<V: AstVisitorMut> {
        pub name: Option<V::NameRet>,
        pub ty: Option<V::TyRet>,
        pub value: V::ExprRet,
    }

    pub fn walk_tuple_lit_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TupleLitEntry>,
    ) -> Result<TupleLitEntry<V>, V::Error> {
        Ok(TupleLitEntry {
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
            ty: node.ty.as_mut().map(|t| visitor.visit_ty(ctx, t.ast_ref_mut())).transpose()?,
            value: visitor.visit_expr(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct TupleLit<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::TupleLitEntryRet>,
    }

    pub fn walk_tuple_lit<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TupleLit>,
    ) -> Result<TupleLit<V>, V::Error> {
        Ok(TupleLit {
            elements: V::try_collect_items(
                ctx,
                node.elements
                    .iter_mut()
                    .map(|e| visitor.visit_tuple_lit_entry(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct TyArg<V: AstVisitorMut> {
        pub ty: V::TyRet,
        pub name: Option<V::NameRet>,
    }

    pub fn walk_ty_arg<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TyArg>,
    ) -> Result<TyArg<V>, V::Error> {
        Ok(TyArg {
            ty: visitor.visit_ty(ctx, node.ty.ast_ref_mut())?,
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct FnTy<V: AstVisitorMut> {
        pub params: V::CollectionContainer<V::TyArgRet>,
        pub return_ty: V::TyRet,
    }

    pub fn walk_fn_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::FnTy>,
    ) -> Result<FnTy<V>, V::Error> {
        Ok(FnTy {
            params: V::try_collect_items(
                ctx,
                node.params.iter_mut().map(|e| visitor.visit_ty_arg(ctx, e.ast_ref_mut())),
            )?,
            return_ty: visitor.visit_ty(ctx, node.return_ty.ast_ref_mut())?,
        })
    }

    pub struct TupleTy<V: AstVisitorMut> {
        pub entries: V::CollectionContainer<V::TyArgRet>,
    }

    pub fn walk_tuple_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TupleTy>,
    ) -> Result<TupleTy<V>, V::Error> {
        Ok(TupleTy {
            entries: V::try_collect_items(
                ctx,
                node.entries.iter_mut().map(|e| visitor.visit_ty_arg(ctx, e.ast_ref_mut())),
            )?,
        })
    }

    pub struct ListTy<V: AstVisitorMut> {
        pub inner: V::TyRet,
    }

    pub fn walk_list_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ListTy>,
    ) -> Result<ListTy<V>, V::Error> {
        Ok(ListTy { inner: visitor.visit_ty(ctx, node.inner.ast_ref_mut())? })
    }

    pub struct SetTy<V: AstVisitorMut> {
        pub inner: V::TyRet,
    }

    pub fn walk_set_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::SetTy>,
    ) -> Result<SetTy<V>, V::Error> {
        Ok(SetTy { inner: visitor.visit_ty(ctx, node.inner.ast_ref_mut())? })
    }

    pub struct MapTy<V: AstVisitorMut> {
        pub key: V::TyRet,
        pub value: V::TyRet,
    }

    pub fn walk_map_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MapTy>,
    ) -> Result<MapTy<V>, V::Error> {
        Ok(MapTy {
            key: visitor.visit_ty(ctx, node.key.ast_ref_mut())?,
            value: visitor.visit_ty(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct NamedTy<V: AstVisitorMut> {
        pub name: V::NameRet,
    }

    pub fn walk_named_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::NamedTy>,
    ) -> Result<NamedTy<V>, V::Error> {
        Ok(NamedTy { name: visitor.visit_name(ctx, node.name.ast_ref_mut())? })
    }

    pub struct AccessTy<V: AstVisitorMut> {
        pub subject: V::TyRet,
        pub property: V::NameRet,
    }

    pub fn walk_access_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::AccessTy>,
    ) -> Result<AccessTy<V>, V::Error> {
        Ok(AccessTy {
            subject: visitor.visit_ty(ctx, node.subject.ast_ref_mut())?,
            property: visitor.visit_name(ctx, node.property.ast_ref_mut())?,
        })
    }

    pub struct RefTy<V: AstVisitorMut> {
        pub inner: V::TyRet,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_ref_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::RefTy>,
    ) -> Result<RefTy<V>, V::Error> {
        Ok(RefTy {
            inner: visitor.visit_ty(ctx, node.inner.ast_ref_mut())?,
            mutability: node
                .mutability
                .as_mut()
                .map(|inner| visitor.visit_mutability_modifier(ctx, inner.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct MergeTy<V: AstVisitorMut> {
        pub lhs: V::TyRet,
        pub rhs: V::TyRet,
    }

    pub fn walk_merge_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MergeTy>,
    ) -> Result<MergeTy<V>, V::Error> {
        Ok(MergeTy {
            lhs: visitor.visit_ty(ctx, node.lhs.ast_ref_mut())?,
            rhs: visitor.visit_ty(ctx, node.rhs.ast_ref_mut())?,
        })
    }

    pub struct UnionTy<V: AstVisitorMut> {
        pub lhs: V::TyRet,
        pub rhs: V::TyRet,
    }

    pub fn walk_union_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::UnionTy>,
    ) -> Result<UnionTy<V>, V::Error> {
        Ok(UnionTy {
            lhs: visitor.visit_ty(ctx, node.lhs.ast_ref_mut())?,
            rhs: visitor.visit_ty(ctx, node.rhs.ast_ref_mut())?,
        })
    }

    pub struct TyFnCall<V: AstVisitorMut> {
        pub subject: V::ExprRet,
        pub args: V::CollectionContainer<V::TyArgRet>,
    }

    pub fn walk_ty_fn_call<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TyFnCall>,
    ) -> Result<TyFnCall<V>, V::Error> {
        Ok(TyFnCall {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref_mut())?,
            args: V::try_collect_items(
                ctx,
                node.args.iter_mut().map(|a| visitor.visit_ty_arg(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct TyFn<V: AstVisitorMut> {
        pub params: V::CollectionContainer<V::ParamRet>,
        pub return_ty: V::TyRet,
    }

    pub fn walk_ty_fn<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TyFn>,
    ) -> Result<TyFn<V>, V::Error> {
        Ok(TyFn {
            params: V::try_collect_items(
                ctx,
                node.params.iter_mut().map(|a| visitor.visit_param(ctx, a.ast_ref_mut())),
            )?,
            return_ty: visitor.visit_ty(ctx, node.return_ty.ast_ref_mut())?,
        })
    }

    pub enum Ty<V: AstVisitorMut> {
        Access(V::AccessTyRet),
        Fn(V::FnTyRet),
        Tuple(V::TupleTyRet),
        List(V::ListTyRet),
        Set(V::SetTyRet),
        Map(V::MapTyRet),
        Named(V::NamedTyRet),
        Ref(V::RefTyRet),
        Merge(V::MergeTyRet),
        Union(V::UnionTyRet),
        TyFn(V::TyFnRet),
        TyFnCall(V::TyFnCallRet),
    }

    pub fn walk_ty<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Ty>,
    ) -> Result<Ty<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut *node {
            ast::Ty::Access(r) => {
                Ty::Access(visitor.visit_access_ty(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Ty::Fn(r) => Ty::Fn(visitor.visit_fn_ty(ctx, AstNodeRefMut::new(r, span, id))?),
            ast::Ty::Tuple(r) => {
                Ty::Tuple(visitor.visit_tuple_ty(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Ty::List(r) => {
                Ty::List(visitor.visit_list_ty(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Ty::Set(r) => Ty::Set(visitor.visit_set_ty(ctx, AstNodeRefMut::new(r, span, id))?),
            ast::Ty::Map(r) => Ty::Map(visitor.visit_map_ty(ctx, AstNodeRefMut::new(r, span, id))?),
            ast::Ty::Named(r) => {
                Ty::Named(visitor.visit_named_ty(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Ty::Ref(r) => Ty::Ref(visitor.visit_ref_ty(ctx, AstNodeRefMut::new(r, span, id))?),
            ast::Ty::Merge(r) => {
                Ty::Merge(visitor.visit_merge_ty(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Ty::Union(r) => {
                Ty::Union(visitor.visit_union_ty(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Ty::TyFn(r) => {
                Ty::TyFn(visitor.visit_ty_fn_ty(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Ty::TyFnCall(r) => {
                Ty::TyFnCall(visitor.visit_ty_fn_call(ctx, AstNodeRefMut::new(r, span, id))?)
            }
        })
    }

    pub fn walk_ty_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Ty>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            AccessTyRet = Ret,
            FnTyRet = Ret,
            TupleTyRet = Ret,
            ListTyRet = Ret,
            SetTyRet = Ret,
            MapTyRet = Ret,
            NamedTyRet = Ret,
            RefTyRet = Ret,
            MergeTyRet = Ret,
            UnionTyRet = Ret,
            TyFnRet = Ret,
            TyFnCallRet = Ret,
        >,
    {
        Ok(match walk_ty(visitor, ctx, node)? {
            Ty::Access(r) => r,
            Ty::Fn(r) => r,
            Ty::Tuple(r) => r,
            Ty::List(r) => r,
            Ty::Set(r) => r,
            Ty::Map(r) => r,
            Ty::Named(r) => r,
            Ty::Ref(r) => r,
            Ty::Merge(r) => r,
            Ty::Union(r) => r,
            Ty::TyFn(r) => r,
            Ty::TyFnCall(r) => r,
        })
    }

    pub enum Pat<V: AstVisitorMut> {
        Access(V::AccessPatRet),
        Constructor(V::ConstructorPatRet),
        Module(V::ModulePatRet),
        Tuple(V::TuplePatRet),
        List(V::ListPatRet),
        Lit(V::LitPatRet),
        Or(V::OrPatRet),
        If(V::IfPatRet),
        Binding(V::BindingPatRet),
        Spread(V::SpreadPatRet),
        Wild(V::WildPatRet),
    }

    pub fn walk_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Pat>,
    ) -> Result<Pat<V>, V::Error> {
        let span = node.span;
        let id = node.id;

        Ok(match &mut *node {
            ast::Pat::Access(r) => {
                Pat::Access(visitor.visit_access_pat(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pat::Constructor(r) => Pat::Constructor(
                visitor.visit_constructor_pat(ctx, AstNodeRefMut::new(r, span, id))?,
            ),
            ast::Pat::Module(r) => {
                Pat::Module(visitor.visit_module_pat(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pat::Tuple(r) => {
                Pat::Tuple(visitor.visit_tuple_pat(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pat::List(r) => {
                Pat::List(visitor.visit_list_pat(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pat::Lit(r) => {
                Pat::Lit(visitor.visit_lit_pat(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pat::Or(r) => Pat::Or(visitor.visit_or_pat(ctx, AstNodeRefMut::new(r, span, id))?),
            ast::Pat::If(r) => Pat::If(visitor.visit_if_pat(ctx, AstNodeRefMut::new(r, span, id))?),
            ast::Pat::Binding(r) => {
                Pat::Binding(visitor.visit_binding_pat(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pat::Spread(r) => {
                Pat::Spread(visitor.visit_spread_pat(ctx, AstNodeRefMut::new(r, span, id))?)
            }
            ast::Pat::Wild(r) => {
                Pat::Wild(visitor.visit_wild_pat(ctx, AstNodeRefMut::new(r, span, id))?)
            }
        })
    }

    pub fn walk_pat_same_children<V, Ret>(
        visitor: &mut V,
        ctx: &V::Ctx,
        node: ast::AstNodeRefMut<ast::Pat>,
    ) -> Result<Ret, V::Error>
    where
        V: AstVisitorMut<
            AccessPatRet = Ret,
            ConstructorPatRet = Ret,
            ModulePatRet = Ret,
            TuplePatRet = Ret,
            ListPatRet = Ret,
            LitPatRet = Ret,
            OrPatRet = Ret,
            IfPatRet = Ret,
            BindingPatRet = Ret,
            SpreadPatRet = Ret,
            WildPatRet = Ret,
        >,
    {
        Ok(match walk_pat(visitor, ctx, node)? {
            Pat::Access(r) => r,
            Pat::Constructor(r) => r,
            Pat::Module(r) => r,
            Pat::Tuple(r) => r,
            Pat::List(r) => r,
            Pat::Lit(r) => r,
            Pat::Or(r) => r,
            Pat::If(r) => r,
            Pat::Binding(r) => r,
            Pat::Spread(r) => r,
            Pat::Wild(r) => r,
        })
    }

    pub struct OrPat<V: AstVisitorMut> {
        pub variants: V::CollectionContainer<V::PatRet>,
    }
    pub fn walk_or_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::OrPat>,
    ) -> Result<OrPat<V>, V::Error> {
        Ok(OrPat {
            variants: V::try_collect_items(
                ctx,
                node.variants.iter_mut().map(|v| visitor.visit_pat(ctx, v.ast_ref_mut())),
            )?,
        })
    }

    pub struct ConstructorPat<V: AstVisitorMut> {
        pub subject: V::PatRet,
        pub args: V::CollectionContainer<V::TuplePatEntryRet>,
    }
    pub fn walk_constructor_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ConstructorPat>,
    ) -> Result<ConstructorPat<V>, V::Error> {
        Ok(ConstructorPat {
            subject: visitor.visit_pat(ctx, node.subject.ast_ref_mut())?,
            args: V::try_collect_items(
                ctx,
                node.fields.iter_mut().map(|a| visitor.visit_tuple_pat_entry(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct ModulePat<V: AstVisitorMut> {
        pub patterns: V::CollectionContainer<V::ModulePatEntryRet>,
    }
    pub fn walk_module_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ModulePat>,
    ) -> Result<ModulePat<V>, V::Error> {
        Ok(ModulePat {
            patterns: V::try_collect_items(
                ctx,
                node.fields
                    .iter_mut()
                    .map(|a| visitor.visit_module_pat_entry(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct TuplePatEntry<V: AstVisitorMut> {
        pub name: Option<V::NameRet>,
        pub pat: V::PatRet,
    }

    pub fn walk_tuple_pat_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TuplePatEntry>,
    ) -> Result<TuplePatEntry<V>, V::Error> {
        Ok(TuplePatEntry {
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
            pat: visitor.visit_pat(ctx, node.pat.ast_ref_mut())?,
        })
    }

    pub struct TuplePat<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::TuplePatEntryRet>,
    }

    pub fn walk_tuple_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TuplePat>,
    ) -> Result<TuplePat<V>, V::Error> {
        Ok(TuplePat {
            elements: V::try_collect_items(
                ctx,
                node.fields.iter_mut().map(|a| visitor.visit_tuple_pat_entry(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct ListPat<V: AstVisitorMut> {
        pub elements: V::CollectionContainer<V::PatRet>,
    }

    pub fn walk_list_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ListPat>,
    ) -> Result<ListPat<V>, V::Error> {
        Ok(ListPat {
            elements: V::try_collect_items(
                ctx,
                node.fields.iter_mut().map(|a| visitor.visit_pat(ctx, a.ast_ref_mut())),
            )?,
        })
    }

    pub struct IfPat<V: AstVisitorMut> {
        pub pat: V::PatRet,
        pub condition: V::ExprRet,
    }
    pub fn walk_if_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::IfPat>,
    ) -> Result<IfPat<V>, V::Error> {
        Ok(IfPat {
            pat: visitor.visit_pat(ctx, node.pat.ast_ref_mut())?,
            condition: visitor.visit_expr(ctx, node.condition.ast_ref_mut())?,
        })
    }

    pub struct BindingPat<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub visibility: Option<V::VisibilityRet>,
        pub mutability: Option<V::MutabilityRet>,
    }

    pub fn walk_binding_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::BindingPat>,
    ) -> Result<BindingPat<V>, V::Error> {
        Ok(BindingPat {
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

    pub struct SpreadPat<V: AstVisitorMut> {
        pub name: Option<V::NameRet>,
    }

    pub fn walk_spread_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::SpreadPat>,
    ) -> Result<SpreadPat<V>, V::Error> {
        Ok(SpreadPat {
            name: node
                .name
                .as_mut()
                .map(|t| visitor.visit_name(ctx, t.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct LitPat<V: AstVisitorMut> {
        pub lit: V::LitRet,
    }

    pub fn walk_lit_pat<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::LitPat>,
    ) -> Result<LitPat<V>, V::Error> {
        Ok(LitPat { lit: visitor.visit_lit(ctx, node.lit.ast_ref_mut())? })
    }

    pub struct ModulePatEntry<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub pat: V::PatRet,
    }
    pub fn walk_module_pat_entry<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ModulePatEntry>,
    ) -> Result<ModulePatEntry<V>, V::Error> {
        Ok(ModulePatEntry {
            name: visitor.visit_name(ctx, node.name.ast_ref_mut())?,
            pat: visitor.visit_pat(ctx, node.pat.ast_ref_mut())?,
        })
    }

    pub struct ReturnStatement<V: AstVisitorMut>(pub Option<V::ExprRet>);
    pub fn walk_return_statement<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::ReturnStatement>,
    ) -> Result<ReturnStatement<V>, V::Error> {
        Ok(ReturnStatement(
            node.0.as_mut().map(|n| visitor.visit_expr(ctx, n.ast_ref_mut())).transpose()?,
        ))
    }

    pub struct Declaration<V: AstVisitorMut> {
        pub pat: V::PatRet,
        pub ty: Option<V::TyRet>,
        pub value: Option<V::ExprRet>,
    }

    pub fn walk_declaration<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Declaration>,
    ) -> Result<Declaration<V>, V::Error> {
        Ok(Declaration {
            pat: visitor.visit_pat(ctx, node.pat.ast_ref_mut())?,
            ty: node.ty.as_mut().map(|t| visitor.visit_ty(ctx, t.ast_ref_mut())).transpose()?,
            value: node
                .value
                .as_mut()
                .map(|t| visitor.visit_expr(ctx, t.ast_ref_mut()))
                .transpose()?,
        })
    }

    pub struct MergeDeclaration<V: AstVisitorMut> {
        pub decl: V::ExprRet,
        pub value: V::ExprRet,
    }

    pub fn walk_merge_declaration<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::MergeDeclaration>,
    ) -> Result<MergeDeclaration<V>, V::Error> {
        Ok(MergeDeclaration {
            decl: visitor.visit_expr(ctx, node.decl.ast_ref_mut())?,
            value: visitor.visit_expr(ctx, node.value.ast_ref_mut())?,
        })
    }

    pub struct AssignExpr<V: AstVisitorMut> {
        pub lhs: V::ExprRet,
        pub rhs: V::ExprRet,
    }

    pub fn walk_assign_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::AssignExpr>,
    ) -> Result<AssignExpr<V>, V::Error> {
        Ok(AssignExpr {
            lhs: visitor.visit_expr(ctx, node.lhs.ast_ref_mut())?,
            rhs: visitor.visit_expr(ctx, node.rhs.ast_ref_mut())?,
        })
    }

    pub struct AssignOpStatement<V: AstVisitorMut> {
        pub lhs: V::ExprRet,
        pub rhs: V::ExprRet,
        pub operator: V::BinOpRet,
    }
    pub fn walk_assign_op_statement<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::AssignOpExpr>,
    ) -> Result<AssignOpStatement<V>, V::Error> {
        Ok(AssignOpStatement {
            lhs: visitor.visit_expr(ctx, node.lhs.ast_ref_mut())?,
            rhs: visitor.visit_expr(ctx, node.rhs.ast_ref_mut())?,
            operator: visitor.visit_bin_op(ctx, node.operator.ast_ref_mut())?,
        })
    }

    pub struct BinaryExpr<V: AstVisitorMut> {
        pub lhs: V::ExprRet,
        pub rhs: V::ExprRet,
        pub operator: V::BinOpRet,
    }
    pub fn walk_binary_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::BinaryExpr>,
    ) -> Result<BinaryExpr<V>, V::Error> {
        Ok(BinaryExpr {
            lhs: visitor.visit_expr(ctx, node.lhs.ast_ref_mut())?,
            rhs: visitor.visit_expr(ctx, node.rhs.ast_ref_mut())?,
            operator: visitor.visit_bin_op(ctx, node.operator.ast_ref_mut())?,
        })
    }

    pub struct UnaryExpr<V: AstVisitorMut> {
        pub expr: V::ExprRet,
        pub operator: V::UnOpRet,
    }

    pub fn walk_unary_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::UnaryExpr>,
    ) -> Result<UnaryExpr<V>, V::Error> {
        Ok(UnaryExpr {
            expr: visitor.visit_expr(ctx, node.expr.ast_ref_mut())?,
            operator: visitor.visit_un_op(ctx, node.operator.ast_ref_mut())?,
        })
    }

    pub struct IndexExpr<V: AstVisitorMut> {
        pub subject: V::ExprRet,
        pub index_expr: V::ExprRet,
    }

    pub fn walk_index_expr<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::IndexExpr>,
    ) -> Result<IndexExpr<V>, V::Error> {
        Ok(IndexExpr {
            subject: visitor.visit_expr(ctx, node.subject.ast_ref_mut())?,
            index_expr: visitor.visit_expr(ctx, node.index_expr.ast_ref_mut())?,
        })
    }

    pub struct StructDef<V: AstVisitorMut> {
        pub entries: V::CollectionContainer<V::ParamRet>,
    }
    pub fn walk_struct_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::StructDef>,
    ) -> Result<StructDef<V>, V::Error> {
        Ok(StructDef {
            entries: V::try_collect_items(
                ctx,
                node.entries.iter_mut().map(|b| visitor.visit_param(ctx, b.ast_ref_mut())),
            )?,
        })
    }

    pub struct EnumDefEntry<V: AstVisitorMut> {
        pub name: V::NameRet,
        pub args: V::CollectionContainer<V::TyRet>,
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
                node.args.iter_mut().map(|b| visitor.visit_ty(ctx, b.ast_ref_mut())),
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
                node.entries.iter_mut().map(|b| visitor.visit_enum_def_entry(ctx, b.ast_ref_mut())),
            )?,
        })
    }

    pub struct TyFnDef<V: AstVisitorMut> {
        pub params: V::CollectionContainer<V::ParamRet>,
        pub return_ty: Option<V::TyRet>,
        pub body: V::ExprRet,
    }

    pub fn walk_ty_fn_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TyFnDef>,
    ) -> Result<TyFnDef<V>, V::Error> {
        Ok(TyFnDef {
            params: V::try_collect_items(
                ctx,
                node.params.iter_mut().map(|t| visitor.visit_param(ctx, t.ast_ref_mut())),
            )?,
            return_ty: node
                .return_ty
                .as_mut()
                .map(|t| visitor.visit_ty(ctx, t.ast_ref_mut()))
                .transpose()?,
            body: visitor.visit_expr(ctx, node.body.ast_ref_mut())?,
        })
    }

    pub struct TraitDef<V: AstVisitorMut> {
        pub members: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_trait_def<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TraitDef>,
    ) -> Result<TraitDef<V>, V::Error> {
        Ok(TraitDef {
            members: V::try_collect_items(
                ctx,
                node.members.iter_mut().map(|t| visitor.visit_expr(ctx, t.ast_ref_mut())),
            )?,
        })
    }

    pub struct TraitImpl<V: AstVisitorMut> {
        pub ty: V::TyRet,
        pub implementation: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_trait_impl<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::TraitImpl>,
    ) -> Result<TraitImpl<V>, V::Error> {
        Ok(TraitImpl {
            ty: visitor.visit_ty(ctx, node.ty.ast_ref_mut())?,
            implementation: V::try_collect_items(
                ctx,
                node.implementation.iter_mut().map(|t| visitor.visit_expr(ctx, t.ast_ref_mut())),
            )?,
        })
    }

    pub struct Module<V: AstVisitorMut> {
        pub contents: V::CollectionContainer<V::ExprRet>,
    }

    pub fn walk_module<V: AstVisitorMut>(
        visitor: &mut V,
        ctx: &V::Ctx,
        mut node: ast::AstNodeRefMut<ast::Module>,
    ) -> Result<Module<V>, V::Error> {
        Ok(Module {
            contents: V::try_collect_items(
                ctx,
                node.contents.iter_mut().map(|s| visitor.visit_expr(ctx, s.ast_ref_mut())),
            )?,
        })
    }
}
