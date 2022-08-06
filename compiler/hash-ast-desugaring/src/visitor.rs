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

    type LitRet = ();

    fn visit_lit(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Lit>,
    ) -> Result<Self::LitRet, Self::Error> {
        Ok(())
    }

    type MapLitRet = ();

    fn visit_map_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapLit>,
    ) -> Result<Self::MapLitRet, Self::Error> {
        let _ = walk_mut::walk_map_lit(self, ctx, node);
        Ok(())
    }

    type MapLitEntryRet = ();

    fn visit_map_lit_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapLitEntry>,
    ) -> Result<Self::MapLitEntryRet, Self::Error> {
        let _ = walk_mut::walk_map_lit_entry(self, ctx, node);
        Ok(())
    }

    type ListLitRet = ();

    fn visit_list_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListLit>,
    ) -> Result<Self::ListLitRet, Self::Error> {
        let _ = walk_mut::walk_list_lit(self, ctx, node);
        Ok(())
    }

    type SetLitRet = ();

    fn visit_set_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SetLit>,
    ) -> Result<Self::SetLitRet, Self::Error> {
        let _ = walk_mut::walk_set_lit(self, ctx, node);
        Ok(())
    }

    type TupleLitEntryRet = ();

    fn visit_tuple_lit_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitEntryRet, Self::Error> {
        let _ = walk_mut::walk_tuple_lit_entry(self, ctx, node);
        Ok(())
    }

    type TupleLitRet = ();

    fn visit_tuple_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        let _ = walk_mut::walk_tuple_lit(self, ctx, node);
        Ok(())
    }

    type StrLitRet = ();

    fn visit_str_lit(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error> {
        Ok(())
    }

    type CharLitRet = ();

    fn visit_char_lit(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error> {
        Ok(())
    }

    type FloatLitRet = ();

    fn visit_float_lit(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        Ok(())
    }

    type BoolLitRet = ();

    fn visit_bool_lit(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error> {
        Ok(())
    }

    type IntLitRet = ();

    fn visit_int_lit(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error> {
        Ok(())
    }

    type BinOpRet = ();

    fn visit_bin_op(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinOpRet, Self::Error> {
        Ok(())
    }

    type UnOpRet = ();

    fn visit_un_op(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnOpRet, Self::Error> {
        Ok(())
    }

    type ExprRet = ();

    fn visit_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Expr>,
    ) -> Result<Self::ExprRet, Self::Error> {
        let _ = walk_mut::walk_expr(self, ctx, node);
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

    type AccessExprRet = ();

    fn visit_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let _ = walk_mut::walk_access_expr(self, ctx, node);
        Ok(())
    }

    type AccessKindRet = ();

    fn visit_access_kind(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AccessKind,
    ) -> Result<Self::AccessKindRet, Self::Error> {
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

    type LitExprRet = ();

    fn visit_lit_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LitExpr>,
    ) -> Result<Self::LitExprRet, Self::Error> {
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

    type TyArgRet = ();

    fn visit_ty_arg(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
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

    type AccessTyRet = ();
    fn visit_access_ty(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
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

    type FnDefRet = ();

    fn visit_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let _ = walk_mut::walk_fn_def(self, ctx, node);
        Ok(())
    }

    type ParamRet = ();

    fn visit_param(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        let _ = walk_mut::walk_param(self, ctx, node);
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

    type AssignExprRet = ();

    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error> {
        let _ = walk_mut::walk_assign_expr(self, ctx, node);
        Ok(())
    }

    type AssignOpExprRet = ();

    fn visit_assign_op_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error> {
        let _ = walk_mut::walk_assign_op_statement(self, ctx, node);
        Ok(())
    }

    type BinaryExprRet = ();

    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error> {
        let _ = walk_mut::walk_binary_expr(self, ctx, node);
        Ok(())
    }

    type UnaryExprRet = ();

    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error> {
        let _ = walk_mut::walk_unary_expr(self, ctx, node);
        Ok(())
    }

    type IndexExprRet = ();

    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error> {
        let _ = walk_mut::walk_index_expr(self, ctx, node);
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

    type PatRet = ();

    fn visit_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Pat>,
    ) -> Result<Self::PatRet, Self::Error> {
        Ok(())
    }

    type AccessPatRet = ();

    fn visit_access_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        Ok(())
    }

    type ConstructorPatRet = ();

    fn visit_constructor_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        Ok(())
    }

    type TuplePatEntryRet = ();

    fn visit_tuple_pat_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TuplePatEntry>,
    ) -> Result<Self::TuplePatEntryRet, Self::Error> {
        Ok(())
    }

    type TuplePatRet = ();

    fn visit_tuple_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        Ok(())
    }

    type ListPatRet = ();

    fn visit_list_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListPat>,
    ) -> Result<Self::ListPatRet, Self::Error> {
        Ok(())
    }

    type SpreadPatRet = ();

    fn visit_spread_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error> {
        Ok(())
    }

    type LitPatRet = ();

    fn visit_lit_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LitPat>,
    ) -> Result<Self::LitPatRet, Self::Error> {
        Ok(())
    }

    type OrPatRet = ();

    fn visit_or_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error> {
        Ok(())
    }

    type IfPatRet = ();

    fn visit_if_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error> {
        let _ = walk_mut::walk_if_pat(self, ctx, node);
        Ok(())
    }

    type BindingPatRet = ();

    fn visit_binding_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        Ok(())
    }

    type WildPatRet = ();

    fn visit_wild_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error> {
        Ok(())
    }

    type ModulePatEntryRet = ();

    fn visit_module_pat_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        Ok(())
    }

    type ModulePatRet = ();

    fn visit_module_pat(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error> {
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
