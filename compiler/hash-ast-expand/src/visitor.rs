use std::convert::Infallible;

use hash_ast::{
    tree::AstTreeGenerator,
    visitor::{walk, AstVisitor},
};
use hash_source::{
    identifier::IDENTS,
    location::{SourceLocation, Span},
    SourceId, SourceMap,
};
use hash_utils::tree_writing::TreeWriter;

#[derive(Debug)]
pub struct AstExpander<'s> {
    /// The map of the current workspace sources.
    pub(crate) source_map: &'s SourceMap,
    /// The `id` of the module that is currently being checked
    source_id: SourceId,
}

impl<'s> AstExpander<'s> {
    /// Create a new [AstDesugaring]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new(source_map: &'s SourceMap, source_id: SourceId) -> Self {
        Self { source_map, source_id }
    }

    /// Create a [SourceLocation] from a [Span]
    pub(crate) fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, id: self.source_id }
    }
}

impl<'s> AstVisitor for AstExpander<'s> {
    type Error = Infallible;
    type NameRet = ();

    fn visit_name(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        Ok(())
    }

    type LitRet = ();

    fn visit_lit(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Lit>,
    ) -> Result<Self::LitRet, Self::Error> {
        Ok(())
    }

    type MapLitRet = ();

    fn visit_map_lit(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLit>,
    ) -> Result<Self::MapLitRet, Self::Error> {
        let _ = walk::walk_map_lit(self, node);
        Ok(())
    }

    type MapLitEntryRet = ();

    fn visit_map_lit_entry(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLitEntry>,
    ) -> Result<Self::MapLitEntryRet, Self::Error> {
        let _ = walk::walk_map_lit_entry(self, node);
        Ok(())
    }

    type ListLitRet = ();

    fn visit_list_lit(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListLit>,
    ) -> Result<Self::ListLitRet, Self::Error> {
        let _ = walk::walk_list_lit(self, node);
        Ok(())
    }

    type SetLitRet = ();

    fn visit_set_lit(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetLit>,
    ) -> Result<Self::SetLitRet, Self::Error> {
        let _ = walk::walk_set_lit(self, node);
        Ok(())
    }

    type TupleLitEntryRet = ();

    fn visit_tuple_lit_entry(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitEntryRet, Self::Error> {
        let _ = walk::walk_tuple_lit_entry(self, node);
        Ok(())
    }

    type TupleLitRet = ();

    fn visit_tuple_lit(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        let _ = walk::walk_tuple_lit(self, node);
        Ok(())
    }

    type StrLitRet = ();

    fn visit_str_lit(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error> {
        Ok(())
    }

    type CharLitRet = ();

    fn visit_char_lit(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error> {
        Ok(())
    }

    type FloatLitRet = ();

    fn visit_float_lit(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        Ok(())
    }

    type BoolLitRet = ();

    fn visit_bool_lit(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error> {
        Ok(())
    }

    type IntLitRet = ();

    fn visit_int_lit(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error> {
        Ok(())
    }

    type BinOpRet = ();

    fn visit_bin_op(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinOpRet, Self::Error> {
        Ok(())
    }

    type UnOpRet = ();

    fn visit_un_op(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnOpRet, Self::Error> {
        Ok(())
    }

    type ExprRet = ();

    fn visit_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Expr>,
    ) -> Result<Self::ExprRet, Self::Error> {
        walk::walk_expr_same_children(self, node)
    }

    type VariableExprRet = ();

    fn visit_variable_expr(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        Ok(())
    }

    type DirectiveExprRet = ();

    fn visit_directive_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let _ = walk::walk_directive_expr(self, node);

        // for the `dump_ast` directive, we essentially "dump" the generated tree
        // that the parser created. We emit this tree regardless of whether or not
        // there will be errors later on in the compilation stage.
        if node.name.is(IDENTS.dump_ast) {
            let tree = AstTreeGenerator.visit_expr(node.subject.ast_ref()).unwrap();
            let name = self.source_map.canonicalised_path_by_id(self.source_id);

            let location = self.source_location(node.subject.span());
            let span = self.source_map.get_column_row_span_for(location);

            println!("AST for {name}:{span}\n{}", TreeWriter::new(&tree));
        }

        Ok(())
    }

    type ConstructorCallArgRet = ();

    fn visit_constructor_call_arg(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
        let _ = walk::walk_constructor_call_arg(self, node);
        Ok(())
    }

    type ConstructorCallExprRet = ();

    fn visit_constructor_call_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        let _ = walk::walk_constructor_call_expr(self, node);
        Ok(())
    }

    type PropertyKindRet = ();

    fn visit_property_kind(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::PropertyKind>,
    ) -> Result<Self::PropertyKindRet, Self::Error> {
        Ok(())
    }

    type AccessExprRet = ();

    fn visit_access_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let _ = walk::walk_access_expr(self, node);
        Ok(())
    }

    type AccessKindRet = ();

    fn visit_access_kind(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessKind>,
    ) -> Result<Self::AccessKindRet, Self::Error> {
        Ok(())
    }

    type RefExprRet = ();

    fn visit_ref_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let _ = walk::walk_ref_expr(self, node);
        Ok(())
    }

    type DerefExprRet = ();

    fn visit_deref_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let _ = walk::walk_deref_expr(self, node);
        Ok(())
    }

    type UnsafeExprRet = ();

    fn visit_unsafe_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        let _ = walk::walk_unsafe_expr(self, node);
        Ok(())
    }

    type LitExprRet = ();

    fn visit_lit_expr(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::LitExpr>,
    ) -> Result<Self::LitExprRet, Self::Error> {
        Ok(())
    }

    type CastExprRet = ();

    fn visit_cast_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let _ = walk::walk_cast_expr(self, node);
        Ok(())
    }

    type TyExprRet = ();

    fn visit_ty_expr(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error> {
        Ok(())
    }

    type BlockExprRet = ();

    #[inline]
    fn visit_block_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        let _ = walk::walk_block_expr(self, node)?;

        Ok(())
    }

    type ImportRet = ();

    fn visit_import(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        Ok(())
    }

    type ImportExprRet = ();

    fn visit_import_expr(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(())
    }

    type TyRet = ();

    fn visit_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Ty>,
    ) -> Result<Self::TyRet, Self::Error> {
        Ok(())
    }

    type TupleTyRet = ();

    fn visit_tuple_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        Ok(())
    }

    type ListTyRet = ();

    fn visit_list_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ListTy>,
    ) -> Result<Self::ListTyRet, Self::Error> {
        Ok(())
    }

    type SetTyRet = ();

    fn visit_set_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::SetTy>,
    ) -> Result<Self::SetTyRet, Self::Error> {
        Ok(())
    }

    type MapTyRet = ();

    fn visit_map_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::MapTy>,
    ) -> Result<Self::MapTyRet, Self::Error> {
        Ok(())
    }

    type TyArgRet = ();

    fn visit_ty_arg(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        Ok(())
    }

    type FnTyRet = ();

    fn visit_fn_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::FnTy>,
    ) -> Result<Self::FnTyRet, Self::Error> {
        Ok(())
    }

    type TyFnRet = ();

    fn visit_ty_fn(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFn>,
    ) -> Result<Self::TyFnRet, Self::Error> {
        Ok(())
    }

    type TyFnCallRet = ();

    fn visit_ty_fn_call(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error> {
        Ok(())
    }

    type NamedTyRet = ();
    fn visit_named_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        Ok(())
    }

    type AccessTyRet = ();

    fn visit_access_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        Ok(())
    }

    type RefTyRet = ();

    fn visit_ref_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error> {
        Ok(())
    }

    type MergeTyRet = ();

    fn visit_merge_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error> {
        Ok(())
    }

    type UnionTyRet = ();

    fn visit_union_ty(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error> {
        Ok(())
    }

    type TyFnDefRet = ();

    fn visit_ty_fn_def(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let _ = walk::walk_ty_fn_def(self, node);
        Ok(())
    }

    type FnDefRet = ();

    fn visit_fn_def(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let _ = walk::walk_fn_def(self, node);
        Ok(())
    }

    type ParamRet = ();

    fn visit_param(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        let _ = walk::walk_param(self, node);
        Ok(())
    }

    type BlockRet = ();

    fn visit_block(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        // We still need to walk the block now
        let _ = walk::walk_block(self, node);

        Ok(())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let _ = walk::walk_match_case(self, node);
        Ok(())
    }

    type MatchBlockRet = ();

    fn visit_match_block(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let _ = walk::walk_match_block(self, node);
        Ok(())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let _ = walk::walk_loop_block(self, node);

        Ok(())
    }

    type ForLoopBlockRet = ();

    fn visit_for_loop_block(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type WhileLoopBlockRet = ();

    fn visit_while_loop_block(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type ModBlockRet = ();

    fn visit_mod_block(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        let _ = walk::walk_mod_block(self, node);
        Ok(())
    }

    type ImplBlockRet = ();

    fn visit_impl_block(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        let _ = walk::walk_impl_block(self, node);
        Ok(())
    }

    type IfClauseRet = ();

    fn visit_if_clause(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type IfBlockRet = ();

    fn visit_if_block(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let _ = walk::walk_body_block(self, node);
        Ok(())
    }

    type ReturnStatementRet = ();

    fn visit_return_statement(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let _ = walk::walk_return_statement(self, node);
        Ok(())
    }

    type BreakStatementRet = ();

    fn visit_break_statement(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        Ok(())
    }

    type ContinueStatementRet = ();

    fn visit_continue_statement(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        Ok(())
    }

    type VisibilityRet = ();

    fn visit_visibility(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        Ok(())
    }

    type MutabilityRet = ();

    fn visit_mutability(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error> {
        Ok(())
    }

    type RefKindRet = ();

    fn visit_ref_kind(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::RefKind>,
    ) -> Result<Self::RefKindRet, Self::Error> {
        Ok(())
    }

    type DeclarationRet = ();

    fn visit_declaration(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let _ = walk::walk_declaration(self, node);
        Ok(())
    }

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        // @@Note: We probably don't have to walk this??
        let _ = walk::walk_merge_declaration(self, node);
        Ok(())
    }

    type AssignExprRet = ();

    fn visit_assign_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error> {
        let _ = walk::walk_assign_expr(self, node);
        Ok(())
    }

    type AssignOpExprRet = ();

    fn visit_assign_op_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error> {
        let _ = walk::walk_assign_op_expr(self, node);
        Ok(())
    }

    type BinaryExprRet = ();

    fn visit_binary_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error> {
        let _ = walk::walk_binary_expr(self, node);
        Ok(())
    }

    type UnaryExprRet = ();

    fn visit_unary_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error> {
        let _ = walk::walk_unary_expr(self, node);
        Ok(())
    }

    type IndexExprRet = ();

    fn visit_index_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error> {
        let _ = walk::walk_index_expr(self, node);
        Ok(())
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let _ = walk::walk_struct_def(self, node);
        Ok(())
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        Ok(())
    }

    type EnumDefRet = ();

    fn visit_enum_def(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        Ok(())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let _ = walk::walk_trait_def(self, node);
        Ok(())
    }

    type TraitImplRet = ();

    fn visit_trait_impl(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let _ = walk::walk_trait_impl(self, node);
        Ok(())
    }

    type PatRet = ();

    fn visit_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::Pat>,
    ) -> Result<Self::PatRet, Self::Error> {
        Ok(())
    }

    type AccessPatRet = ();

    fn visit_access_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        Ok(())
    }

    type ConstructorPatRet = ();

    fn visit_constructor_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        Ok(())
    }

    type TuplePatEntryRet = ();

    fn visit_tuple_pat_entry(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePatEntry>,
    ) -> Result<Self::TuplePatEntryRet, Self::Error> {
        Ok(())
    }

    type TuplePatRet = ();

    fn visit_tuple_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        Ok(())
    }

    type ListPatRet = ();

    fn visit_list_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ListPat>,
    ) -> Result<Self::ListPatRet, Self::Error> {
        Ok(())
    }

    type SpreadPatRet = ();

    fn visit_spread_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error> {
        Ok(())
    }

    type LitPatRet = ();

    fn visit_lit_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::LitPat>,
    ) -> Result<Self::LitPatRet, Self::Error> {
        Ok(())
    }

    type RangePatRet = ();

    fn visit_range_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::RangePat>,
    ) -> Result<Self::RangePatRet, Self::Error> {
        Ok(())
    }

    type OrPatRet = ();

    fn visit_or_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error> {
        Ok(())
    }

    type IfPatRet = ();

    fn visit_if_pat(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error> {
        let _ = walk::walk_if_pat(self, node);
        Ok(())
    }

    type BindingPatRet = ();

    fn visit_binding_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        Ok(())
    }

    type WildPatRet = ();

    fn visit_wild_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error> {
        Ok(())
    }

    type ModulePatEntryRet = ();

    fn visit_module_pat_entry(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        Ok(())
    }

    type ModulePatRet = ();

    fn visit_module_pat(
        &self,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error> {
        Ok(())
    }

    type ModuleRet = ();

    fn visit_module(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let _ = walk::walk_module(self, node);
        Ok(())
    }
}
