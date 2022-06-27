//! Contains functions to traverse the AST and add types to it, while checking
//! it for correctness.

use hash_ast::visitor;
use hash_pipeline::sources::Sources;
use hash_source::SourceId;

use crate::{
    error::TcResult,
    ops::AccessToOpsMut,
    storage::{primitives::TermId, AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut},
};

/// Traverses the AST and adds types to it, while checking it for correctness.
///
/// Contains typechecker state that is accessed while traversing.
pub struct TcVisitor<'gs, 'ls, 'cd, 'src> {
    pub storage: StorageRefMut<'gs, 'ls, 'cd>,
    pub source_id: SourceId,
    pub sources: &'src Sources,
}

impl<'gs, 'ls, 'cd, 'src> AccessToStorage for TcVisitor<'gs, 'ls, 'cd, 'src> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 'src> AccessToStorageMut for TcVisitor<'gs, 'ls, 'cd, 'src> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 'src> TcVisitor<'gs, 'ls, 'cd, 'src> {
    /// Create a new [TcVisitor] with the given state, traversing the given
    /// source from [Sources].
    pub fn new_in_source(
        storage: StorageRefMut<'gs, 'ls, 'cd>,
        source_id: SourceId,
        sources: &'src Sources,
    ) -> Self {
        TcVisitor { storage, source_id, sources }
    }

    /// Visits the source passed in as an argument to [Self::new], and returns
    /// the term of the module that corresponds to the source.
    pub(crate) fn visit_source(&mut self) -> TcResult<TermId> {
        // @@Todo: implement this
        Ok(self.builder().create_unresolved_term())
    }
}

impl<'gs, 'ls, 'cd, 'src> visitor::AstVisitor for TcVisitor<'gs, 'ls, 'cd, 'src> {
    type Ctx = ();
    type CollectionContainer<T> = Vec<T>;

    fn try_collect_items<T, E, I: Iterator<Item = Result<T, E>>>(
        _ctx: &Self::Ctx,
        _items: I,
    ) -> Result<Self::CollectionContainer<T>, E> {
        todo!()
    }

    type Error = TermId;

    type ImportRet = TermId;

    fn visit_import(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        todo!()
    }

    type NameRet = TermId;

    fn visit_name(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        todo!()
    }

    type AccessNameRet = TermId;

    fn visit_access_name(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessName>,
    ) -> Result<Self::AccessNameRet, Self::Error> {
        todo!()
    }

    type LiteralRet = TermId;

    fn visit_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Literal>,
    ) -> Result<Self::LiteralRet, Self::Error> {
        todo!()
    }

    type BinaryOperatorRet = TermId;

    fn visit_binary_operator(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinaryOperatorRet, Self::Error> {
        todo!()
    }

    type UnaryOperatorRet = TermId;

    fn visit_unary_operator(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnaryOperatorRet, Self::Error> {
        todo!()
    }

    type ExpressionRet = TermId;

    fn visit_expression(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Expression>,
    ) -> Result<Self::ExpressionRet, Self::Error> {
        todo!()
    }

    type VariableExprRet = TermId;

    fn visit_variable_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        todo!()
    }

    type DirectiveExprRet = TermId;

    fn visit_directive_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        todo!()
    }

    type ConstructorCallArgRet = TermId;

    fn visit_constructor_call_arg(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
        todo!()
    }

    type ConstructorCallArgsRet = TermId;

    fn visit_constructor_call_args(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallArgs>,
    ) -> Result<Self::ConstructorCallArgsRet, Self::Error> {
        todo!()
    }

    type ConstructorCallExprRet = TermId;

    fn visit_constructor_call_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        todo!()
    }

    type PropertyAccessExprRet = TermId;

    fn visit_property_access_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::PropertyAccessExpr>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        todo!()
    }

    type RefExprRet = TermId;

    fn visit_ref_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        todo!()
    }

    type DerefExprRet = TermId;

    fn visit_deref_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        todo!()
    }

    type UnsafeExprRet = TermId;

    fn visit_unsafe_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        todo!()
    }

    type LiteralExprRet = TermId;

    fn visit_literal_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::LiteralExpr>,
    ) -> Result<Self::LiteralExprRet, Self::Error> {
        todo!()
    }

    type CastExprRet = TermId;

    fn visit_cast_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        todo!()
    }

    type TypeExprRet = TermId;

    fn visit_type_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeExpr>,
    ) -> Result<Self::TypeExprRet, Self::Error> {
        todo!()
    }

    type BlockExprRet = TermId;

    fn visit_block_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        todo!()
    }

    type ImportExprRet = TermId;

    fn visit_import_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        todo!()
    }

    type TypeRet = TermId;

    fn visit_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Type>,
    ) -> Result<Self::TypeRet, Self::Error> {
        todo!()
    }

    type NamedFieldTypeRet = TermId;

    fn visit_named_field_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedFieldTypeEntry>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error> {
        todo!()
    }

    type FnTypeRet = TermId;

    fn visit_function_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::FnType>,
    ) -> Result<Self::FnTypeRet, Self::Error> {
        todo!()
    }

    type TypeFunctionParamRet = TermId;

    fn visit_type_function_param(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionParam>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error> {
        todo!()
    }

    type TypeFunctionRet = TermId;

    fn visit_type_function(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunction>,
    ) -> Result<Self::TypeFunctionRet, Self::Error> {
        todo!()
    }

    type TypeFunctionCallRet = TermId;

    fn visit_type_function_call(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionCall>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error> {
        todo!()
    }

    type NamedTypeRet = TermId;

    fn visit_named_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedType>,
    ) -> Result<Self::NamedTypeRet, Self::Error> {
        todo!()
    }

    type RefTypeRet = TermId;

    fn visit_ref_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::RefType>,
    ) -> Result<Self::RefTypeRet, Self::Error> {
        todo!()
    }

    type MergedTypeRet = TermId;

    fn visit_merged_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergedType>,
    ) -> Result<Self::MergedTypeRet, Self::Error> {
        todo!()
    }

    type MapLiteralRet = TermId;

    fn visit_map_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLiteral>,
    ) -> Result<Self::MapLiteralRet, Self::Error> {
        todo!()
    }

    type MapLiteralEntryRet = TermId;

    fn visit_map_literal_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLiteralEntry>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error> {
        todo!()
    }

    type ListLiteralRet = TermId;

    fn visit_list_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListLiteral>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        todo!()
    }

    type SetLiteralRet = TermId;

    fn visit_set_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetLiteral>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        todo!()
    }

    type TupleLiteralEntryRet = TermId;

    fn visit_tuple_literal_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLiteralEntry>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error> {
        todo!()
    }

    type TupleLiteralRet = TermId;

    fn visit_tuple_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLiteral>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        todo!()
    }

    type StrLiteralRet = TermId;

    fn visit_str_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        todo!()
    }

    type CharLiteralRet = TermId;

    fn visit_char_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error> {
        todo!()
    }

    type FloatLiteralRet = TermId;

    fn visit_float_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        todo!()
    }

    type BoolLiteralRet = TermId;

    fn visit_bool_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error> {
        todo!()
    }

    type IntLiteralRet = TermId;

    fn visit_int_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        todo!()
    }

    type FunctionDefRet = TermId;

    fn visit_function_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionDef>,
    ) -> Result<Self::FunctionDefRet, Self::Error> {
        todo!()
    }

    type FunctionDefArgRet = TermId;

    fn visit_function_def_arg(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionDefArg>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error> {
        todo!()
    }

    type BlockRet = TermId;

    fn visit_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        todo!()
    }

    type MatchCaseRet = TermId;

    fn visit_match_case(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        todo!()
    }

    type MatchBlockRet = TermId;

    fn visit_match_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        todo!()
    }

    type LoopBlockRet = TermId;

    fn visit_loop_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        todo!()
    }

    type ForLoopBlockRet = TermId;

    fn visit_for_loop_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        todo!()
    }

    type WhileLoopBlockRet = TermId;

    fn visit_while_loop_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        todo!()
    }

    type ModBlockRet = TermId;

    fn visit_mod_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        todo!()
    }

    type ImplBlockRet = TermId;

    fn visit_impl_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        todo!()
    }

    type IfClauseRet = TermId;

    fn visit_if_clause(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        todo!()
    }

    type IfBlockRet = TermId;

    fn visit_if_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        todo!()
    }

    type BodyBlockRet = TermId;

    fn visit_body_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        todo!()
    }

    type ReturnStatementRet = TermId;

    fn visit_return_statement(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        todo!()
    }

    type BreakStatementRet = TermId;

    fn visit_break_statement(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        todo!()
    }

    type ContinueStatementRet = TermId;

    fn visit_continue_statement(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        todo!()
    }

    type VisibilityRet = TermId;

    fn visit_visibility_modifier(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        todo!()
    }

    type MutabilityRet = TermId;

    fn visit_mutability_modifier(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error> {
        todo!()
    }

    type DeclarationRet = TermId;

    fn visit_declaration(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        todo!()
    }

    type MergeDeclarationRet = TermId;

    fn visit_merge_declaration(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        todo!()
    }

    type AssignExpressionRet = TermId;

    fn visit_assign_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignExpression>,
    ) -> Result<Self::AssignExpressionRet, Self::Error> {
        todo!()
    }

    type AssignOpExpressionRet = TermId;

    fn visit_assign_op_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignOpExpression>,
    ) -> Result<Self::AssignOpExpressionRet, Self::Error> {
        todo!()
    }

    type BinaryExpressionRet = TermId;

    fn visit_binary_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinaryExpression>,
    ) -> Result<Self::BinaryExpressionRet, Self::Error> {
        todo!()
    }

    type UnaryExpressionRet = TermId;

    fn visit_unary_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnaryExpression>,
    ) -> Result<Self::UnaryExpressionRet, Self::Error> {
        todo!()
    }

    type IndexExpressionRet = TermId;

    fn visit_index_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IndexExpression>,
    ) -> Result<Self::IndexExpressionRet, Self::Error> {
        todo!()
    }

    type StructDefEntryRet = TermId;

    fn visit_struct_def_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDefEntry>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        todo!()
    }

    type StructDefRet = TermId;

    fn visit_struct_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        todo!()
    }

    type EnumDefEntryRet = TermId;

    fn visit_enum_def_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        todo!()
    }

    type EnumDefRet = TermId;

    fn visit_enum_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        todo!()
    }

    type TraitDefRet = TermId;

    fn visit_trait_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        todo!()
    }

    type PatternRet = TermId;

    fn visit_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Pattern>,
    ) -> Result<Self::PatternRet, Self::Error> {
        todo!()
    }

    type TraitImplRet = TermId;

    fn visit_trait_impl(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        todo!()
    }

    type TypeFunctionDefRet = TermId;

    fn visit_type_function_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionDef>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error> {
        todo!()
    }

    type TypeFunctionDefArgRet = TermId;

    fn visit_type_function_def_arg(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionDefArg>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error> {
        todo!()
    }

    type ConstructorPatternRet = TermId;

    fn visit_constructor_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorPattern>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error> {
        todo!()
    }

    type NamespacePatternRet = TermId;

    fn visit_namespace_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::NamespacePattern>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        todo!()
    }

    type TuplePatternEntryRet = TermId;

    fn visit_tuple_pattern_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePatternEntry>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error> {
        todo!()
    }

    type TuplePatternRet = TermId;

    fn visit_tuple_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePattern>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        todo!()
    }

    type ListPatternRet = TermId;

    fn visit_list_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListPattern>,
    ) -> Result<Self::ListPatternRet, Self::Error> {
        todo!()
    }

    type TupleTypeRet = TermId;

    fn visit_tuple_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleType>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        todo!()
    }

    type ListTypeRet = TermId;

    fn visit_list_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListType>,
    ) -> Result<Self::ListTypeRet, Self::Error> {
        todo!()
    }

    type SetTypeRet = TermId;

    fn visit_set_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetType>,
    ) -> Result<Self::SetTypeRet, Self::Error> {
        todo!()
    }

    type MapTypeRet = TermId;

    fn visit_map_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapType>,
    ) -> Result<Self::MapTypeRet, Self::Error> {
        todo!()
    }

    type StrLiteralPatternRet = TermId;

    fn visit_str_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        todo!()
    }

    type CharLiteralPatternRet = TermId;

    fn visit_char_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        todo!()
    }

    type IntLiteralPatternRet = TermId;

    fn visit_int_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        todo!()
    }

    type FloatLiteralPatternRet = TermId;

    fn visit_float_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        todo!()
    }

    type BoolLiteralPatternRet = TermId;

    fn visit_bool_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error> {
        todo!()
    }

    type LiteralPatternRet = TermId;

    fn visit_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error> {
        todo!()
    }

    type OrPatternRet = TermId;

    fn visit_or_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::OrPattern>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        todo!()
    }

    type IfPatternRet = TermId;

    fn visit_if_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfPattern>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        todo!()
    }

    type BindingPatternRet = TermId;

    fn visit_binding_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BindingPattern>,
    ) -> Result<Self::BindingPatternRet, Self::Error> {
        todo!()
    }

    type SpreadPatternRet = TermId;

    fn visit_spread_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::SpreadPattern>,
    ) -> Result<Self::SpreadPatternRet, Self::Error> {
        todo!()
    }

    type IgnorePatternRet = TermId;

    fn visit_ignore_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        todo!()
    }

    type DestructuringPatternRet = TermId;

    fn visit_destructuring_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::DestructuringPattern>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error> {
        todo!()
    }

    type ModuleRet = TermId;

    fn visit_module(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        todo!()
    }
}
