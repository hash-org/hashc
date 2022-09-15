//! Visitor implementation for [crate::ast] nodes.

use std::convert::Infallible;

use crate::ast;

macro_rules! make_ast_visitor {
    ($visitor_trait_name:ident, $($path:ident)::+) => {
        /// A visitor [crate::ast] nodes that takes `&mut self`.
        /// This contains a method for each AST structure, as well as a dedicated return
        /// type for it. These can be implemented using the functions defined in [walk]
        /// that can traverse the children of each node.
        pub trait $visitor_trait_name: Sized {
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
                node: $($path)::+<ast::Name>,
            ) -> Result<Self::NameRet, Self::Error>;

            type LitRet;
            fn visit_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Lit>,
            ) -> Result<Self::LitRet, Self::Error>;

            type MapLitRet;
            fn visit_map_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::MapLit>,
            ) -> Result<Self::MapLitRet, Self::Error>;

            type MapLitEntryRet;
            fn visit_map_lit_entry(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::MapLitEntry>,
            ) -> Result<Self::MapLitEntryRet, Self::Error>;

            type ListLitRet;
            fn visit_list_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ListLit>,
            ) -> Result<Self::ListLitRet, Self::Error>;

            type SetLitRet;
            fn visit_set_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::SetLit>,
            ) -> Result<Self::SetLitRet, Self::Error>;

            type TupleLitEntryRet;
            fn visit_tuple_lit_entry(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TupleLitEntry>,
            ) -> Result<Self::TupleLitEntryRet, Self::Error>;

            type TupleLitRet;
            fn visit_tuple_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TupleLit>,
            ) -> Result<Self::TupleLitRet, Self::Error>;

            type StrLitRet;
            fn visit_str_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::StrLit>,
            ) -> Result<Self::StrLitRet, Self::Error>;

            type CharLitRet;
            fn visit_char_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::CharLit>,
            ) -> Result<Self::CharLitRet, Self::Error>;

            type FloatLitRet;
            fn visit_float_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::FloatLit>,
            ) -> Result<Self::FloatLitRet, Self::Error>;

            type BoolLitRet;
            fn visit_bool_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::BoolLit>,
            ) -> Result<Self::BoolLitRet, Self::Error>;

            type IntLitRet;
            fn visit_int_lit(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::IntLit>,
            ) -> Result<Self::IntLitRet, Self::Error>;

            type BinOpRet;
            fn visit_bin_op(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::BinOp>,
            ) -> Result<Self::BinOpRet, Self::Error>;

            type UnOpRet;
            fn visit_un_op(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::UnOp>,
            ) -> Result<Self::UnOpRet, Self::Error>;

            type ExprRet;
            fn visit_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Expr>,
            ) -> Result<Self::ExprRet, Self::Error>;

            type VariableExprRet;
            fn visit_variable_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::VariableExpr>,
            ) -> Result<Self::VariableExprRet, Self::Error>;

            type DirectiveExprRet;
            fn visit_directive_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::DirectiveExpr>,
            ) -> Result<Self::DirectiveExprRet, Self::Error>;

            type ConstructorCallArgRet;
            fn visit_constructor_call_arg(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ConstructorCallArg>,
            ) -> Result<Self::ConstructorCallArgRet, Self::Error>;

            type ConstructorCallExprRet;
            fn visit_constructor_call_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ConstructorCallExpr>,
            ) -> Result<Self::ConstructorCallExprRet, Self::Error>;

            type PropertyKindRet;
            fn visit_property_kind(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::PropertyKind>,
            ) -> Result<Self::PropertyKindRet, Self::Error>;

            type AccessExprRet;
            fn visit_access_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::AccessExpr>,
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
                node: $($path)::+<ast::RefExpr>,
            ) -> Result<Self::RefExprRet, Self::Error>;

            type DerefExprRet;
            fn visit_deref_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::DerefExpr>,
            ) -> Result<Self::DerefExprRet, Self::Error>;

            type UnsafeExprRet;
            fn visit_unsafe_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::UnsafeExpr>,
            ) -> Result<Self::UnsafeExprRet, Self::Error>;

            type LitExprRet;
            fn visit_lit_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::LitExpr>,
            ) -> Result<Self::LitExprRet, Self::Error>;

            type CastExprRet;
            fn visit_cast_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::CastExpr>,
            ) -> Result<Self::CastExprRet, Self::Error>;

            type TyExprRet;
            fn visit_ty_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TyExpr>,
            ) -> Result<Self::TyExprRet, Self::Error>;

            type BlockExprRet;
            fn visit_block_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::BlockExpr>,
            ) -> Result<Self::BlockExprRet, Self::Error>;

            type ImportRet;
            fn visit_import(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Import>,
            ) -> Result<Self::ImportRet, Self::Error>;

            type ImportExprRet;
            fn visit_import_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ImportExpr>,
            ) -> Result<Self::ImportExprRet, Self::Error>;

            type TyRet;
            fn visit_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Ty>,
            ) -> Result<Self::TyRet, Self::Error>;

            type TupleTyRet;
            fn visit_tuple_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TupleTy>,
            ) -> Result<Self::TupleTyRet, Self::Error>;

            type ListTyRet;
            fn visit_list_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ListTy>,
            ) -> Result<Self::ListTyRet, Self::Error>;

            type SetTyRet;
            fn visit_set_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::SetTy>,
            ) -> Result<Self::SetTyRet, Self::Error>;

            type MapTyRet;
            fn visit_map_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::MapTy>,
            ) -> Result<Self::MapTyRet, Self::Error>;

            type TyArgRet;
            fn visit_ty_arg(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TyArg>,
            ) -> Result<Self::TyArgRet, Self::Error>;

            type FnTyRet;
            fn visit_fn_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::FnTy>,
            ) -> Result<Self::FnTyRet, Self::Error>;

            type TyFnRet;
            fn visit_ty_fn_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TyFn>,
            ) -> Result<Self::TyFnRet, Self::Error>;

            type TyFnCallRet;
            fn visit_ty_fn_call(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TyFnCall>,
            ) -> Result<Self::TyFnCallRet, Self::Error>;

            type NamedTyRet;
            fn visit_named_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::NamedTy>,
            ) -> Result<Self::NamedTyRet, Self::Error>;

            type AccessTyRet;
            fn visit_access_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::AccessTy>,
            ) -> Result<Self::AccessTyRet, Self::Error>;

            type RefTyRet;
            fn visit_ref_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::RefTy>,
            ) -> Result<Self::RefTyRet, Self::Error>;

            type MergeTyRet;
            fn visit_merge_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::MergeTy>,
            ) -> Result<Self::MergeTyRet, Self::Error>;

            type UnionTyRet;
            fn visit_union_ty(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::UnionTy>,
            ) -> Result<Self::UnionTyRet, Self::Error>;

            type TyFnDefRet;
            fn visit_ty_fn_def(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TyFnDef>,
            ) -> Result<Self::TyFnDefRet, Self::Error>;

            type FnDefRet;
            fn visit_fn_def(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::FnDef>,
            ) -> Result<Self::FnDefRet, Self::Error>;

            type ParamRet;
            fn visit_param(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Param>,
            ) -> Result<Self::ParamRet, Self::Error>;

            type BlockRet;
            fn visit_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Block>,
            ) -> Result<Self::BlockRet, Self::Error>;

            type MatchCaseRet;
            fn visit_match_case(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::MatchCase>,
            ) -> Result<Self::MatchCaseRet, Self::Error>;

            type MatchBlockRet;
            fn visit_match_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::MatchBlock>,
            ) -> Result<Self::MatchBlockRet, Self::Error>;

            type LoopBlockRet;
            fn visit_loop_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::LoopBlock>,
            ) -> Result<Self::LoopBlockRet, Self::Error>;

            type ForLoopBlockRet;
            fn visit_for_loop_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ForLoopBlock>,
            ) -> Result<Self::ForLoopBlockRet, Self::Error>;

            type WhileLoopBlockRet;
            fn visit_while_loop_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::WhileLoopBlock>,
            ) -> Result<Self::WhileLoopBlockRet, Self::Error>;

            type ModBlockRet;
            fn visit_mod_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ModBlock>,
            ) -> Result<Self::ModBlockRet, Self::Error>;

            type ImplBlockRet;
            fn visit_impl_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ImplBlock>,
            ) -> Result<Self::ImplBlockRet, Self::Error>;

            type IfClauseRet;
            fn visit_if_clause(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::IfClause>,
            ) -> Result<Self::IfClauseRet, Self::Error>;

            type IfBlockRet;
            fn visit_if_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::IfBlock>,
            ) -> Result<Self::IfBlockRet, Self::Error>;

            type BodyBlockRet;
            fn visit_body_block(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::BodyBlock>,
            ) -> Result<Self::BodyBlockRet, Self::Error>;

            type ReturnStatementRet;
            fn visit_return_statement(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ReturnStatement>,
            ) -> Result<Self::ReturnStatementRet, Self::Error>;

            type BreakStatementRet;
            fn visit_break_statement(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::BreakStatement>,
            ) -> Result<Self::BreakStatementRet, Self::Error>;

            type ContinueStatementRet;
            fn visit_continue_statement(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ContinueStatement>,
            ) -> Result<Self::ContinueStatementRet, Self::Error>;

            type VisibilityRet;
            fn visit_visibility_modifier(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Visibility>,
            ) -> Result<Self::VisibilityRet, Self::Error>;

            type MutabilityRet;
            fn visit_mutability_modifier(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Mutability>,
            ) -> Result<Self::MutabilityRet, Self::Error>;

            type RefKindRet;
            fn visit_ref_kind(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::RefKind>,
            ) -> Result<Self::RefKindRet, Self::Error>;

            type DeclarationRet;
            fn visit_declaration(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Declaration>,
            ) -> Result<Self::DeclarationRet, Self::Error>;

            type MergeDeclarationRet;
            fn visit_merge_declaration(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::MergeDeclaration>,
            ) -> Result<Self::MergeDeclarationRet, Self::Error>;

            type AssignExprRet;
            fn visit_assign_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::AssignExpr>,
            ) -> Result<Self::AssignExprRet, Self::Error>;

            type AssignOpExprRet;
            fn visit_assign_op_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::AssignOpExpr>,
            ) -> Result<Self::AssignOpExprRet, Self::Error>;

            type BinaryExprRet;
            fn visit_binary_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::BinaryExpr>,
            ) -> Result<Self::BinaryExprRet, Self::Error>;

            type UnaryExprRet;
            fn visit_unary_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::UnaryExpr>,
            ) -> Result<Self::UnaryExprRet, Self::Error>;

            type IndexExprRet;
            fn visit_index_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::IndexExpr>,
            ) -> Result<Self::IndexExprRet, Self::Error>;

            type EmptyExprRet;
            fn visit_empty_expr(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::EmptyExpr>,
            ) -> Result<Self::EmptyExprRet, Self::Error>;

            type StructDefRet;
            fn visit_struct_def(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::StructDef>,
            ) -> Result<Self::StructDefRet, Self::Error>;

            type EnumDefEntryRet;
            fn visit_enum_def_entry(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::EnumDefEntry>,
            ) -> Result<Self::EnumDefEntryRet, Self::Error>;

            type EnumDefRet;
            fn visit_enum_def(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::EnumDef>,
            ) -> Result<Self::EnumDefRet, Self::Error>;

            type TraitDefRet;
            fn visit_trait_def(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TraitDef>,
            ) -> Result<Self::TraitDefRet, Self::Error>;

            type TraitImplRet;
            fn visit_trait_impl(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TraitImpl>,
            ) -> Result<Self::TraitImplRet, Self::Error>;

            type PatRet;
            fn visit_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Pat>,
            ) -> Result<Self::PatRet, Self::Error>;

            type AccessPatRet;
            fn visit_access_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::AccessPat>,
            ) -> Result<Self::AccessPatRet, Self::Error>;

            type ConstructorPatRet;
            fn visit_constructor_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ConstructorPat>,
            ) -> Result<Self::ConstructorPatRet, Self::Error>;

            type TuplePatEntryRet;
            fn visit_tuple_pat_entry(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TuplePatEntry>,
            ) -> Result<Self::TuplePatEntryRet, Self::Error>;

            type TuplePatRet;
            fn visit_tuple_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::TuplePat>,
            ) -> Result<Self::TuplePatRet, Self::Error>;

            type ListPatRet;
            fn visit_list_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ListPat>,
            ) -> Result<Self::ListPatRet, Self::Error>;

            type SpreadPatRet;
            fn visit_spread_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::SpreadPat>,
            ) -> Result<Self::SpreadPatRet, Self::Error>;

            type LitPatRet;
            fn visit_lit_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::LitPat>,
            ) -> Result<Self::LitPatRet, Self::Error>;

            type RangePatRet;
            fn visit_range_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::RangePat>,
            ) -> Result<Self::RangePatRet, Self::Error>;

            type OrPatRet;
            fn visit_or_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::OrPat>,
            ) -> Result<Self::OrPatRet, Self::Error>;

            type IfPatRet;
            fn visit_if_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::IfPat>,
            ) -> Result<Self::IfPatRet, Self::Error>;

            type BindingPatRet;
            fn visit_binding_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::BindingPat>,
            ) -> Result<Self::BindingPatRet, Self::Error>;

            type WildPatRet;
            fn visit_wild_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::WildPat>,
            ) -> Result<Self::WildPatRet, Self::Error>;

            type ModulePatEntryRet;
            fn visit_module_pat_entry(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ModulePatEntry>,
            ) -> Result<Self::ModulePatEntryRet, Self::Error>;

            type ModulePatRet;
            fn visit_module_pat(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::ModulePat>,
            ) -> Result<Self::ModulePatRet, Self::Error>;

            type ModuleRet;
            fn visit_module(
                &mut self,
                ctx: &Self::Ctx,
                node: $($path)::+<ast::Module>,
            ) -> Result<Self::ModuleRet, Self::Error>;
        }
    }
}

// Derive both a `mutable` and `immutable` visitor which takes a
// mutable or immutable reference to the body.
make_ast_visitor!(AstVisitor, ast::AstNodeRef);
make_ast_visitor!(AstVisitorMut, ast::AstNodeRefMut);

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
macro_rules! make_ast_walker {
    (
        $mod_name:ident,
        $($path:ident)::+,
        $visitor: ident,
        $ref:ident,
        $ast_ref:ident,
        $iter_ref:ident,
        $($mutability:ident)?
    ) => {
        pub mod $mod_name {
            use super::{ast, $visitor};

            pub struct Param<V: $visitor> {
                pub name: Option<V::NameRet>,
                pub ty: Option<V::TyRet>,
                pub default: Option<V::ExprRet>,
            }

            pub fn walk_param<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::Param>,
            ) -> Result<Param<V>, V::Error> {
                Ok(Param {
                    name: node.name.$ref().map(|t| visitor.visit_name(ctx, t.$ast_ref())).transpose()?,
                    ty: node.ty.$ref().map(|t| visitor.visit_ty(ctx, t.$ast_ref())).transpose()?,
                    default: node
                        .default
                        .$ref()
                        .map(|t| visitor.visit_expr(ctx, t.$ast_ref()))
                        .transpose()?,
                })
            }

            pub struct FnDef<V: $visitor> {
                pub params: V::CollectionContainer<V::ParamRet>,
                pub return_ty: Option<V::TyRet>,
                pub fn_body: V::ExprRet,
            }

            pub fn walk_fn_def<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::FnDef>,
            ) -> Result<FnDef<V>, V::Error> {
                Ok(FnDef {
                    params: V::try_collect_items(
                        ctx,
                        node.params.$iter_ref().map(|a| visitor.visit_param(ctx, a.$ast_ref())),
                    )?,
                    return_ty: node
                        .return_ty
                        .$ref()
                        .map(|t| visitor.visit_ty(ctx, t.$ast_ref()))
                        .transpose()?,
                    fn_body: visitor.visit_expr(ctx, node.fn_body.$ast_ref())?,
                })
            }

            pub enum Expr<V: $visitor> {
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
                Empty(V::EmptyExprRet)
            }

            pub fn walk_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::Expr>,
            ) -> Result<Expr<V>, V::Error> {
                let (span, id) = (node.span(), node.id());

                Ok(match &$($mutability)? node.kind {
                    ast::ExprKind::ConstructorCall(inner) => Expr::ConstructorCall(
                        visitor.visit_constructor_call_expr(ctx, $($path)::+::new(inner, span, id))?,
                    ),
                    ast::ExprKind::Ty(inner) => {
                        Expr::Ty(visitor.visit_ty_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::Directive(inner) => Expr::Directive(
                        visitor.visit_directive_expr(ctx, $($path)::+::new(inner, span, id))?,
                    ),
                    ast::ExprKind::Declaration(inner) => {
                        Expr::Declaration(visitor.visit_declaration(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::MergeDeclaration(inner) => Expr::MergeDeclaration(
                        visitor.visit_merge_declaration(ctx, $($path)::+::new(inner, span, id))?,
                    ),
                    ast::ExprKind::Variable(inner) => {
                        Expr::Variable(visitor.visit_variable_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::Access(inner) => {
                        Expr::Access(visitor.visit_access_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::Ref(inner) => {
                        Expr::Ref(visitor.visit_ref_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::Deref(inner) => {
                        Expr::Deref(visitor.visit_deref_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::Unsafe(inner) => {
                        Expr::Unsafe(visitor.visit_unsafe_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::LitExpr(inner) => {
                        Expr::LitExpr(visitor.visit_lit_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::Cast(inner) => {
                        Expr::Cast(visitor.visit_cast_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::Block(inner) => {
                        Expr::Block(visitor.visit_block_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::Import(inner) => {
                        Expr::Import(visitor.visit_import_expr(ctx, $($path)::+::new(inner, span, id))?)
                    }
                    ast::ExprKind::StructDef(r) => {
                        Expr::StructDef(visitor.visit_struct_def(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::EnumDef(r) => {
                        Expr::EnumDef(visitor.visit_enum_def(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::TyFnDef(r) => {
                        Expr::TyFnDef(visitor.visit_ty_fn_def(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::TraitDef(r) => {
                        Expr::TraitDef(visitor.visit_trait_def(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::FnDef(r) => {
                        Expr::FnDef(visitor.visit_fn_def(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::Return(r) => {
                        Expr::Return(visitor.visit_return_statement(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::Break(r) => {
                        Expr::Break(visitor.visit_break_statement(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::Continue(r) => {
                        Expr::Continue(visitor.visit_continue_statement(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::Assign(r) => {
                        Expr::Assign(visitor.visit_assign_expr(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::AssignOp(r) => {
                        Expr::AssignOp(visitor.visit_assign_op_expr(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::TraitImpl(r) => {
                        Expr::TraitImpl(visitor.visit_trait_impl(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::BinaryExpr(r) => {
                        Expr::BinaryExpr(visitor.visit_binary_expr(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::UnaryExpr(r) => {
                        Expr::UnaryExpr(visitor.visit_unary_expr(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::Index(r) => {
                        Expr::Index(visitor.visit_index_expr(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::ExprKind::Empty(r) => {
                        Expr::Empty(visitor.visit_empty_expr(ctx, $($path)::+::new(r, span, id))?)
                    }
                })
            }

            pub fn walk_expr_same_children<V, Ret>(
                visitor: &mut V,
                ctx: &V::Ctx,
                node: $($path)::+<ast::Expr>,
            ) -> Result<Ret, V::Error>
            where
                V: $visitor<
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
                    EmptyExprRet = Ret
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
                    Expr::Empty(r) => r,
                })
            }

            pub struct VariableExpr<V: $visitor> {
                pub name: V::NameRet,
            }

            pub fn walk_variable_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::VariableExpr>,
            ) -> Result<VariableExpr<V>, V::Error> {
                Ok(VariableExpr { name: visitor.visit_name(ctx, node.name.$ast_ref())? })
            }

            pub struct DirectiveExpr<V: $visitor> {
                pub name: V::NameRet,
                pub subject: V::ExprRet,
            }

            pub fn walk_directive_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::DirectiveExpr>,
            ) -> Result<DirectiveExpr<V>, V::Error> {
                Ok(DirectiveExpr {
                    name: visitor.visit_name(ctx, node.name.$ast_ref())?,
                    subject: visitor.visit_expr(ctx, node.subject.$ast_ref())?,
                })
            }

            pub struct ConstructorCallArg<V: $visitor> {
                pub name: Option<V::NameRet>,
                pub value: V::ExprRet,
            }

            pub fn walk_constructor_call_arg<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ConstructorCallArg>,
            ) -> Result<ConstructorCallArg<V>, V::Error> {
                Ok(ConstructorCallArg {
                    name: node.name.$ref().map(|t| visitor.visit_name(ctx, t.$ast_ref())).transpose()?,
                    value: visitor.visit_expr(ctx, node.value.$ast_ref())?,
                })
            }

            pub struct ConstructorCallExpr<V: $visitor> {
                pub subject: V::ExprRet,
                pub args: V::CollectionContainer<V::ConstructorCallArgRet>,
            }

            pub fn walk_constructor_call_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ConstructorCallExpr>,
            ) -> Result<ConstructorCallExpr<V>, V::Error> {
                Ok(ConstructorCallExpr {
                    subject: visitor.visit_expr(ctx, node.subject.$ast_ref())?,
                    args: V::try_collect_items(
                        ctx,
                        node.args.$iter_ref().map(|e| visitor.visit_constructor_call_arg(ctx, e.$ast_ref())),
                    )?,
                })
            }

            pub struct AccessExpr<V: $visitor> {
                pub subject: V::ExprRet,
                pub property: V::PropertyKindRet,
                pub kind: V::AccessKindRet,
            }

            pub fn walk_access_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::AccessExpr>,
            ) -> Result<AccessExpr<V>, V::Error> {
                Ok(AccessExpr {
                    subject: visitor.visit_expr(ctx, node.subject.$ast_ref())?,
                    property: visitor.visit_property_kind(ctx, node.property.$ast_ref())?,
                    kind: visitor.visit_access_kind(ctx, node.kind)?,
                })
            }

            pub struct RefExpr<V: $visitor> {
                pub inner_expr: V::ExprRet,
                pub mutability: Option<V::MutabilityRet>,
            }

            pub fn walk_ref_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::RefExpr>,
            ) -> Result<RefExpr<V>, V::Error> {
                Ok(RefExpr {
                    inner_expr: visitor.visit_expr(ctx, node.inner_expr.$ast_ref())?,
                    mutability: node
                        .mutability
                        .$ref()
                        .map(|inner| visitor.visit_mutability_modifier(ctx, inner.$ast_ref()))
                        .transpose()?,
                })
            }

            pub struct DerefExpr<V: $visitor>(pub V::ExprRet);

            pub fn walk_deref_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::DerefExpr>,
            ) -> Result<DerefExpr<V>, V::Error> {
                Ok(DerefExpr(visitor.visit_expr(ctx, node.0.$ast_ref())?))
            }

            pub struct UnsafeExpr<V: $visitor>(pub V::ExprRet);

            pub fn walk_unsafe_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::UnsafeExpr>,
            ) -> Result<UnsafeExpr<V>, V::Error> {
                Ok(UnsafeExpr(visitor.visit_expr(ctx, node.0.$ast_ref())?))
            }

            pub struct LitExpr<V: $visitor>(pub V::LitRet);

            pub fn walk_lit_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::LitExpr>,
            ) -> Result<LitExpr<V>, V::Error> {
                Ok(LitExpr(visitor.visit_lit(ctx, node.0.$ast_ref())?))
            }

            pub struct CastExpr<V: $visitor> {
                pub expr: V::ExprRet,
                pub ty: V::TyRet,
            }

            pub fn walk_cast_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::CastExpr>,
            ) -> Result<CastExpr<V>, V::Error> {
                Ok(CastExpr {
                    ty: visitor.visit_ty(ctx, node.ty.$ast_ref())?,
                    expr: visitor.visit_expr(ctx, node.expr.$ast_ref())?,
                })
            }

            pub struct TyExpr<V: $visitor>(pub V::TyRet);

            pub fn walk_ty_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TyExpr>,
            ) -> Result<TyExpr<V>, V::Error> {
                Ok(TyExpr(visitor.visit_ty(ctx, node.0.$ast_ref())?))
            }

            pub struct BlockExpr<V: $visitor>(pub V::BlockRet);

            pub fn walk_block_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::BlockExpr>,
            ) -> Result<BlockExpr<V>, V::Error> {
                Ok(BlockExpr(visitor.visit_block(ctx, node.0.$ast_ref())?))
            }

            pub struct ImportExpr<V: $visitor>(pub V::ImportRet);

            pub fn walk_import_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ImportExpr>,
            ) -> Result<ImportExpr<V>, V::Error> {
                Ok(ImportExpr(visitor.visit_import(ctx, node.0.$ast_ref())?))
            }

            pub enum Lit<V: $visitor> {
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

            pub fn walk_lit<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::Lit>,
            ) -> Result<Lit<V>, V::Error> {
                let (span, id) = (node.span(), node.id());

                Ok(match &$($mutability)? *node {
                    ast::Lit::Str(r) => Lit::Str(visitor.visit_str_lit(ctx, $($path)::+::new(r, span, id))?),
                    ast::Lit::Char(r) => {
                        Lit::Char(visitor.visit_char_lit(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Lit::Int(r) => Lit::Int(visitor.visit_int_lit(ctx, $($path)::+::new(r, span, id))?),
                    ast::Lit::Float(r) => {
                        Lit::Float(visitor.visit_float_lit(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Lit::Bool(r) => {
                        Lit::Bool(visitor.visit_bool_lit(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Lit::Set(r) => Lit::Set(visitor.visit_set_lit(ctx, $($path)::+::new(r, span, id))?),
                    ast::Lit::Map(r) => Lit::Map(visitor.visit_map_lit(ctx, $($path)::+::new(r, span, id))?),
                    ast::Lit::List(r) => {
                        Lit::List(visitor.visit_list_lit(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Lit::Tuple(r) => {
                        Lit::Tuple(visitor.visit_tuple_lit(ctx, $($path)::+::new(r, span, id))?)
                    }
                })
            }

            pub fn walk_lit_same_children<V, Ret>(
                visitor: &mut V,
                ctx: &V::Ctx,
                node: $($path)::+<ast::Lit>,
            ) -> Result<Ret, V::Error>
            where
                V: $visitor<
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

            pub struct MatchCase<V: $visitor> {
                pub pat: V::PatRet,
                pub expr: V::ExprRet,
            }

            pub fn walk_match_case<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::MatchCase>,
            ) -> Result<MatchCase<V>, V::Error> {
                Ok(MatchCase {
                    pat: visitor.visit_pat(ctx, node.pat.$ast_ref())?,
                    expr: visitor.visit_expr(ctx, node.expr.$ast_ref())?,
                })
            }

            pub struct MatchBlock<V: $visitor> {
                pub subject: V::ExprRet,
                pub cases: V::CollectionContainer<V::MatchCaseRet>,
            }

            pub fn walk_match_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::MatchBlock>,
            ) -> Result<MatchBlock<V>, V::Error> {
                Ok(MatchBlock {
                    subject: visitor.visit_expr(ctx, node.subject.$ast_ref())?,
                    cases: V::try_collect_items(
                        ctx,
                        node.cases.$iter_ref().map(|c| visitor.visit_match_case(ctx, c.$ast_ref())),
                    )?,
                })
            }

            pub struct LoopBlock<V: $visitor>(pub V::BlockRet);

            pub fn walk_loop_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::LoopBlock>,
            ) -> Result<LoopBlock<V>, V::Error> {
                Ok(LoopBlock(visitor.visit_block(ctx, node.0.$ast_ref())?))
            }

            pub struct ForLoopBlock<V: $visitor> {
                pub pat: V::PatRet,
                pub iterator: V::ExprRet,
                pub body: V::BlockRet,
            }

            pub fn walk_for_loop_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ForLoopBlock>,
            ) -> Result<ForLoopBlock<V>, V::Error> {
                Ok(ForLoopBlock {
                    pat: visitor.visit_pat(ctx, node.pat.$ast_ref())?,
                    iterator: visitor.visit_expr(ctx, node.iterator.$ast_ref())?,
                    body: visitor.visit_block(ctx, node.body.$ast_ref())?,
                })
            }

            pub struct WhileLoopBlock<V: $visitor> {
                pub condition: V::ExprRet,
                pub body: V::BlockRet,
            }

            pub fn walk_while_loop_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::WhileLoopBlock>,
            ) -> Result<WhileLoopBlock<V>, V::Error> {
                Ok(WhileLoopBlock {
                    condition: visitor.visit_expr(ctx, node.condition.$ast_ref())?,
                    body: visitor.visit_block(ctx, node.body.$ast_ref())?,
                })
            }

            pub struct ModBlock<V: $visitor>(pub V::BodyBlockRet);

            pub fn walk_mod_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ModBlock>,
            ) -> Result<ModBlock<V>, V::Error> {
                Ok(ModBlock(visitor.visit_body_block(ctx, node.0.$ast_ref())?))
            }

            pub struct ImplBlock<V: $visitor>(pub V::BodyBlockRet);

            pub fn walk_impl_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ImplBlock>,
            ) -> Result<ImplBlock<V>, V::Error> {
                Ok(ImplBlock(visitor.visit_body_block(ctx, node.0.$ast_ref())?))
            }

            pub struct IfClause<V: $visitor> {
                pub condition: V::ExprRet,
                pub body: V::BlockRet,
            }

            pub fn walk_if_clause<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::IfClause>,
            ) -> Result<IfClause<V>, V::Error> {
                Ok(IfClause {
                    condition: visitor.visit_expr(ctx, node.condition.$ast_ref())?,
                    body: visitor.visit_block(ctx, node.body.$ast_ref())?,
                })
            }

            pub struct IfBlock<V: $visitor> {
                pub clauses: V::CollectionContainer<V::IfClauseRet>,
                pub otherwise: Option<V::BlockRet>,
            }

            pub fn walk_if_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::IfBlock>,
            ) -> Result<IfBlock<V>, V::Error> {
                Ok(IfBlock {
                    clauses: V::try_collect_items(
                        ctx,
                        node.clauses.$iter_ref().map(|clause| visitor.visit_if_clause(ctx, clause.$ast_ref())),
                    )?,
                    otherwise: node
                        .otherwise
                        .$ref()
                        .map(|body| visitor.visit_block(ctx, body.$ast_ref()))
                        .transpose()?,
                })
            }

            pub struct BodyBlock<V: $visitor> {
                pub statements: V::CollectionContainer<V::ExprRet>,
                pub expr: Option<V::ExprRet>,
            }

            pub fn walk_body_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::BodyBlock>,
            ) -> Result<BodyBlock<V>, V::Error> {
                Ok(BodyBlock {
                    statements: V::try_collect_items(
                        ctx,
                        node.statements.$iter_ref().map(|s| visitor.visit_expr(ctx, s.$ast_ref())),
                    )?,
                    expr: node.expr.$ref().map(|e| visitor.visit_expr(ctx, e.$ast_ref())).transpose()?,
                })
            }

            pub enum Block<V: $visitor> {
                Match(V::MatchBlockRet),
                Loop(V::LoopBlockRet),
                For(V::ForLoopBlockRet),
                While(V::WhileLoopBlockRet),
                Mod(V::ModBlockRet),
                Body(V::BodyBlockRet),
                Impl(V::ImplBlockRet),
                If(V::IfBlockRet),
            }

            pub fn walk_block<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::Block>,
            ) -> Result<Block<V>, V::Error> {
                let (span, id) = (node.span(), node.id());

                Ok(match &$($mutability)? *node {
                    ast::Block::Match(r) => {
                        Block::Match(visitor.visit_match_block(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Block::Loop(r) => {
                        Block::Loop(visitor.visit_loop_block(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Block::For(r) => {
                        Block::For(visitor.visit_for_loop_block(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Block::While(r) => {
                        Block::While(visitor.visit_while_loop_block(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Block::Mod(r) => {
                        Block::Mod(visitor.visit_mod_block(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Block::Body(r) => {
                        Block::Body(visitor.visit_body_block(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Block::Impl(r) => {
                        Block::Impl(visitor.visit_impl_block(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Block::If(r) => {
                        Block::If(visitor.visit_if_block(ctx, $($path)::+::new(r, span, id))?)
                    }
                })
            }

            pub fn walk_block_same_children<V, Ret>(
                visitor: &mut V,
                ctx: &V::Ctx,
                node: $($path)::+<ast::Block>,
            ) -> Result<Ret, V::Error>
            where
                V: $visitor<
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

            pub struct SetLit<V: $visitor> {
                pub elements: V::CollectionContainer<V::ExprRet>,
            }

            pub fn walk_set_lit<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::SetLit>,
            ) -> Result<SetLit<V>, V::Error> {
                Ok(SetLit {
                    elements: V::try_collect_items(
                        ctx,
                        node.elements.$iter_ref().map(|e| visitor.visit_expr(ctx, e.$ast_ref())),
                    )?,
                })
            }

            pub struct MapLitEntry<V: $visitor> {
                pub key: V::ExprRet,
                pub value: V::ExprRet,
            }

            pub fn walk_map_lit_entry<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::MapLitEntry>,
            ) -> Result<MapLitEntry<V>, V::Error> {
                Ok(MapLitEntry {
                    key: visitor.visit_expr(ctx, node.key.$ast_ref())?,
                    value: visitor.visit_expr(ctx, node.value.$ast_ref())?,
                })
            }

            pub struct MapLit<V: $visitor> {
                pub entries: V::CollectionContainer<V::MapLitEntryRet>,
            }

            pub fn walk_map_lit<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::MapLit>,
            ) -> Result<MapLit<V>, V::Error> {
                Ok(MapLit {
                    entries: V::try_collect_items(
                        ctx,
                        node.elements.$iter_ref().map(|e| visitor.visit_map_lit_entry(ctx, e.$ast_ref())),
                    )?,
                })
            }

            pub struct ListLit<V: $visitor> {
                pub elements: V::CollectionContainer<V::ExprRet>,
            }

            pub fn walk_list_lit<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ListLit>,
            ) -> Result<ListLit<V>, V::Error> {
                Ok(ListLit {
                    elements: V::try_collect_items(
                        ctx,
                        node.elements.$iter_ref().map(|e| visitor.visit_expr(ctx, e.$ast_ref())),
                    )?,
                })
            }

            pub struct TupleLitEntry<V: $visitor> {
                pub name: Option<V::NameRet>,
                pub ty: Option<V::TyRet>,
                pub value: V::ExprRet,
            }

            pub fn walk_tuple_lit_entry<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TupleLitEntry>,
            ) -> Result<TupleLitEntry<V>, V::Error> {
                Ok(TupleLitEntry {
                    name: node.name.$ref().map(|t| visitor.visit_name(ctx, t.$ast_ref())).transpose()?,
                    ty: node.ty.$ref().map(|t| visitor.visit_ty(ctx, t.$ast_ref())).transpose()?,
                    value: visitor.visit_expr(ctx, node.value.$ast_ref())?,
                })
            }

            pub struct TupleLit<V: $visitor> {
                pub elements: V::CollectionContainer<V::TupleLitEntryRet>,
            }

            pub fn walk_tuple_lit<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TupleLit>,
            ) -> Result<TupleLit<V>, V::Error> {
                Ok(TupleLit {
                    elements: V::try_collect_items(
                        ctx,
                        node.elements.$iter_ref().map(|e| visitor.visit_tuple_lit_entry(ctx, e.$ast_ref())),
                    )?,
                })
            }

            pub struct TyArg<V: $visitor> {
                pub ty: V::TyRet,
                pub name: Option<V::NameRet>,
            }

            pub fn walk_ty_arg<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TyArg>,
            ) -> Result<TyArg<V>, V::Error> {
                Ok(TyArg {
                    ty: visitor.visit_ty(ctx, node.ty.$ast_ref())?,
                    name: node.name.$ref().map(|t| visitor.visit_name(ctx, t.$ast_ref())).transpose()?,
                })
            }

            pub struct FnTy<V: $visitor> {
                pub params: V::CollectionContainer<V::TyArgRet>,
                pub return_ty: V::TyRet,
            }

            pub fn walk_fn_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::FnTy>,
            ) -> Result<FnTy<V>, V::Error> {
                Ok(FnTy {
                    params: V::try_collect_items(
                        ctx,
                        node.params.$iter_ref().map(|e| visitor.visit_ty_arg(ctx, e.$ast_ref())),
                    )?,
                    return_ty: visitor.visit_ty(ctx, node.return_ty.$ast_ref())?,
                })
            }

            pub struct TupleTy<V: $visitor> {
                pub entries: V::CollectionContainer<V::TyArgRet>,
            }

            pub fn walk_tuple_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TupleTy>,
            ) -> Result<TupleTy<V>, V::Error> {
                Ok(TupleTy {
                    entries: V::try_collect_items(
                        ctx,
                        node.entries.$iter_ref().map(|e| visitor.visit_ty_arg(ctx, e.$ast_ref())),
                    )?,
                })
            }

            pub struct ListTy<V: $visitor> {
                pub inner: V::TyRet,
            }

            pub fn walk_list_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ListTy>,
            ) -> Result<ListTy<V>, V::Error> {
                Ok(ListTy { inner: visitor.visit_ty(ctx, node.inner.$ast_ref())? })
            }

            pub struct SetTy<V: $visitor> {
                pub inner: V::TyRet,
            }

            pub fn walk_set_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::SetTy>,
            ) -> Result<SetTy<V>, V::Error> {
                Ok(SetTy { inner: visitor.visit_ty(ctx, node.inner.$ast_ref())? })
            }

            pub struct MapTy<V: $visitor> {
                pub key: V::TyRet,
                pub value: V::TyRet,
            }

            pub fn walk_map_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::MapTy>,
            ) -> Result<MapTy<V>, V::Error> {
                Ok(MapTy {
                    key: visitor.visit_ty(ctx, node.key.$ast_ref())?,
                    value: visitor.visit_ty(ctx, node.value.$ast_ref())?,
                })
            }

            pub struct NamedTy<V: $visitor> {
                pub name: V::NameRet,
            }

            pub fn walk_named_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::NamedTy>,
            ) -> Result<NamedTy<V>, V::Error> {
                Ok(NamedTy { name: visitor.visit_name(ctx, node.name.$ast_ref())? })
            }

            pub struct AccessTy<V: $visitor> {
                pub subject: V::TyRet,
                pub property: V::NameRet,
            }

            pub fn walk_access_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::AccessTy>,
            ) -> Result<AccessTy<V>, V::Error> {
                Ok(AccessTy {
                    subject: visitor.visit_ty(ctx, node.subject.$ast_ref())?,
                    property: visitor.visit_name(ctx, node.property.$ast_ref())?,
                })
            }

            pub struct RefTy<V: $visitor> {
                pub inner: V::TyRet,
                pub mutability: Option<V::MutabilityRet>,
                pub kind: Option<V::RefKindRet>,
            }

            pub fn walk_ref_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::RefTy>,
            ) -> Result<RefTy<V>, V::Error> {
                Ok(RefTy {
                    inner: visitor.visit_ty(ctx, node.inner.$ast_ref())?,
                    kind: node
                        .kind
                        .$ref()
                        .map(|inner| visitor.visit_ref_kind(ctx, inner.$ast_ref()))
                        .transpose()?,
                    mutability: node
                        .mutability
                        .$ref()
                        .map(|inner| visitor.visit_mutability_modifier(ctx, inner.$ast_ref()))
                        .transpose()?,
                })
            }

            pub struct MergeTy<V: $visitor> {
                pub lhs: V::TyRet,
                pub rhs: V::TyRet,
            }

            pub fn walk_merge_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::MergeTy>,
            ) -> Result<MergeTy<V>, V::Error> {
                Ok(MergeTy {
                    lhs: visitor.visit_ty(ctx, node.lhs.$ast_ref())?,
                    rhs: visitor.visit_ty(ctx, node.rhs.$ast_ref())?,
                })
            }

            pub struct UnionTy<V: $visitor> {
                pub lhs: V::TyRet,
                pub rhs: V::TyRet,
            }

            pub fn walk_union_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::UnionTy>,
            ) -> Result<UnionTy<V>, V::Error> {
                Ok(UnionTy {
                    lhs: visitor.visit_ty(ctx, node.lhs.$ast_ref())?,
                    rhs: visitor.visit_ty(ctx, node.rhs.$ast_ref())?,
                })
            }
            pub struct TyFnCall<V: $visitor> {
                pub subject: V::ExprRet,
                pub args: V::CollectionContainer<V::TyArgRet>,
            }

            pub fn walk_ty_fn_call<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TyFnCall>,
            ) -> Result<TyFnCall<V>, V::Error> {
                Ok(TyFnCall {
                    subject: visitor.visit_expr(ctx, node.subject.$ast_ref())?,
                    args: V::try_collect_items(
                        ctx,
                        node.args.$iter_ref().map(|a| visitor.visit_ty_arg(ctx, a.$ast_ref())),
                    )?,
                })
            }

            pub struct TyFn<V: $visitor> {
                pub params: V::CollectionContainer<V::ParamRet>,
                pub return_ty: V::TyRet,
            }

            pub fn walk_ty_fn<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TyFn>,
            ) -> Result<TyFn<V>, V::Error> {
                Ok(TyFn {
                    params: V::try_collect_items(
                        ctx,
                        node.params.$iter_ref().map(|a| visitor.visit_param(ctx, a.$ast_ref())),
                    )?,
                    return_ty: visitor.visit_ty(ctx, node.return_ty.$ast_ref())?,
                })
            }

            pub enum Ty<V: $visitor> {
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

            pub fn walk_ty<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::Ty>,
            ) -> Result<Ty<V>, V::Error> {
                let (span, id) = (node.span(), node.id());

                Ok(match &$($mutability)? *node {
                    ast::Ty::Access(r) => {
                        Ty::Access(visitor.visit_access_ty(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Ty::Fn(r) => Ty::Fn(visitor.visit_fn_ty(ctx, $($path)::+::new(r, span, id))?),
                    ast::Ty::Tuple(r) => {
                        Ty::Tuple(visitor.visit_tuple_ty(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Ty::List(r) => Ty::List(visitor.visit_list_ty(ctx, $($path)::+::new(r, span, id))?),
                    ast::Ty::Set(r) => Ty::Set(visitor.visit_set_ty(ctx, $($path)::+::new(r, span, id))?),
                    ast::Ty::Map(r) => Ty::Map(visitor.visit_map_ty(ctx, $($path)::+::new(r, span, id))?),
                    ast::Ty::Named(r) => {
                        Ty::Named(visitor.visit_named_ty(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Ty::Ref(r) => Ty::Ref(visitor.visit_ref_ty(ctx, $($path)::+::new(r, span, id))?),
                    ast::Ty::Merge(r) => {
                        Ty::Merge(visitor.visit_merge_ty(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Ty::Union(r) => {
                        Ty::Union(visitor.visit_union_ty(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Ty::TyFn(r) => {
                        Ty::TyFn(visitor.visit_ty_fn_ty(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Ty::TyFnCall(r) => {
                        Ty::TyFnCall(visitor.visit_ty_fn_call(ctx, $($path)::+::new(r, span, id))?)
                    }
                })
            }

            pub fn walk_ty_same_children<V, Ret>(
                visitor: &mut V,
                ctx: &V::Ctx,
                node: $($path)::+<ast::Ty>,
            ) -> Result<Ret, V::Error>
            where
                V: $visitor<
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

            pub enum Pat<V: $visitor> {
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
                Range(V::RangePatRet),
            }

            pub fn walk_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::Pat>,
            ) -> Result<Pat<V>, V::Error> {
                let (span, id) = (node.span(), node.id());

                Ok(match &$($mutability)? *node {
                    ast::Pat::Access(r) => {
                        Pat::Access(visitor.visit_access_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Pat::Constructor(r) => {
                        Pat::Constructor(visitor.visit_constructor_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Pat::Module(r) => {
                        Pat::Module(visitor.visit_module_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Pat::Tuple(r) => {
                        Pat::Tuple(visitor.visit_tuple_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Pat::List(r) => {
                        Pat::List(visitor.visit_list_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Pat::Lit(r) => Pat::Lit(visitor.visit_lit_pat(ctx, $($path)::+::new(r, span, id))?),
                    ast::Pat::Or(r) => Pat::Or(visitor.visit_or_pat(ctx, $($path)::+::new(r, span, id))?),
                    ast::Pat::If(r) => Pat::If(visitor.visit_if_pat(ctx, $($path)::+::new(r, span, id))?),
                    ast::Pat::Binding(r) => {
                        Pat::Binding(visitor.visit_binding_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Pat::Spread(r) => {
                        Pat::Spread(visitor.visit_spread_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Pat::Wild(r) => {
                        Pat::Wild(visitor.visit_wild_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                    ast::Pat::Range(r) => {
                        Pat::Range(visitor.visit_range_pat(ctx, $($path)::+::new(r, span, id))?)
                    }
                })
            }

            pub fn walk_pat_same_children<V, Ret>(
                visitor: &mut V,
                ctx: &V::Ctx,
                node: $($path)::+<ast::Pat>,
            ) -> Result<Ret, V::Error>
            where
                V: $visitor<
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
                    RangePatRet = Ret,
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
                    Pat::Range(r) => r,
                })
            }

            pub struct OrPat<V: $visitor> {
                pub variants: V::CollectionContainer<V::PatRet>,
            }
            pub fn walk_or_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::OrPat>,
            ) -> Result<OrPat<V>, V::Error> {
                Ok(OrPat {
                    variants: V::try_collect_items(
                        ctx,
                        node.variants.$iter_ref().map(|v| visitor.visit_pat(ctx, v.$ast_ref())),
                    )?,
                })
            }

            pub struct AccessPat<V: $visitor> {
                pub subject: V::PatRet,
                pub property: V::NameRet,
            }

            pub fn walk_access_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::AccessPat>,
            ) -> Result<AccessPat<V>, V::Error> {
                Ok(AccessPat {
                    subject: visitor.visit_pat(ctx, node.subject.$ast_ref())?,
                    property: visitor.visit_name(ctx, node.property.$ast_ref())?,
                })
            }

            pub struct ConstructorPat<V: $visitor> {
                pub subject: V::PatRet,
                pub args: V::CollectionContainer<V::TuplePatEntryRet>,
            }
            pub fn walk_constructor_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ConstructorPat>,
            ) -> Result<ConstructorPat<V>, V::Error> {
                Ok(ConstructorPat {
                    subject: visitor.visit_pat(ctx, node.subject.$ast_ref())?,
                    args: V::try_collect_items(
                        ctx,
                        node.fields.$iter_ref().map(|a| visitor.visit_tuple_pat_entry(ctx, a.$ast_ref())),
                    )?,
                })
            }

            pub struct ModulePat<V: $visitor> {
                pub fields: V::CollectionContainer<V::ModulePatEntryRet>,
            }
            pub fn walk_module_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ModulePat>,
            ) -> Result<ModulePat<V>, V::Error> {
                Ok(ModulePat {
                    fields: V::try_collect_items(
                        ctx,
                        node.fields.$iter_ref().map(|a| visitor.visit_module_pat_entry(ctx, a.$ast_ref())),
                    )?,
                })
            }

            pub struct TuplePatEntry<V: $visitor> {
                pub name: Option<V::NameRet>,
                pub pat: V::PatRet,
            }

            pub fn walk_tuple_pat_entry<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TuplePatEntry>,
            ) -> Result<TuplePatEntry<V>, V::Error> {
                Ok(TuplePatEntry {
                    name: node.name.$ref().map(|t| visitor.visit_name(ctx, t.$ast_ref())).transpose()?,
                    pat: visitor.visit_pat(ctx, node.pat.$ast_ref())?,
                })
            }

            pub struct TuplePat<V: $visitor> {
                pub elements: V::CollectionContainer<V::TuplePatEntryRet>,
            }

            pub fn walk_tuple_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TuplePat>,
            ) -> Result<TuplePat<V>, V::Error> {
                Ok(TuplePat {
                    elements: V::try_collect_items(
                        ctx,
                        node.fields.$iter_ref().map(|a| visitor.visit_tuple_pat_entry(ctx, a.$ast_ref())),
                    )?,
                })
            }

            pub struct ListPat<V: $visitor> {
                pub elements: V::CollectionContainer<V::PatRet>,
            }

            pub fn walk_list_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ListPat>,
            ) -> Result<ListPat<V>, V::Error> {
                Ok(ListPat {
                    elements: V::try_collect_items(
                        ctx,
                        node.fields.$iter_ref().map(|a| visitor.visit_pat(ctx, a.$ast_ref())),
                    )?,
                })
            }

            pub struct IfPat<V: $visitor> {
                pub pat: V::PatRet,
                pub condition: V::ExprRet,
            }
            pub fn walk_if_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::IfPat>,
            ) -> Result<IfPat<V>, V::Error> {
                Ok(IfPat {
                    pat: visitor.visit_pat(ctx, node.pat.$ast_ref())?,
                    condition: visitor.visit_expr(ctx, node.condition.$ast_ref())?,
                })
            }

            pub struct BindingPat<V: $visitor> {
                pub name: V::NameRet,
                pub visibility: Option<V::VisibilityRet>,
                pub mutability: Option<V::MutabilityRet>,
            }

            pub fn walk_binding_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::BindingPat>,
            ) -> Result<BindingPat<V>, V::Error> {
                Ok(BindingPat {
                    name: visitor.visit_name(ctx, node.name.$ast_ref())?,
                    visibility: node
                        .visibility
                        .$ref()
                        .map(|inner| visitor.visit_visibility_modifier(ctx, inner.$ast_ref()))
                        .transpose()?,

                    mutability: node
                        .mutability
                        .$ref()
                        .map(|inner| visitor.visit_mutability_modifier(ctx, inner.$ast_ref()))
                        .transpose()?,
                })
            }

            pub struct SpreadPat<V: $visitor> {
                pub name: Option<V::NameRet>,
            }

            pub fn walk_spread_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::SpreadPat>,
            ) -> Result<SpreadPat<V>, V::Error> {
                Ok(SpreadPat {
                    name: node.name.$ref().map(|t| visitor.visit_name(ctx, t.$ast_ref())).transpose()?,
                })
            }

            pub struct LitPat<V: $visitor>(pub V::LitRet);

            pub fn walk_lit_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::LitPat>,
            ) -> Result<LitPat<V>, V::Error> {
                Ok(LitPat(visitor.visit_lit(ctx, node.0.$ast_ref())?))
            }

            pub struct RangePat<V: $visitor> {
                pub lo: V::LitRet,
                pub hi: V::LitRet,
            }

            pub fn walk_range_pat<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::RangePat>,
            ) -> Result<RangePat<V>, V::Error> {
                Ok(RangePat {
                    lo: visitor.visit_lit(ctx, node.lo.$ast_ref())?,
                    hi: visitor.visit_lit(ctx, node.hi.$ast_ref())?,
                })
            }

            pub struct ModulePatEntry<V: $visitor> {
                pub name: V::NameRet,
                pub pat: V::PatRet,
            }
            pub fn walk_module_pat_entry<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ModulePatEntry>,
            ) -> Result<ModulePatEntry<V>, V::Error> {
                Ok(ModulePatEntry {
                    name: visitor.visit_name(ctx, node.name.$ast_ref())?,
                    pat: visitor.visit_pat(ctx, node.pat.$ast_ref())?,
                })
            }

            pub struct ReturnStatement<V: $visitor>(pub Option<V::ExprRet>);
            pub fn walk_return_statement<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::ReturnStatement>,
            ) -> Result<ReturnStatement<V>, V::Error> {
                Ok(ReturnStatement(
                    node.0.$ref().map(|n| visitor.visit_expr(ctx, n.$ast_ref())).transpose()?,
                ))
            }

            pub struct Declaration<V: $visitor> {
                pub pat: V::PatRet,
                pub ty: Option<V::TyRet>,
                pub value: Option<V::ExprRet>,
            }

            pub fn walk_declaration<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::Declaration>,
            ) -> Result<Declaration<V>, V::Error> {
                Ok(Declaration {
                    pat: visitor.visit_pat(ctx, node.pat.$ast_ref())?,
                    ty: node.ty.$ref().map(|t| visitor.visit_ty(ctx, t.$ast_ref())).transpose()?,
                    value: node.value.$ref().map(|t| visitor.visit_expr(ctx, t.$ast_ref())).transpose()?,
                })
            }

            pub struct MergeDeclaration<V: $visitor> {
                pub decl: V::ExprRet,
                pub value: V::ExprRet,
            }

            pub fn walk_merge_declaration<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::MergeDeclaration>,
            ) -> Result<MergeDeclaration<V>, V::Error> {
                Ok(MergeDeclaration {
                    decl: visitor.visit_expr(ctx, node.decl.$ast_ref())?,
                    value: visitor.visit_expr(ctx, node.value.$ast_ref())?,
                })
            }

            pub struct AssignExpr<V: $visitor> {
                pub lhs: V::ExprRet,
                pub rhs: V::ExprRet,
            }

            pub fn walk_assign_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::AssignExpr>,
            ) -> Result<AssignExpr<V>, V::Error> {
                Ok(AssignExpr {
                    lhs: visitor.visit_expr(ctx, node.lhs.$ast_ref())?,
                    rhs: visitor.visit_expr(ctx, node.rhs.$ast_ref())?,
                })
            }

            pub struct AssignOpStatement<V: $visitor> {
                pub lhs: V::ExprRet,
                pub rhs: V::ExprRet,
                pub operator: V::BinOpRet,
            }
            pub fn walk_assign_op_statement<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::AssignOpExpr>,
            ) -> Result<AssignOpStatement<V>, V::Error> {
                Ok(AssignOpStatement {
                    lhs: visitor.visit_expr(ctx, node.lhs.$ast_ref())?,
                    rhs: visitor.visit_expr(ctx, node.rhs.$ast_ref())?,
                    operator: visitor.visit_bin_op(ctx, node.operator.$ast_ref())?,
                })
            }

            pub struct BinaryExpr<V: $visitor> {
                pub lhs: V::ExprRet,
                pub rhs: V::ExprRet,
                pub operator: V::BinOpRet,
            }
            pub fn walk_binary_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::BinaryExpr>,
            ) -> Result<BinaryExpr<V>, V::Error> {
                Ok(BinaryExpr {
                    lhs: visitor.visit_expr(ctx, node.lhs.$ast_ref())?,
                    rhs: visitor.visit_expr(ctx, node.rhs.$ast_ref())?,
                    operator: visitor.visit_bin_op(ctx, node.operator.$ast_ref())?,
                })
            }

            pub struct UnaryExpr<V: $visitor> {
                pub expr: V::ExprRet,
                pub operator: V::UnOpRet,
            }

            pub fn walk_unary_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::UnaryExpr>,
            ) -> Result<UnaryExpr<V>, V::Error> {
                Ok(UnaryExpr {
                    expr: visitor.visit_expr(ctx, node.expr.$ast_ref())?,
                    operator: visitor.visit_un_op(ctx, node.operator.$ast_ref())?,
                })
            }

            pub struct IndexExpr<V: $visitor> {
                pub subject: V::ExprRet,
                pub index_expr: V::ExprRet,
            }

            pub fn walk_index_expr<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::IndexExpr>,
            ) -> Result<IndexExpr<V>, V::Error> {
                Ok(IndexExpr {
                    subject: visitor.visit_expr(ctx, node.subject.$ast_ref())?,
                    index_expr: visitor.visit_expr(ctx, node.index_expr.$ast_ref())?,
                })
            }

            pub struct StructDef<V: $visitor> {
                pub entries: V::CollectionContainer<V::ParamRet>,
            }
            pub fn walk_struct_def<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::StructDef>,
            ) -> Result<StructDef<V>, V::Error> {
                Ok(StructDef {
                    entries: V::try_collect_items(
                        ctx,
                        node.fields.$iter_ref().map(|b| visitor.visit_param(ctx, b.$ast_ref())),
                    )?,
                })
            }

            pub struct EnumDefEntry<V: $visitor> {
                pub name: V::NameRet,
                pub fields: V::CollectionContainer<V::ParamRet>,
            }
            pub fn walk_enum_def_entry<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::EnumDefEntry>,
            ) -> Result<EnumDefEntry<V>, V::Error> {
                Ok(EnumDefEntry {
                    name: visitor.visit_name(ctx, node.name.$ast_ref())?,
                    fields: V::try_collect_items(
                        ctx,
                        node.fields.$iter_ref().map(|b| visitor.visit_param(ctx, b.$ast_ref())),
                    )?,
                })
            }

            pub struct EnumDef<V: $visitor> {
                pub entries: V::CollectionContainer<V::EnumDefEntryRet>,
            }
            pub fn walk_enum_def<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::EnumDef>,
            ) -> Result<EnumDef<V>, V::Error> {
                Ok(EnumDef {
                    entries: V::try_collect_items(
                        ctx,
                        node.entries.$iter_ref().map(|b| visitor.visit_enum_def_entry(ctx, b.$ast_ref())),
                    )?,
                })
            }

            pub struct TyFnDef<V: $visitor> {
                pub params: V::CollectionContainer<V::ParamRet>,
                pub return_ty: Option<V::TyRet>,
                pub body: V::ExprRet,
            }

            pub fn walk_ty_fn_def<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TyFnDef>,
            ) -> Result<TyFnDef<V>, V::Error> {
                Ok(TyFnDef {
                    params: V::try_collect_items(
                        ctx,
                        node.params.$iter_ref().map(|t| visitor.visit_param(ctx, t.$ast_ref())),
                    )?,
                    return_ty: node
                        .return_ty
                        .$ref()
                        .map(|t| visitor.visit_ty(ctx, t.$ast_ref()))
                        .transpose()?,
                    body: visitor.visit_expr(ctx, node.body.$ast_ref())?,
                })
            }

            pub struct TraitDef<V: $visitor> {
                pub members: V::CollectionContainer<V::ExprRet>,
            }

            pub fn walk_trait_def<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TraitDef>,
            ) -> Result<TraitDef<V>, V::Error> {
                Ok(TraitDef {
                    members: V::try_collect_items(
                        ctx,
                        node.members.$iter_ref().map(|t| visitor.visit_expr(ctx, t.$ast_ref())),
                    )?,
                })
            }

            pub struct TraitImpl<V: $visitor> {
                pub ty: V::TyRet,
                pub implementation: V::CollectionContainer<V::ExprRet>,
            }

            pub fn walk_trait_impl<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::TraitImpl>,
            ) -> Result<TraitImpl<V>, V::Error> {
                Ok(TraitImpl {
                    ty: visitor.visit_ty(ctx, node.ty.$ast_ref())?,
                    implementation: V::try_collect_items(
                        ctx,
                        node.implementation.$iter_ref().map(|t| visitor.visit_expr(ctx, t.$ast_ref())),
                    )?,
                })
            }

            pub struct Module<V: $visitor> {
                pub contents: V::CollectionContainer<V::ExprRet>,
            }

            pub fn walk_module<V: $visitor>(
                visitor: &mut V,
                ctx: &V::Ctx,
                $($mutability)? node: $($path)::+<ast::Module>,
            ) -> Result<Module<V>, V::Error> {
                Ok(Module {
                    contents: V::try_collect_items(
                        ctx,
                        node.contents.$iter_ref().map(|s| visitor.visit_expr(ctx, s.$ast_ref())),
                    )?,
                })
            }
        }

    }
}

// Derive both a `mutable` and `immutable` walkers which work with
// the ast mutable and immutable visitors.
//
// @@Cleanup: It would be nice to derive all of the `access` method identifiers
// via another macro...
make_ast_walker!(walk, ast::AstNodeRef, AstVisitor, as_ref, ast_ref, iter,);
make_ast_walker!(walk_mut, ast::AstNodeRefMut, AstVisitorMut, as_mut, ast_ref_mut, iter_mut, mut);
