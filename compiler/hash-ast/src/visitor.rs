use std::iter::FromIterator;

use crate::ast;

pub trait AstVisitor<'c>: Sized {
    type CollectionContainer<T>: FromIterator<T> + Sized;

    type ImportRet;
    fn visit_import(&mut self, node: ast::AstNodeRef<ast::Import>) -> Self::ImportRet;

    type NameRet;
    fn visit_name(&mut self, node: ast::AstNodeRef<ast::Name>) -> Self::NameRet;

    type AccessNameRet;
    fn visit_access_name(
        &mut self,
        node: ast::AstNodeRef<ast::AccessName<'c>>,
    ) -> Self::AccessNameRet;

    type LiteralRet;
    fn visit_literal(&mut self, node: ast::AstNodeRef<ast::Literal<'c>>) -> Self::LiteralRet;

    type ExpressionRet;
    fn visit_expression(
        &mut self,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Self::ExpressionRet;

    type VariableExprRet;
    fn visit_variable_expr(
        &mut self,
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> Self::VariableExprRet;

    type IntrinsicKeyRet;
    fn visit_intrinsic_key(
        &mut self,
        node: ast::AstNodeRef<ast::IntrinsicKey>,
    ) -> Self::IntrinsicKeyRet;

    type FunctionCallArgsRet;
    fn visit_function_call_args(
        &mut self,
        node: ast::AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> Self::FunctionCallArgsRet;

    type FunctionCallExprRet;
    fn visit_function_call_expr(
        &mut self,
        node: ast::AstNodeRef<ast::FunctionCallExpr<'c>>,
    ) -> Self::FunctionCallExprRet;

    type PropertyAccessExprRet;
    fn visit_property_access_expr(
        &mut self,
        node: ast::AstNodeRef<ast::PropertyAccessExpr<'c>>,
    ) -> Self::PropertyAccessExprRet;

    type RefExprRet;
    fn visit_ref_expr(&mut self, node: ast::AstNodeRef<ast::RefExpr<'c>>) -> Self::RefExprRet;

    type DerefExprRet;
    fn visit_deref_expr(&mut self, node: ast::AstNodeRef<ast::DerefExpr<'c>>)
        -> Self::DerefExprRet;

    type LiteralExprRet;
    fn visit_literal_expr(
        &mut self,
        node: ast::AstNodeRef<ast::LiteralExpr<'c>>,
    ) -> Self::LiteralExprRet;

    type TypedExprRet;
    fn visit_typed_expr(&mut self, node: ast::AstNodeRef<ast::TypedExpr<'c>>)
        -> Self::TypedExprRet;

    type BlockExprRet;
    fn visit_block_expr(&mut self, node: ast::AstNodeRef<ast::BlockExpr<'c>>)
        -> Self::BlockExprRet;

    type ImportExprRet;
    fn visit_import_expr(
        &mut self,
        node: ast::AstNodeRef<ast::ImportExpr<'c>>,
    ) -> Self::ImportExprRet;

    type TypeRet;
    fn visit_type(&mut self, node: ast::AstNodeRef<ast::Type<'c>>) -> Self::TypeRet;

    type NamedTypeRet;
    fn visit_named_type(&mut self, node: ast::AstNodeRef<ast::NamedType<'c>>)
        -> Self::NamedTypeRet;

    type RefTypeRet;
    fn visit_ref_type(&mut self, node: ast::AstNodeRef<ast::RefType<'c>>) -> Self::RefTypeRet;

    type RawRefTypeRet;
    fn visit_raw_ref_type(
        &mut self,
        node: ast::AstNodeRef<ast::RawRefType<'c>>,
    ) -> Self::RawRefTypeRet;

    type TypeVarRet;
    fn visit_type_var(&mut self, node: ast::AstNodeRef<ast::TypeVar<'c>>) -> Self::TypeVarRet;

    type ExistentialTypeRet;
    fn visit_existential_type(
        &mut self,
        node: ast::AstNodeRef<ast::ExistentialType>,
    ) -> Self::ExistentialTypeRet;

    type InferTypeRet;
    fn visit_infer_type(&mut self, node: ast::AstNodeRef<ast::InferType>) -> Self::InferTypeRet;

    type MapLiteralRet;
    fn visit_map_literal(
        &mut self,
        node: ast::AstNodeRef<ast::MapLiteral<'c>>,
    ) -> Self::MapLiteralRet;

    type MapLiteralEntryRet;
    fn visit_map_literal_entry(
        &mut self,
        node: ast::AstNodeRef<ast::MapLiteralEntry<'c>>,
    ) -> Self::MapLiteralEntryRet;

    type ListLiteralRet;
    fn visit_list_literal(
        &mut self,
        node: ast::AstNodeRef<ast::ListLiteral<'c>>,
    ) -> Self::ListLiteralRet;

    type SetLiteralRet;
    fn visit_set_literal(
        &mut self,
        node: ast::AstNodeRef<ast::SetLiteral<'c>>,
    ) -> Self::SetLiteralRet;

    type TupleLiteralRet;
    fn visit_tuple_literal(
        &mut self,
        node: ast::AstNodeRef<ast::TupleLiteral<'c>>,
    ) -> Self::TupleLiteralRet;

    type StrLiteralRet;
    fn visit_str_literal(&mut self, node: ast::AstNodeRef<ast::StrLiteral>) -> Self::StrLiteralRet;

    type CharLiteralRet;
    fn visit_char_literal(
        &mut self,
        node: ast::AstNodeRef<ast::CharLiteral>,
    ) -> Self::CharLiteralRet;

    type FloatLiteralRet;
    fn visit_float_literal(
        &mut self,
        node: ast::AstNodeRef<ast::FloatLiteral>,
    ) -> Self::FloatLiteralRet;

    type IntLiteralRet;
    fn visit_int_literal(&mut self, node: ast::AstNodeRef<ast::IntLiteral>) -> Self::IntLiteralRet;

    type StructLiteralRet;
    fn visit_struct_literal(
        &mut self,
        node: ast::AstNodeRef<ast::StructLiteral<'c>>,
    ) -> Self::StructLiteralRet;

    type StructLiteralEntryRet;
    fn visit_struct_literal_entry(
        &mut self,
        node: ast::AstNodeRef<ast::StructLiteralEntry<'c>>,
    ) -> Self::StructLiteralEntryRet;

    type FunctionDefRet;
    fn visit_function_def(
        &mut self,
        node: ast::AstNodeRef<ast::FunctionDef<'c>>,
    ) -> Self::FunctionDefRet;

    type FunctionDefArgRet;
    fn visit_function_def_arg(
        &mut self,
        node: ast::AstNodeRef<ast::FunctionDefArg<'c>>,
    ) -> Self::FunctionDefArgRet;

    type BlockRet;
    fn visit_block(&mut self, node: ast::AstNodeRef<ast::Block<'c>>) -> Self::BlockRet;

    type MatchCaseRet;
    fn visit_match_case(&mut self, node: ast::AstNodeRef<ast::MatchCase<'c>>)
        -> Self::MatchCaseRet;

    type MatchBlockRet;
    fn visit_match_block(
        &mut self,
        node: ast::AstNodeRef<ast::MatchBlock<'c>>,
    ) -> Self::MatchBlockRet;

    type LoopBlockRet;
    fn visit_loop_block(&mut self, node: ast::AstNodeRef<ast::LoopBlock<'c>>)
        -> Self::LoopBlockRet;

    type BodyBlockRet;
    fn visit_body_block(&mut self, node: ast::AstNodeRef<ast::BodyBlock<'c>>)
        -> Self::BodyBlockRet;

    type StatementRet;
    fn visit_statement(&mut self, node: ast::AstNodeRef<ast::Statement<'c>>) -> Self::StatementRet;

    type ExprStatementRet;
    fn visit_expr_statement(
        &mut self,
        node: ast::AstNodeRef<ast::ExprStatement<'c>>,
    ) -> Self::ExprStatementRet;

    type ReturnStatementRet;
    fn visit_return_statement(
        &mut self,
        node: ast::AstNodeRef<ast::ReturnStatement<'c>>,
    ) -> Self::ReturnStatementRet;

    type BlockStatementRet;
    fn visit_block_statement(
        &mut self,
        node: ast::AstNodeRef<ast::BlockStatement<'c>>,
    ) -> Self::BlockStatementRet;

    type BreakStatementRet;
    fn visit_break_statement(
        &mut self,
        node: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Self::BreakStatementRet;

    type ContinueStatementRet;
    fn visit_continue_statement(
        &mut self,
        node: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Self::ContinueStatementRet;

    type LetStatementRet;
    fn visit_let_statement(
        &mut self,
        node: ast::AstNodeRef<ast::LetStatement<'c>>,
    ) -> Self::LetStatementRet;

    type AssignStatementRet;
    fn visit_assign_statement(
        &mut self,
        node: ast::AstNodeRef<ast::AssignStatement<'c>>,
    ) -> Self::AssignStatementRet;

    type StructDefEntryRet;
    fn visit_struct_def_entry(
        &mut self,
        node: ast::AstNodeRef<ast::StructDefEntry<'c>>,
    ) -> Self::StructDefEntryRet;

    type StructDefRet;
    fn visit_struct_def(&mut self, node: ast::AstNodeRef<ast::StructDef<'c>>)
        -> Self::StructDefRet;

    type EnumDefEntryRet;
    fn visit_enum_def_entry(
        &mut self,
        node: ast::AstNodeRef<ast::EnumDefEntry<'c>>,
    ) -> Self::EnumDefEntryRet;

    type EnumDefRet;
    fn visit_enum_def(&mut self, node: ast::AstNodeRef<ast::EnumDef<'c>>) -> Self::EnumDefRet;

    type TraitDefRet;
    fn visit_trait_def(&mut self, node: ast::AstNodeRef<ast::TraitDef<'c>>) -> Self::TraitDefRet;

    type PatternRet;
    fn visit_pattern(&mut self, node: ast::AstNodeRef<ast::Pattern<'c>>) -> Self::PatternRet;

    type TraitBoundRet;
    fn visit_trait_bound(
        &mut self,
        node: ast::AstNodeRef<ast::TraitBound<'c>>,
    ) -> Self::TraitBoundRet;

    type BoundRet;
    fn visit_bound(&mut self, node: ast::AstNodeRef<ast::Bound<'c>>) -> Self::BoundRet;

    type EnumPatternRet;
    fn visit_enum_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::EnumPattern<'c>>,
    ) -> Self::EnumPatternRet;

    type StructPatternRet;
    fn visit_struct_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::StructPattern<'c>>,
    ) -> Self::StructPatternRet;

    type NamespacePatternRet;
    fn visit_namespace_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> Self::NamespacePatternRet;

    type TuplePatternRet;
    fn visit_tuple_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Self::TuplePatternRet;

    type StrLiteralPatternRet;
    fn visit_str_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::StrLiteralPattern>,
    ) -> Self::StrLiteralPatternRet;

    type CharLiteralPatternRet;
    fn visit_char_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::CharLiteralPattern>,
    ) -> Self::CharLiteralPatternRet;

    type IntLiteralPatternRet;
    fn visit_int_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::IntLiteralPattern>,
    ) -> Self::IntLiteralPatternRet;

    type FloatLiteralPatternRet;
    fn visit_float_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::FloatLiteralPattern>,
    ) -> Self::FloatLiteralPatternRet;

    type LiteralPatternRet;
    fn visit_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Self::LiteralPatternRet;

    type OrPatternRet;
    fn visit_or_pattern(&mut self, node: ast::AstNodeRef<ast::OrPattern<'c>>)
        -> Self::OrPatternRet;

    type IfPatternRet;
    fn visit_if_pattern(&mut self, node: ast::AstNodeRef<ast::IfPattern<'c>>)
        -> Self::IfPatternRet;

    type BindingPatternRet;
    fn visit_binding_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::BindingPattern<'c>>,
    ) -> Self::BindingPatternRet;

    type IgnorePatternRet;
    fn visit_ignore_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::IgnorePattern>,
    ) -> Self::IgnorePatternRet;

    type DestructuringPatternRet;
    fn visit_destructuring_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::DestructuringPattern<'c>>,
    ) -> Self::DestructuringPatternRet;

    type ModuleRet;
    fn visit_module(&mut self, node: ast::AstNodeRef<ast::Module<'c>>) -> Self::ModuleRet;
}

pub mod walk {
    use super::ast;
    use super::AstVisitor;

    pub struct FunctionDefArg<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
    }

    pub fn walk_function_def_arg<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::FunctionDefArg<'c>>,
    ) -> FunctionDefArg<'c, V> {
        FunctionDefArg {
            name: visitor.visit_name(node.name.ast_ref()),
            ty: node.ty.as_ref().map(|t| visitor.visit_type(t.ast_ref())),
        }
    }

    pub struct FunctionDef<'c, V: AstVisitor<'c>> {
        pub args: V::CollectionContainer<V::FunctionDefArgRet>,
        pub return_ty: Option<V::TypeRet>,
        pub fn_body: V::ExpressionRet,
    }

    pub fn walk_function_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::FunctionDef<'c>>,
    ) -> FunctionDef<'c, V> {
        FunctionDef {
            args: node
                .args
                .iter()
                .map(|a| visitor.visit_function_def_arg(a.ast_ref()))
                .collect(),
            return_ty: node
                .return_ty
                .as_ref()
                .map(|t| visitor.visit_type(t.ast_ref())),
            fn_body: visitor.visit_expression(node.fn_body.ast_ref()),
        }
    }

    pub struct StructLiteral<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
        pub type_args: V::CollectionContainer<V::TypeRet>,
        pub entries: V::CollectionContainer<V::StructLiteralEntryRet>,
    }

    pub fn walk_struct_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::StructLiteral<'c>>,
    ) -> StructLiteral<'c, V> {
        StructLiteral {
            name: visitor.visit_access_name(node.name.ast_ref()),
            type_args: node
                .type_args
                .iter()
                .map(|a| visitor.visit_type(a.ast_ref()))
                .collect(),
            entries: node
                .entries
                .iter()
                .map(|e| visitor.visit_struct_literal_entry(e.ast_ref()))
                .collect(),
        }
    }

    pub struct StructLiteralEntry<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub value: V::ExpressionRet,
    }

    pub fn walk_struct_literal_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::StructLiteralEntry<'c>>,
    ) -> StructLiteralEntry<'c, V> {
        StructLiteralEntry {
            name: visitor.visit_name(node.name.ast_ref()),
            value: visitor.visit_expression(node.value.ast_ref()),
        }
    }

    pub enum Expression<'c, V: AstVisitor<'c>> {
        FunctionCall(V::FunctionCallExprRet),
        Intrinsic(V::IntrinsicKeyRet),
        Variable(V::VariableExprRet),
        PropertyAccess(V::PropertyAccessExprRet),
        Ref(V::RefExprRet),
        Deref(V::DerefExprRet),
        LiteralExpr(V::LiteralExprRet),
        Typed(V::TypedExprRet),
        Block(V::BlockExprRet),
        Import(V::ImportExprRet),
    }

    pub fn walk_expression<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Expression<'c, V> {
        match node.kind() {
            ast::ExpressionKind::FunctionCall(inner) => {
                Expression::FunctionCall(visitor.visit_function_call_expr(node.with_body(inner)))
            }
            ast::ExpressionKind::Intrinsic(inner) => {
                Expression::Intrinsic(visitor.visit_intrinsic_key(node.with_body(inner)))
            }
            ast::ExpressionKind::Variable(inner) => {
                Expression::Variable(visitor.visit_variable_expr(node.with_body(inner)))
            }
            ast::ExpressionKind::PropertyAccess(inner) => Expression::PropertyAccess({
                visitor.visit_property_access_expr(node.with_body(inner))
            }),
            ast::ExpressionKind::Ref(inner) => {
                Expression::Ref(visitor.visit_ref_expr(node.with_body(inner)))
            }
            ast::ExpressionKind::Deref(inner) => {
                Expression::Deref(visitor.visit_deref_expr(node.with_body(inner)))
            }
            ast::ExpressionKind::LiteralExpr(inner) => {
                Expression::LiteralExpr(visitor.visit_literal_expr(node.with_body(inner)))
            }
            ast::ExpressionKind::Typed(inner) => {
                Expression::Typed(visitor.visit_typed_expr(node.with_body(inner)))
            }
            ast::ExpressionKind::Block(inner) => {
                Expression::Block(visitor.visit_block_expr(node.with_body(inner)))
            }
            ast::ExpressionKind::Import(inner) => {
                Expression::Import(visitor.visit_import_expr(node.with_body(inner)))
            }
        }
    }

    pub fn walk_expression_same_children<'c, V, Ret>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Ret
    where
        V: AstVisitor<
            'c,
            FunctionCallExprRet = Ret,
            IntrinsicKeyRet = Ret,
            VariableExprRet = Ret,
            PropertyAccessExprRet = Ret,
            RefExprRet = Ret,
            DerefExprRet = Ret,
            LiteralExprRet = Ret,
            TypedExprRet = Ret,
            BlockExprRet = Ret,
            ImportExprRet = Ret,
        >,
    {
        match walk_expression(visitor, node) {
            Expression::FunctionCall(r) => r,
            Expression::Intrinsic(r) => r,
            Expression::Variable(r) => r,
            Expression::PropertyAccess(r) => r,
            Expression::Ref(r) => r,
            Expression::Deref(r) => r,
            Expression::LiteralExpr(r) => r,
            Expression::Typed(r) => r,
            Expression::Block(r) => r,
            Expression::Import(r) => r,
        }
    }

    pub struct VariableExpr<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
        pub type_args: V::CollectionContainer<V::TypeRet>,
    }

    pub fn walk_variable_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> VariableExpr<'c, V> {
        VariableExpr {
            name: visitor.visit_access_name(node.name.ast_ref()),
            type_args: node
                .type_args
                .iter()
                .map(|t| visitor.visit_type(t.ast_ref()))
                .collect(),
        }
    }

    pub struct FunctionCallArgs<'c, V: AstVisitor<'c>> {
        pub entries: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_function_call_args<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> FunctionCallArgs<'c, V> {
        FunctionCallArgs {
            entries: node
                .entries
                .iter()
                .map(|e| visitor.visit_expression(e.ast_ref()))
                .collect(),
        }
    }

    pub struct FunctionCallExpr<'c, V: AstVisitor<'c>> {
        pub subject: V::ExpressionRet,
        pub args: V::FunctionCallArgsRet,
    }

    pub fn walk_function_call_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::FunctionCallExpr<'c>>,
    ) -> FunctionCallExpr<'c, V> {
        FunctionCallExpr {
            subject: visitor.visit_expression(node.subject.ast_ref()),
            args: visitor.visit_function_call_args(node.args.ast_ref()),
        }
    }

    pub struct PropertyAccessExpr<'c, V: AstVisitor<'c>> {
        pub subject: V::ExpressionRet,
        pub property: V::NameRet,
    }

    pub fn walk_property_access_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::PropertyAccessExpr<'c>>,
    ) -> PropertyAccessExpr<'c, V> {
        PropertyAccessExpr {
            subject: visitor.visit_expression(node.subject.ast_ref()),
            property: visitor.visit_name(node.property.ast_ref()),
        }
    }

    pub struct RefExpr<'c, V: AstVisitor<'c>> {
        pub inner_expr: V::ExpressionRet,
    }

    pub fn walk_ref_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::RefExpr<'c>>,
    ) -> RefExpr<'c, V> {
        RefExpr {
            inner_expr: visitor.visit_expression(node.inner_expr.ast_ref()),
        }
    }

    pub struct DerefExpr<'c, V: AstVisitor<'c>>(pub V::ExpressionRet);

    pub fn walk_deref_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::DerefExpr<'c>>,
    ) -> DerefExpr<'c, V> {
        DerefExpr(visitor.visit_expression(node.0.ast_ref()))
    }

    pub struct LiteralExpr<'c, V: AstVisitor<'c>>(pub V::LiteralRet);

    pub fn walk_literal_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::LiteralExpr<'c>>,
    ) -> LiteralExpr<'c, V> {
        LiteralExpr(visitor.visit_literal(node.0.ast_ref()))
    }

    pub struct TypedExpr<'c, V: AstVisitor<'c>> {
        pub ty: V::TypeRet,
        pub expr: V::ExpressionRet,
    }

    pub fn walk_typed_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::TypedExpr<'c>>,
    ) -> TypedExpr<'c, V> {
        TypedExpr {
            ty: visitor.visit_type(node.ty.ast_ref()),
            expr: visitor.visit_expression(node.expr.ast_ref()),
        }
    }

    pub struct BlockExpr<'c, V: AstVisitor<'c>>(pub V::BlockRet);

    pub fn walk_block_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::BlockExpr<'c>>,
    ) -> BlockExpr<'c, V> {
        BlockExpr(visitor.visit_block(node.0.ast_ref()))
    }

    pub struct ImportExpr<'c, V: AstVisitor<'c>>(pub V::ImportRet);

    pub fn walk_import_expr<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::ImportExpr<'c>>,
    ) -> ImportExpr<'c, V> {
        ImportExpr(visitor.visit_import(node.0.ast_ref()))
    }

    pub enum Literal<'c, V: AstVisitor<'c>> {
        Str(V::StrLiteralRet),
        Char(V::CharLiteralRet),
        Int(V::IntLiteralRet),
        Float(V::FloatLiteralRet),
        Set(V::SetLiteralRet),
        Map(V::MapLiteralRet),
        List(V::ListLiteralRet),
        Tuple(V::TupleLiteralRet),
        Struct(V::StructLiteralRet),
        Function(V::FunctionDefRet),
    }

    pub fn walk_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Literal<'c>>,
    ) -> Literal<'c, V> {
        match &*node {
            ast::Literal::Str(r) => Literal::Str(visitor.visit_str_literal(node.with_body(r))),
            ast::Literal::Char(r) => Literal::Char(visitor.visit_char_literal(node.with_body(r))),
            ast::Literal::Int(r) => Literal::Int(visitor.visit_int_literal(node.with_body(r))),
            ast::Literal::Float(r) => {
                Literal::Float(visitor.visit_float_literal(node.with_body(r)))
            }
            ast::Literal::Set(r) => Literal::Set(visitor.visit_set_literal(node.with_body(r))),
            ast::Literal::Map(r) => Literal::Map(visitor.visit_map_literal(node.with_body(r))),
            ast::Literal::List(r) => Literal::List(visitor.visit_list_literal(node.with_body(r))),
            ast::Literal::Tuple(r) => {
                Literal::Tuple(visitor.visit_tuple_literal(node.with_body(r)))
            }
            ast::Literal::Struct(r) => {
                Literal::Struct(visitor.visit_struct_literal(node.with_body(r)))
            }
            ast::Literal::Function(r) => {
                Literal::Function(visitor.visit_function_def(node.with_body(r)))
            }
        }
    }

    pub fn walk_literal_same_children<'c, V, Ret>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Literal<'c>>,
    ) -> Ret
    where
        V: AstVisitor<
            'c,
            StrLiteralRet = Ret,
            CharLiteralRet = Ret,
            IntLiteralRet = Ret,
            FloatLiteralRet = Ret,
            SetLiteralRet = Ret,
            MapLiteralRet = Ret,
            ListLiteralRet = Ret,
            TupleLiteralRet = Ret,
            StructLiteralRet = Ret,
            FunctionDefRet = Ret,
        >,
    {
        match walk_literal(visitor, node) {
            Literal::Str(r) => r,
            Literal::Char(r) => r,
            Literal::Int(r) => r,
            Literal::Float(r) => r,
            Literal::Set(r) => r,
            Literal::Map(r) => r,
            Literal::List(r) => r,
            Literal::Tuple(r) => r,
            Literal::Struct(r) => r,
            Literal::Function(r) => r,
        }
    }

    pub struct MatchCase<'c, V: AstVisitor<'c>> {
        pub pattern: V::PatternRet,
        pub expr: V::ExpressionRet,
    }

    pub fn walk_match_case<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::MatchCase<'c>>,
    ) -> MatchCase<'c, V> {
        MatchCase {
            pattern: visitor.visit_pattern(node.pattern.ast_ref()),
            expr: visitor.visit_expression(node.expr.ast_ref()),
        }
    }

    pub struct MatchBlock<'c, V: AstVisitor<'c>> {
        pub subject: V::ExpressionRet,
        pub cases: V::CollectionContainer<V::MatchCaseRet>,
    }

    pub fn walk_match_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::MatchBlock<'c>>,
    ) -> MatchBlock<'c, V> {
        MatchBlock {
            subject: visitor.visit_expression(node.subject.ast_ref()),
            cases: node
                .cases
                .iter()
                .map(|c| visitor.visit_match_case(c.ast_ref()))
                .collect(),
        }
    }

    pub struct LoopBlock<'c, V: AstVisitor<'c>>(pub V::BlockRet);

    pub fn walk_loop_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::LoopBlock<'c>>,
    ) -> LoopBlock<'c, V> {
        LoopBlock(visitor.visit_block(node.0.ast_ref()))
    }

    pub struct BodyBlock<'c, V: AstVisitor<'c>> {
        pub statements: V::CollectionContainer<V::StatementRet>,
        pub expr: Option<V::ExpressionRet>,
    }

    pub fn walk_body_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::BodyBlock<'c>>,
    ) -> BodyBlock<'c, V> {
        BodyBlock {
            statements: node
                .statements
                .iter()
                .map(|s| visitor.visit_statement(s.ast_ref()))
                .collect(),
            expr: node
                .expr
                .as_ref()
                .map(|e| visitor.visit_expression(e.ast_ref())),
        }
    }

    pub enum Block<'c, V: AstVisitor<'c>> {
        Match(V::MatchBlockRet),
        Loop(V::LoopBlockRet),
        Body(V::BodyBlockRet),
    }

    pub fn walk_block<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Block<'c>>,
    ) -> Block<'c, V> {
        match &*node {
            ast::Block::Match(r) => Block::Match(visitor.visit_match_block(node.with_body(r))),
            ast::Block::Loop(r) => Block::Loop(visitor.visit_loop_block(node.with_body(r))),
            ast::Block::Body(r) => Block::Body(visitor.visit_body_block(node.with_body(r))),
        }
    }

    pub fn walk_block_same_children<'c, V, Ret>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Block<'c>>,
    ) -> Ret
    where
        V: AstVisitor<'c, MatchBlockRet = Ret, LoopBlockRet = Ret, BodyBlockRet = Ret>,
    {
        match walk_block(visitor, node) {
            Block::Match(r) => r,
            Block::Loop(r) => r,
            Block::Body(r) => r,
        }
    }

    pub struct SetLiteral<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_set_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::SetLiteral<'c>>,
    ) -> SetLiteral<'c, V> {
        SetLiteral {
            elements: node
                .elements
                .iter()
                .map(|e| visitor.visit_expression(e.ast_ref()))
                .collect(),
        }
    }

    pub struct MapLiteralEntry<'c, V: AstVisitor<'c>> {
        pub key: V::ExpressionRet,
        pub value: V::ExpressionRet,
    }

    pub fn walk_map_literal_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::MapLiteralEntry<'c>>,
    ) -> MapLiteralEntry<'c, V> {
        MapLiteralEntry {
            key: visitor.visit_expression(node.key.ast_ref()),
            value: visitor.visit_expression(node.value.ast_ref()),
        }
    }

    pub struct MapLiteral<'c, V: AstVisitor<'c>> {
        pub entries: V::CollectionContainer<V::MapLiteralEntryRet>,
    }

    pub fn walk_map_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::MapLiteral<'c>>,
    ) -> MapLiteral<'c, V> {
        MapLiteral {
            entries: node
                .elements
                .iter()
                .map(|e| visitor.visit_map_literal_entry(e.ast_ref()))
                .collect(),
        }
    }

    pub struct ListLiteral<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_list_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::ListLiteral<'c>>,
    ) -> ListLiteral<'c, V> {
        ListLiteral {
            elements: node
                .elements
                .iter()
                .map(|e| visitor.visit_expression(e.ast_ref()))
                .collect(),
        }
    }

    pub struct TupleLiteral<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::ExpressionRet>,
    }

    pub fn walk_tuple_literal<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::TupleLiteral<'c>>,
    ) -> TupleLiteral<'c, V> {
        TupleLiteral {
            elements: node
                .elements
                .iter()
                .map(|e| visitor.visit_expression(e.ast_ref()))
                .collect(),
        }
    }

    pub struct NamedType<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
        pub type_args: V::CollectionContainer<V::TypeRet>,
    }

    pub fn walk_named_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::NamedType<'c>>,
    ) -> NamedType<'c, V> {
        NamedType {
            name: visitor.visit_access_name(node.name.ast_ref()),
            type_args: node
                .type_args
                .iter()
                .map(|e| visitor.visit_type(e.ast_ref()))
                .collect(),
        }
    }

    pub struct RefType<'c, V: AstVisitor<'c>>(pub V::TypeRet);

    pub fn walk_ref_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::RefType<'c>>,
    ) -> RefType<'c, V> {
        RefType(visitor.visit_type(node.0.ast_ref()))
    }

    pub struct RawRefType<'c, V: AstVisitor<'c>>(pub V::TypeRet);

    pub fn walk_raw_ref_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::RawRefType<'c>>,
    ) -> RawRefType<'c, V> {
        RawRefType(visitor.visit_type(node.0.ast_ref()))
    }

    pub struct TypeVar<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
    }

    pub fn walk_type_var<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::TypeVar<'c>>,
    ) -> TypeVar<'c, V> {
        TypeVar {
            name: visitor.visit_name(node.name.ast_ref()),
        }
    }

    pub enum Type<'c, V: AstVisitor<'c>> {
        Named(V::NamedTypeRet),
        Ref(V::RefTypeRet),
        RawRef(V::RawRefTypeRet),
        TypeVar(V::TypeVarRet),
        Existential(V::ExistentialTypeRet),
        Infer(V::InferTypeRet),
    }

    pub fn walk_type<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Type<'c>>,
    ) -> Type<'c, V> {
        match &*node {
            ast::Type::Named(r) => Type::Named(visitor.visit_named_type(node.with_body(r))),
            ast::Type::Ref(r) => Type::Ref(visitor.visit_ref_type(node.with_body(r))),
            ast::Type::RawRef(r) => Type::RawRef(visitor.visit_raw_ref_type(node.with_body(r))),
            ast::Type::TypeVar(r) => Type::TypeVar(visitor.visit_type_var(node.with_body(r))),
            ast::Type::Existential(r) => {
                Type::Existential(visitor.visit_existential_type(node.with_body(r)))
            }
            ast::Type::Infer(r) => Type::Infer(visitor.visit_infer_type(node.with_body(r))),
        }
    }

    pub fn walk_type_same_children<'c, V, Ret>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Type<'c>>,
    ) -> Ret
    where
        V: AstVisitor<
            'c,
            NamedTypeRet = Ret,
            RefTypeRet = Ret,
            RawRefTypeRet = Ret,
            TypeVarRet = Ret,
            ExistentialTypeRet = Ret,
            InferTypeRet = Ret,
        >,
    {
        match walk_type(visitor, node) {
            Type::Named(r) => r,
            Type::Ref(r) => r,
            Type::RawRef(r) => r,
            Type::TypeVar(r) => r,
            Type::Existential(r) => r,
            Type::Infer(r) => r,
        }
    }

    pub enum Pattern<'c, V: AstVisitor<'c>> {
        Enum(V::EnumPatternRet),
        Struct(V::StructPatternRet),
        Namespace(V::NamespacePatternRet),
        Tuple(V::TuplePatternRet),
        Literal(V::LiteralPatternRet),
        Or(V::OrPatternRet),
        If(V::IfPatternRet),
        Binding(V::BindingPatternRet),
        Ignore(V::IgnorePatternRet),
    }

    pub fn walk_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Pattern<'c>>,
    ) -> Pattern<'c, V> {
        match &*node {
            ast::Pattern::Enum(r) => Pattern::Enum(visitor.visit_enum_pattern(node.with_body(r))),
            ast::Pattern::Struct(r) => {
                Pattern::Struct(visitor.visit_struct_pattern(node.with_body(r)))
            }
            ast::Pattern::Namespace(r) => {
                Pattern::Namespace(visitor.visit_namespace_pattern(node.with_body(r)))
            }
            ast::Pattern::Tuple(r) => {
                Pattern::Tuple(visitor.visit_tuple_pattern(node.with_body(r)))
            }
            ast::Pattern::Literal(r) => {
                Pattern::Literal(visitor.visit_literal_pattern(node.with_body(r)))
            }
            ast::Pattern::Or(r) => Pattern::Or(visitor.visit_or_pattern(node.with_body(r))),
            ast::Pattern::If(r) => Pattern::If(visitor.visit_if_pattern(node.with_body(r))),
            ast::Pattern::Binding(r) => {
                Pattern::Binding(visitor.visit_binding_pattern(node.with_body(r)))
            }
            ast::Pattern::Ignore(r) => {
                Pattern::Ignore(visitor.visit_ignore_pattern(node.with_body(r)))
            }
        }
    }

    pub fn walk_pattern_same_children<'c, V, Ret>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Pattern<'c>>,
    ) -> Ret
    where
        V: AstVisitor<
            'c,
            EnumPatternRet = Ret,
            StructPatternRet = Ret,
            NamespacePatternRet = Ret,
            TuplePatternRet = Ret,
            LiteralPatternRet = Ret,
            OrPatternRet = Ret,
            IfPatternRet = Ret,
            BindingPatternRet = Ret,
            IgnorePatternRet = Ret,
        >,
    {
        match walk_pattern(visitor, node) {
            Pattern::Enum(r) => r,
            Pattern::Struct(r) => r,
            Pattern::Namespace(r) => r,
            Pattern::Tuple(r) => r,
            Pattern::Literal(r) => r,
            Pattern::Or(r) => r,
            Pattern::If(r) => r,
            Pattern::Binding(r) => r,
            Pattern::Ignore(r) => r,
        }
    }

    pub struct OrPattern<'c, V: AstVisitor<'c>> {
        pub variants: V::CollectionContainer<V::PatternRet>,
    }
    pub fn walk_or_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::OrPattern<'c>>,
    ) -> OrPattern<'c, V> {
        OrPattern {
            variants: node
                .variants
                .iter()
                .map(|v| visitor.visit_pattern(v.ast_ref()))
                .collect(),
        }
    }

    pub struct EnumPattern<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
        pub args: V::CollectionContainer<V::PatternRet>,
    }
    pub fn walk_enum_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::EnumPattern<'c>>,
    ) -> EnumPattern<'c, V> {
        EnumPattern {
            name: visitor.visit_access_name(node.name.ast_ref()),
            args: node
                .args
                .iter()
                .map(|a| visitor.visit_pattern(a.ast_ref()))
                .collect(),
        }
    }

    pub struct StructPattern<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
        pub entries: V::CollectionContainer<V::DestructuringPatternRet>,
    }
    pub fn walk_struct_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::StructPattern<'c>>,
    ) -> StructPattern<'c, V> {
        StructPattern {
            name: visitor.visit_access_name(node.name.ast_ref()),
            entries: node
                .entries
                .iter()
                .map(|a| visitor.visit_destructuring_pattern(a.ast_ref()))
                .collect(),
        }
    }

    pub struct NamespacePattern<'c, V: AstVisitor<'c>> {
        pub patterns: V::CollectionContainer<V::DestructuringPatternRet>,
    }
    pub fn walk_namespace_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> NamespacePattern<'c, V> {
        NamespacePattern {
            patterns: node
                .patterns
                .iter()
                .map(|a| visitor.visit_destructuring_pattern(a.ast_ref()))
                .collect(),
        }
    }

    pub struct TuplePattern<'c, V: AstVisitor<'c>> {
        pub elements: V::CollectionContainer<V::PatternRet>,
    }
    pub fn walk_tuple_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> TuplePattern<'c, V> {
        TuplePattern {
            elements: node
                .elements
                .iter()
                .map(|a| visitor.visit_pattern(a.ast_ref()))
                .collect(),
        }
    }

    pub struct IfPattern<'c, V: AstVisitor<'c>> {
        pub pattern: V::PatternRet,
        pub condition: V::ExpressionRet,
    }
    pub fn walk_if_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::IfPattern<'c>>,
    ) -> IfPattern<'c, V> {
        IfPattern {
            pattern: visitor.visit_pattern(node.pattern.ast_ref()),
            condition: visitor.visit_expression(node.condition.ast_ref()),
        }
    }

    pub struct BindingPattern<'c, V: AstVisitor<'c>>(pub V::NameRet);
    pub fn walk_binding_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::BindingPattern<'c>>,
    ) -> BindingPattern<'c, V> {
        BindingPattern(visitor.visit_name(node.0.ast_ref()))
    }

    pub enum LiteralPattern<'c, V: AstVisitor<'c>> {
        Str(V::StrLiteralPatternRet),
        Char(V::CharLiteralPatternRet),
        Int(V::IntLiteralPatternRet),
        Float(V::FloatLiteralPatternRet),
    }

    pub fn walk_literal_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> LiteralPattern<'c, V> {
        match &*node {
            ast::LiteralPattern::Str(r) => {
                LiteralPattern::Str(visitor.visit_str_literal_pattern(node.with_body(r)))
            }
            ast::LiteralPattern::Char(r) => {
                LiteralPattern::Char(visitor.visit_char_literal_pattern(node.with_body(r)))
            }
            ast::LiteralPattern::Int(r) => {
                LiteralPattern::Int(visitor.visit_int_literal_pattern(node.with_body(r)))
            }
            ast::LiteralPattern::Float(r) => {
                LiteralPattern::Float(visitor.visit_float_literal_pattern(node.with_body(r)))
            }
        }
    }

    pub fn walk_literal_pattern_same_children<'c, V, Ret>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Ret
    where
        V: AstVisitor<
            'c,
            StrLiteralPatternRet = Ret,
            CharLiteralPatternRet = Ret,
            IntLiteralPatternRet = Ret,
            FloatLiteralPatternRet = Ret,
        >,
    {
        match walk_literal_pattern(visitor, node) {
            LiteralPattern::Str(r) => r,
            LiteralPattern::Char(r) => r,
            LiteralPattern::Int(r) => r,
            LiteralPattern::Float(r) => r,
        }
    }

    pub struct DestructuringPattern<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub pattern: V::PatternRet,
    }
    pub fn walk_destructuring_pattern<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::DestructuringPattern<'c>>,
    ) -> DestructuringPattern<'c, V> {
        DestructuringPattern {
            name: visitor.visit_name(node.name.ast_ref()),
            pattern: visitor.visit_pattern(node.pattern.ast_ref()),
        }
    }

    pub struct ExprStatement<'c, V: AstVisitor<'c>>(pub V::ExpressionRet);
    pub fn walk_expr_statement<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::ExprStatement<'c>>,
    ) -> ExprStatement<'c, V> {
        ExprStatement(visitor.visit_expression(node.0.ast_ref()))
    }

    pub struct ReturnStatement<'c, V: AstVisitor<'c>>(pub Option<V::ExpressionRet>);
    pub fn walk_return_statement<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::ReturnStatement<'c>>,
    ) -> ReturnStatement<'c, V> {
        ReturnStatement(
            node.0
                .as_ref()
                .map(|n| visitor.visit_expression(n.ast_ref())),
        )
    }

    pub struct BlockStatement<'c, V: AstVisitor<'c>>(pub V::BlockRet);
    pub fn walk_block_statement<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::BlockStatement<'c>>,
    ) -> BlockStatement<'c, V> {
        BlockStatement(visitor.visit_block(node.0.ast_ref()))
    }

    pub struct LetStatement<'c, V: AstVisitor<'c>> {
        pub pattern: V::PatternRet,
        pub ty: Option<V::TypeRet>,
        pub bound: Option<V::BoundRet>,
        pub value: Option<V::ExpressionRet>,
    }
    pub fn walk_let_statement<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::LetStatement<'c>>,
    ) -> LetStatement<'c, V> {
        LetStatement {
            pattern: visitor.visit_pattern(node.pattern.ast_ref()),
            ty: node.ty.as_ref().map(|t| visitor.visit_type(t.ast_ref())),
            bound: node
                .bound
                .as_ref()
                .map(|t| visitor.visit_bound(t.ast_ref())),
            value: node
                .value
                .as_ref()
                .map(|t| visitor.visit_expression(t.ast_ref())),
        }
    }

    pub struct AssignStatement<'c, V: AstVisitor<'c>> {
        pub lhs: V::ExpressionRet,
        pub rhs: V::ExpressionRet,
    }
    pub fn walk_assign_statement<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::AssignStatement<'c>>,
    ) -> AssignStatement<'c, V> {
        AssignStatement {
            lhs: visitor.visit_expression(node.lhs.ast_ref()),
            rhs: visitor.visit_expression(node.rhs.ast_ref()),
        }
    }

    pub struct StructDefEntry<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub ty: Option<V::TypeRet>,
        pub default: Option<V::ExpressionRet>,
    }
    pub fn walk_struct_def_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::StructDefEntry<'c>>,
    ) -> StructDefEntry<'c, V> {
        StructDefEntry {
            name: visitor.visit_name(node.name.ast_ref()),
            ty: node.ty.as_ref().map(|t| visitor.visit_type(t.ast_ref())),
            default: node
                .default
                .as_ref()
                .map(|d| visitor.visit_expression(d.ast_ref())),
        }
    }

    pub struct StructDef<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub bound: Option<V::BoundRet>,
        pub entries: V::CollectionContainer<V::StructDefEntryRet>,
    }
    pub fn walk_struct_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::StructDef<'c>>,
    ) -> StructDef<'c, V> {
        StructDef {
            name: visitor.visit_name(node.name.ast_ref()),
            bound: node
                .bound
                .as_ref()
                .map(|b| visitor.visit_bound(b.ast_ref())),
            entries: node
                .entries
                .iter()
                .map(|b| visitor.visit_struct_def_entry(b.ast_ref()))
                .collect(),
        }
    }

    pub struct EnumDefEntry<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub args: V::CollectionContainer<V::TypeRet>,
    }
    pub fn walk_enum_def_entry<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::EnumDefEntry<'c>>,
    ) -> EnumDefEntry<'c, V> {
        EnumDefEntry {
            name: visitor.visit_name(node.name.ast_ref()),
            args: node
                .args
                .iter()
                .map(|b| visitor.visit_type(b.ast_ref()))
                .collect(),
        }
    }

    pub struct EnumDef<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub bound: Option<V::BoundRet>,
        pub entries: V::CollectionContainer<V::EnumDefEntryRet>,
    }
    pub fn walk_enum_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::EnumDef<'c>>,
    ) -> EnumDef<'c, V> {
        EnumDef {
            name: visitor.visit_name(node.name.ast_ref()),
            bound: node
                .bound
                .as_ref()
                .map(|b| visitor.visit_bound(b.ast_ref())),
            entries: node
                .entries
                .iter()
                .map(|b| visitor.visit_enum_def_entry(b.ast_ref()))
                .collect(),
        }
    }

    pub struct TraitBound<'c, V: AstVisitor<'c>> {
        pub name: V::AccessNameRet,
        pub type_args: V::CollectionContainer<V::TypeRet>,
    }
    pub fn walk_trait_bound<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::TraitBound<'c>>,
    ) -> TraitBound<'c, V> {
        TraitBound {
            name: visitor.visit_access_name(node.name.ast_ref()),
            type_args: node
                .type_args
                .iter()
                .map(|t| visitor.visit_type(t.ast_ref()))
                .collect(),
        }
    }

    pub struct Bound<'c, V: AstVisitor<'c>> {
        pub type_args: V::CollectionContainer<V::TypeRet>,
        pub trait_bounds: V::CollectionContainer<V::TraitBoundRet>,
    }
    pub fn walk_bound<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Bound<'c>>,
    ) -> Bound<'c, V> {
        Bound {
            type_args: node
                .type_args
                .iter()
                .map(|t| visitor.visit_type(t.ast_ref()))
                .collect(),
            trait_bounds: node
                .trait_bounds
                .iter()
                .map(|t| visitor.visit_trait_bound(t.ast_ref()))
                .collect(),
        }
    }

    pub struct TraitDef<'c, V: AstVisitor<'c>> {
        pub name: V::NameRet,
        pub bound: V::BoundRet,
        pub trait_type: V::TypeRet,
    }
    pub fn walk_trait_def<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::TraitDef<'c>>,
    ) -> TraitDef<'c, V> {
        TraitDef {
            name: visitor.visit_name(node.name.ast_ref()),
            bound: visitor.visit_bound(node.bound.ast_ref()),
            trait_type: visitor.visit_type(node.trait_type.ast_ref()),
        }
    }

    pub enum Statement<'c, V: AstVisitor<'c>> {
        Expr(V::ExprStatementRet),
        Return(V::ReturnStatementRet),
        Block(V::BlockStatementRet),
        Break(V::BreakStatementRet),
        Continue(V::ContinueStatementRet),
        Let(V::LetStatementRet),
        Assign(V::AssignStatementRet),
        StructDef(V::StructDefRet),
        EnumDef(V::EnumDefRet),
        TraitDef(V::TraitDefRet),
    }

    pub fn walk_statement<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Statement<'c>>,
    ) -> Statement<'c, V> {
        match &*node {
            ast::Statement::Expr(r) => {
                Statement::Expr(visitor.visit_expr_statement(node.with_body(r)))
            }
            ast::Statement::Return(r) => {
                Statement::Return(visitor.visit_return_statement(node.with_body(r)))
            }
            ast::Statement::Block(r) => {
                Statement::Block(visitor.visit_block_statement(node.with_body(r)))
            }
            ast::Statement::Break(r) => {
                Statement::Break(visitor.visit_break_statement(node.with_body(r)))
            }
            ast::Statement::Continue(r) => {
                Statement::Continue(visitor.visit_continue_statement(node.with_body(r)))
            }
            ast::Statement::Let(r) => {
                Statement::Let(visitor.visit_let_statement(node.with_body(r)))
            }
            ast::Statement::Assign(r) => {
                Statement::Assign(visitor.visit_assign_statement(node.with_body(r)))
            }
            ast::Statement::StructDef(r) => {
                Statement::StructDef(visitor.visit_struct_def(node.with_body(r)))
            }
            ast::Statement::EnumDef(r) => {
                Statement::EnumDef(visitor.visit_enum_def(node.with_body(r)))
            }
            ast::Statement::TraitDef(r) => {
                Statement::TraitDef(visitor.visit_trait_def(node.with_body(r)))
            }
        }
    }

    pub fn walk_statement_same_children<'c, V, Ret>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Statement<'c>>,
    ) -> Ret
    where
        V: AstVisitor<
            'c,
            ExprStatementRet = Ret,
            ReturnStatementRet = Ret,
            BlockStatementRet = Ret,
            BreakStatementRet = Ret,
            ContinueStatementRet = Ret,
            LetStatementRet = Ret,
            AssignStatementRet = Ret,
            StructDefRet = Ret,
            EnumDefRet = Ret,
            TraitDefRet = Ret,
        >,
    {
        match walk_statement(visitor, node) {
            Statement::Expr(r) => r,
            Statement::Return(r) => r,
            Statement::Block(r) => r,
            Statement::Break(r) => r,
            Statement::Continue(r) => r,
            Statement::Let(r) => r,
            Statement::Assign(r) => r,
            Statement::StructDef(r) => r,
            Statement::EnumDef(r) => r,
            Statement::TraitDef(r) => r,
        }
    }

    pub struct Module<'c, V: AstVisitor<'c>> {
        pub contents: V::CollectionContainer<V::StatementRet>,
    }

    pub fn walk_module<'c, V: AstVisitor<'c>>(
        visitor: &mut V,
        node: ast::AstNodeRef<ast::Module<'c>>,
    ) -> Module<'c, V> {
        Module {
            contents: node
                .contents
                .iter()
                .map(|s| visitor.visit_statement(s.ast_ref()))
                .collect(),
        }
    }
}
