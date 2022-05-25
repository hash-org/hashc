//! AST visualisation utilities.
//!
//! All rights reserved 2022 (c) The Hash Language authors
use std::convert::Infallible;
use std::iter;

use hash_utils::tree_writing::TreeNode;

use crate::ident::IDENTIFIER_MAP;
use crate::literal::STRING_LITERAL_MAP;
use crate::{ast, visitor::walk, visitor::AstVisitor};

/// Struct implementing [AstVisitor], for the purpose of transforming the AST tree into a
/// [TreeNode] tree, for visualisation purposes.
pub struct AstTreeGenerator;

/// Easy way to format a [TreeNode] label with a main label as well as short contents, and a
/// quoting string.
fn labelled(label: impl ToString, contents: impl ToString, quote_str: &str) -> String {
    format!(
        "{} {}{}{}",
        label.to_string(),
        quote_str,
        contents.to_string(),
        quote_str
    )
}

impl<'c> AstVisitor<'c> for AstTreeGenerator {
    type Ctx = ();

    type CollectionContainer<T: 'c> = Vec<T>;
    fn try_collect_items<T: 'c, E, I: Iterator<Item = Result<T, E>>>(
        _: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E> {
        items.collect()
    }

    type Error = Infallible;

    type ImportRet = TreeNode;
    fn visit_import(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        Ok(TreeNode::leaf(labelled(
            "import",
            STRING_LITERAL_MAP.lookup(node.path),
            "\"",
        )))
    }

    type NameRet = TreeNode;
    fn visit_name(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        Ok(TreeNode::leaf(IDENTIFIER_MAP.get_ident(node.ident)))
    }

    type AccessNameRet = TreeNode;
    fn visit_access_name(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::AccessName<'c>>,
    ) -> Result<Self::AccessNameRet, Self::Error> {
        Ok(TreeNode::leaf(
            node.path
                .iter()
                .map(|p| IDENTIFIER_MAP.get_ident(*p.body()))
                .intersperse("::")
                .collect::<String>(),
        ))
    }

    type LiteralRet = TreeNode;
    fn visit_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Literal<'c>>,
    ) -> Result<Self::LiteralRet, Self::Error> {
        walk::walk_literal_same_children(self, ctx, node)
    }

    type ExpressionRet = TreeNode;
    fn visit_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Result<Self::ExpressionRet, Self::Error> {
        walk::walk_expression_same_children(self, ctx, node)
    }

    type VariableExprRet = TreeNode;
    fn visit_variable_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        let walk::VariableExpr { name, type_args } = walk::walk_variable_expr(self, ctx, node)?;

        let mut children = vec![TreeNode::leaf(labelled("named", name.label, "\""))];

        if !type_args.is_empty() {
            children.extend(iter::once(TreeNode::branch("type_args", type_args)));
        }

        Ok(TreeNode::branch("variable", children))
    }

    type DirectiveExprRet = TreeNode;
    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let walk::DirectiveExpr { subject, .. } = walk::walk_directive_expr(self, ctx, node)?;

        Ok(TreeNode::branch(
            labelled("directive", IDENTIFIER_MAP.get_ident(node.name.ident), "\""),
            vec![subject],
        ))
    }

    type FunctionCallArgRet = TreeNode;

    fn visit_function_call_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallArg<'c>>,
    ) -> Result<Self::FunctionCallArgRet, Self::Error> {
        if let Some(name) = &node.name {
            Ok(TreeNode::branch(
                "arg",
                vec![
                    TreeNode::leaf(labelled(
                        "named",
                        IDENTIFIER_MAP.get_ident(name.ident),
                        "\"",
                    )),
                    TreeNode::branch(
                        "value",
                        vec![self.visit_expression(ctx, node.value.ast_ref())?],
                    ),
                ],
            ))
        } else {
            self.visit_expression(ctx, node.value.ast_ref())
        }
    }

    type FunctionCallArgsRet = TreeNode;
    fn visit_function_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> Result<Self::FunctionCallArgsRet, Self::Error> {
        Ok(TreeNode::branch(
            "args",
            walk::walk_function_call_args(self, ctx, node)?
                .entries
                .into_iter()
                .collect(),
        ))
    }

    type FunctionCallExprRet = TreeNode;
    fn visit_function_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallExpr<'c>>,
    ) -> Result<Self::FunctionCallExprRet, Self::Error> {
        let walk::FunctionCallExpr { subject, args } =
            walk::walk_function_call_expr(self, ctx, node)?;

        let children = if !node.args.entries.is_empty() {
            vec![TreeNode::branch("subject", vec![subject]), args]
        } else {
            vec![TreeNode::branch("subject", vec![subject])]
        };

        Ok(TreeNode::branch("function_call", children))
    }

    type PropertyAccessExprRet = TreeNode;
    fn visit_property_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::PropertyAccessExpr<'c>>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        let walk::PropertyAccessExpr { subject, property } =
            walk::walk_property_access_expr(self, ctx, node)?;
        Ok(TreeNode::branch(
            "property_access",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::branch("property", vec![property]),
            ],
        ))
    }

    type RefExprRet = TreeNode;
    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefExpr<'c>>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let walk::RefExpr { inner_expr } = walk::walk_ref_expr(self, ctx, node)?;
        Ok(TreeNode::branch("ref", vec![inner_expr]))
    }

    type DerefExprRet = TreeNode;
    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DerefExpr<'c>>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::DerefExpr(inner_expr) = walk::walk_deref_expr(self, ctx, node)?;
        Ok(TreeNode::branch("deref", vec![inner_expr]))
    }

    type UnsafeExprRet = TreeNode;
    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::UnsafeExpr<'c>>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::UnsafeExpr(inner_expr) = walk::walk_unsafe_expr(self, ctx, node)?;
        Ok(TreeNode::branch("unsafe", vec![inner_expr]))
    }

    type LiteralExprRet = TreeNode;
    fn visit_literal_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralExpr<'c>>,
    ) -> Result<Self::LiteralExprRet, Self::Error> {
        let walk::LiteralExpr(literal) = walk::walk_literal_expr(self, ctx, node)?;
        Ok(literal)
    }

    type TypedExprRet = TreeNode;
    fn visit_typed_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypedExpr<'c>>,
    ) -> Result<Self::TypedExprRet, Self::Error> {
        let walk::TypedExpr { ty, expr } = walk::walk_typed_expr(self, ctx, node)?;
        Ok(TreeNode::branch(
            "typed_expr",
            vec![
                TreeNode::branch("subject", vec![expr]),
                TreeNode::branch("type", vec![ty]),
            ],
        ))
    }

    type BlockExprRet = TreeNode;
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BlockExpr<'c>>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        Ok(walk::walk_block_expr(self, ctx, node)?.0)
    }

    type ImportExprRet = TreeNode;
    fn visit_import_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ImportExpr<'c>>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(walk::walk_import_expr(self, ctx, node)?.0)
    }

    type NamedFieldTypeRet = TreeNode;
    fn visit_named_field_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedFieldTypeEntry<'c>>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error> {
        let walk::NamedFieldTypeEntry { name, ty } = walk::walk_named_field_type(self, ctx, node)?;

        if let Some(name) = name {
            Ok(TreeNode::branch(
                "field",
                vec![
                    TreeNode::branch("name", vec![name]),
                    TreeNode::branch("type", vec![ty]),
                ],
            ))
        } else {
            Ok(ty)
        }
    }

    type TypeRet = TreeNode;
    fn visit_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Type<'c>>,
    ) -> Result<Self::TypeRet, Self::Error> {
        walk::walk_type_same_children(self, ctx, node)
    }

    type TupleTypeRet = TreeNode;
    fn visit_tuple_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleType<'c>>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        let walk::TupleType { entries } = walk::walk_tuple_type(self, ctx, node)?;

        Ok(TreeNode::branch("tuple", entries))
    }

    type ListTypeRet = TreeNode;
    fn visit_list_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListType<'c>>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        let walk::ListType { inner } = walk::walk_list_type(self, ctx, node)?;

        Ok(TreeNode::branch("list", vec![inner]))
    }

    type SetTypeRet = TreeNode;
    fn visit_set_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetType<'c>>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        let walk::SetType { key } = walk::walk_set_type(self, ctx, node)?;

        Ok(TreeNode::branch("set", vec![key]))
    }

    type MapTypeRet = TreeNode;
    fn visit_map_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapType<'c>>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        let walk::MapType { key, value } = walk::walk_map_type(self, ctx, node)?;

        Ok(TreeNode::branch(
            "map",
            vec![
                TreeNode::branch("key", vec![key]),
                TreeNode::branch("key", vec![value]),
            ],
        ))
    }

    type FnTypeRet = TreeNode;
    fn visit_function_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FnType<'c>>,
    ) -> Result<Self::FnTypeRet, Self::Error> {
        let walk::FnType { args, return_ty } = walk::walk_function_type(self, ctx, node)?;

        let return_child = TreeNode::branch("return", vec![return_ty]);

        let children = {
            if args.is_empty() {
                vec![return_child]
            } else {
                vec![TreeNode::branch("arguments", args), return_child]
            }
        };

        Ok(TreeNode::branch("function", children))
    }

    type NamedTypeRet = TreeNode;
    fn visit_named_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedType<'c>>,
    ) -> Result<Self::NamedTypeRet, Self::Error> {
        let walk::NamedType { name } = walk::walk_named_type(self, ctx, node)?;
        Ok(TreeNode::leaf(labelled("named", name.label, "\"")))
    }

    type GroupedTypeRet = TreeNode;
    fn visit_grouped_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::GroupedType<'c>>,
    ) -> Result<Self::GroupedTypeRet, Self::Error> {
        let walk::GroupedType(inner) = walk::walk_grouped_type(self, ctx, node)?;
        Ok(TreeNode::branch("grouped", vec![inner]))
    }

    type RefTypeRet = TreeNode;
    fn visit_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefType<'c>>,
    ) -> Result<Self::RefTypeRet, Self::Error> {
        let walk::RefType(inner) = walk::walk_ref_type(self, ctx, node)?;
        Ok(TreeNode::branch("ref", vec![inner]))
    }

    type RawRefTypeRet = TreeNode;
    fn visit_raw_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RawRefType<'c>>,
    ) -> Result<Self::RawRefTypeRet, Self::Error> {
        let walk::RawRefType(inner) = walk::walk_raw_ref_type(self, ctx, node)?;
        Ok(TreeNode::branch("raw_ref", vec![inner]))
    }

    type MergedTypeRet = TreeNode;
    fn visit_merged_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MergedType<'c>>,
    ) -> Result<Self::RawRefTypeRet, Self::Error> {
        let walk::MergedType(tys) = walk::walk_merged_type(self, ctx, node)?;
        Ok(TreeNode::branch("merged", tys))
    }

    type TypeFunctionCallRet = TreeNode;
    fn visit_type_function_call(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionCall<'c>>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error> {
        let walk::TypeFunctionCall { subject, args } =
            walk::walk_type_function_call(self, ctx, node)?;

        Ok(TreeNode::branch(
            "function_call",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::branch("arguments", args),
            ],
        ))
    }

    type TypeFunctionParamRet = TreeNode;
    fn visit_type_function_param(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionParam<'c>>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error> {
        let walk::TypeFunctionParam {
            name,
            bound,
            default,
        } = walk::walk_type_function_param(self, ctx, node)?;

        Ok(TreeNode::branch(
            "arg",
            iter::once(TreeNode::branch("name", vec![name]))
                .chain(bound.map(|t| TreeNode::branch("type", vec![t])))
                .chain(default.map(|d| TreeNode::branch("default", vec![d])))
                .collect(),
        ))
    }

    type TypeFunctionRet = TreeNode;
    fn visit_type_function(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunction<'c>>,
    ) -> Result<Self::TypeFunctionRet, Self::Error> {
        let walk::TypeFunction { args, return_ty } = walk::walk_type_function(self, ctx, node)?;

        let return_child = TreeNode::branch("return", vec![return_ty]);

        let children = {
            if args.is_empty() {
                vec![return_child]
            } else {
                vec![TreeNode::branch("arguments", args), return_child]
            }
        };

        Ok(TreeNode::branch("type_function", children))
    }

    type ExistentialTypeRet = TreeNode;
    fn visit_existential_type(
        &mut self,
        _: &Self::Ctx,
        _: ast::AstNodeRef<ast::ExistentialType>,
    ) -> Result<Self::ExistentialTypeRet, Self::Error> {
        Ok(TreeNode::leaf("existential"))
    }

    type InferTypeRet = TreeNode;
    fn visit_infer_type(
        &mut self,
        _: &Self::Ctx,
        _: ast::AstNodeRef<ast::InferType>,
    ) -> Result<Self::InferTypeRet, Self::Error> {
        Ok(TreeNode::leaf("infer"))
    }

    type MapLiteralRet = TreeNode;
    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLiteral<'c>>,
    ) -> Result<Self::MapLiteralRet, Self::Error> {
        Ok(TreeNode::branch(
            "map",
            walk::walk_map_literal(self, ctx, node)?.entries,
        ))
    }

    type MapLiteralEntryRet = TreeNode;
    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLiteralEntry<'c>>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error> {
        let walk::MapLiteralEntry { key, value } = walk::walk_map_literal_entry(self, ctx, node)?;
        Ok(TreeNode::branch(
            "entry",
            vec![
                TreeNode::branch("key", vec![key]),
                TreeNode::branch("value", vec![value]),
            ],
        ))
    }

    type ListLiteralRet = TreeNode;
    fn visit_list_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListLiteral<'c>>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        let children = walk::walk_list_literal(self, ctx, node)?;
        Ok(TreeNode::branch("list", children.elements))
    }

    type SetLiteralRet = TreeNode;
    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetLiteral<'c>>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        let children = walk::walk_set_literal(self, ctx, node)?;
        Ok(TreeNode::branch("set", children.elements))
    }

    type TupleLiteralEntryRet = TreeNode;
    fn visit_tuple_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteralEntry<'c>>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        let walk::TupleLiteralEntry { name, ty, value } =
            walk::walk_tuple_literal_entry(self, ctx, node)?;

        Ok(TreeNode::branch(
            "entry",
            name.map(|t| TreeNode::branch("name", vec![t]))
                .into_iter()
                .chain(ty.map(|t| TreeNode::branch("type", vec![t])).into_iter())
                .chain(iter::once(TreeNode::branch("value", vec![value])))
                .collect(),
        ))
    }

    type TupleLiteralRet = TreeNode;
    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteral<'c>>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        let children = walk::walk_tuple_literal(self, ctx, node)?;
        Ok(TreeNode::branch("tuple", children.elements))
    }

    type StrLiteralRet = TreeNode;
    fn visit_str_literal(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        Ok(TreeNode::leaf(labelled(
            "str",
            STRING_LITERAL_MAP.lookup(node.0),
            "\"",
        )))
    }

    type CharLiteralRet = TreeNode;
    fn visit_char_literal(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("char", node.0, "'")))
    }

    type FloatLiteralRet = TreeNode;
    fn visit_float_literal(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("float", node.0, "")))
    }

    type BoolLiteralRet = TreeNode;
    fn visit_bool_literal(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("bool", node.0, "")))
    }

    type IntLiteralRet = TreeNode;
    fn visit_int_literal(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("int", node.0, "")))
    }

    type FunctionDefRet = TreeNode;
    fn visit_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDef<'c>>,
    ) -> Result<Self::FunctionDefRet, Self::Error> {
        let walk::FunctionDef {
            args,
            fn_body,
            return_ty,
        } = walk::walk_function_def(self, ctx, node)?;

        Ok(TreeNode::branch(
            "function_def",
            iter::once(TreeNode::branch("args", args))
                .chain(return_ty.map(|r| TreeNode::branch("return_type", vec![r])))
                .chain(iter::once(TreeNode::branch("body", vec![fn_body])))
                .collect(),
        ))
    }

    type FunctionDefArgRet = TreeNode;
    fn visit_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDefArg<'c>>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error> {
        let walk::FunctionDefArg { name, ty, default } =
            walk::walk_function_def_arg(self, ctx, node)?;
        Ok(TreeNode::branch(
            "arg",
            iter::once(TreeNode::branch("name", vec![name]))
                .chain(ty.map(|t| TreeNode::branch("type", vec![t])))
                .chain(default.map(|d| TreeNode::branch("default", vec![d])))
                .collect(),
        ))
    }

    type BlockRet = TreeNode;
    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Block<'c>>,
    ) -> Result<Self::BlockRet, Self::Error> {
        walk::walk_block_same_children(self, ctx, node)
    }

    type MatchCaseRet = TreeNode;
    fn visit_match_case(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MatchCase<'c>>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let walk::MatchCase { expr, pattern } = walk::walk_match_case(self, ctx, node)?;
        Ok(TreeNode::branch(
            "case",
            vec![pattern, TreeNode::branch("branch", vec![expr])],
        ))
    }

    type MatchBlockRet = TreeNode;
    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MatchBlock<'c>>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let walk::MatchBlock { cases, subject } = walk::walk_match_block(self, ctx, node)?;

        Ok(TreeNode::branch(
            "match",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::branch("cases", cases),
            ],
        ))
    }

    type LoopBlockRet = TreeNode;
    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LoopBlock<'c>>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let walk::LoopBlock(inner) = walk::walk_loop_block(self, ctx, node)?;
        Ok(TreeNode::branch("loop", inner.children))
    }

    type BodyBlockRet = TreeNode;
    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BodyBlock<'c>>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let walk::BodyBlock { statements, expr } = walk::walk_body_block(self, ctx, node)?;

        let mut children = Vec::new();
        if !statements.is_empty() {
            children.push(TreeNode::branch("statements", statements));
        }
        if let Some(expr) = expr {
            children.push(TreeNode::branch("expr", vec![expr]));
        }

        Ok(TreeNode::branch("body", children))
    }

    type ReturnStatementRet = TreeNode;
    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ReturnStatement<'c>>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let walk::ReturnStatement(inner) = walk::walk_return_statement(self, ctx, node)?;
        Ok(TreeNode::branch("return", inner.into_iter().collect()))
    }

    type BreakStatementRet = TreeNode;
    fn visit_break_statement(
        &mut self,
        _: &Self::Ctx,
        _: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        Ok(TreeNode::leaf("break"))
    }

    type ContinueStatementRet = TreeNode;
    fn visit_continue_statement(
        &mut self,
        _: &Self::Ctx,
        _: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        Ok(TreeNode::leaf("continue"))
    }

    type DeclarationRet = TreeNode;
    fn visit_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Declaration<'c>>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let walk::Declaration { pattern, ty, value } = walk::walk_declaration(self, ctx, node)?;
        Ok(TreeNode::branch(
            "declaration",
            iter::once(TreeNode::branch("pattern", vec![pattern]))
                .chain(ty.map(|t| TreeNode::branch("type", vec![t])))
                .chain(value.map(|t| TreeNode::branch("value", vec![t])))
                .collect(),
        ))
    }

    type AssignExpressionRet = TreeNode;
    fn visit_assign_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AssignExpression<'c>>,
    ) -> Result<Self::AssignExpressionRet, Self::Error> {
        let walk::AssignStatement { lhs, rhs } = walk::walk_assign_statement(self, ctx, node)?;
        Ok(TreeNode::branch(
            "assign",
            vec![
                TreeNode::branch("lhs", vec![lhs]),
                TreeNode::branch("rhs", vec![rhs]),
            ],
        ))
    }

    type StructDefEntryRet = TreeNode;
    fn visit_struct_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructDefEntry<'c>>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        let walk::StructDefEntry { name, ty, default } =
            walk::walk_struct_def_entry(self, ctx, node)?;
        Ok(TreeNode::branch(
            labelled("field", name.label, "\""),
            ty.map(|t| TreeNode::branch("type", vec![t]))
                .into_iter()
                .chain(default.map(|d| TreeNode::branch("default", vec![d])))
                .collect(),
        ))
    }

    type StructDefRet = TreeNode;
    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructDef<'c>>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let walk::StructDef { entries } = walk::walk_struct_def(self, ctx, node)?;
        Ok(TreeNode::branch(
            "struct_def",
            iter::once(TreeNode::branch("fields", entries)).collect(),
        ))
    }

    type EnumDefEntryRet = TreeNode;
    fn visit_enum_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::EnumDefEntry<'c>>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        let walk::EnumDefEntry { name, args } = walk::walk_enum_def_entry(self, ctx, node)?;
        Ok(TreeNode::branch(
            labelled("variant", name.label, "\""),
            if args.is_empty() { vec![] } else { vec![TreeNode::branch("args", args)] },
        ))
    }

    type EnumDefRet = TreeNode;
    fn visit_enum_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::EnumDef<'c>>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let walk::EnumDef { entries } = walk::walk_enum_def(self, ctx, node)?;
        Ok(TreeNode::branch(
            "enum_def",
            iter::once(TreeNode::branch("variants", entries)).collect(),
        ))
    }

    type TraitDefRet = TreeNode;
    fn visit_trait_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitDef<'c>>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let walk::TraitDef { members } = walk::walk_trait_def(self, ctx, node)?;

        Ok(TreeNode::branch(
            "trait_def",
            vec![TreeNode::branch("members", members)],
        ))
    }

    type PatternRet = TreeNode;
    fn visit_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Pattern<'c>>,
    ) -> Result<Self::PatternRet, Self::Error> {
        walk::walk_pattern_same_children(self, ctx, node)
    }

    type TypeFunctionDefRet = TreeNode;
    fn visit_type_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDef<'c>>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error> {
        let walk::TypeFunctionDef {
            args,
            return_ty,
            expression,
        } = walk::walk_type_function_def(self, ctx, node)?;

        Ok(TreeNode::branch(
            "type_function",
            iter::once(TreeNode::branch("args", args))
                .chain(return_ty.map(|r| TreeNode::branch("return_type", vec![r])))
                .chain(iter::once(TreeNode::branch("body", vec![expression])))
                .collect(),
        ))
    }

    type TypeFunctionDefArgRet = TreeNode;
    fn visit_type_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDefArg<'c>>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error> {
        let walk::TypeFunctionDefArg { name, ty } =
            walk::walk_type_function_def_arg(self, ctx, node)?;

        Ok(TreeNode::branch("arg", vec![name, ty]))
    }

    type ConstructorPatternRet = TreeNode;
    fn visit_constructor_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ConstructorPattern<'c>>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error> {
        let walk::ConstructorPattern { args, name } =
            walk::walk_constructor_pattern(self, ctx, node)?;
        Ok(TreeNode::branch(
            "enum",
            iter::once(TreeNode::leaf(labelled("name", name.label, "\"")))
                .chain(
                    (if args.is_empty() { None } else { Some(TreeNode::branch("args", args)) })
                        .into_iter(),
                )
                .collect(),
        ))
    }

    type NamespacePatternRet = TreeNode;
    fn visit_namespace_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        let walk::NamespacePattern { patterns } = walk::walk_namespace_pattern(self, ctx, node)?;
        Ok(TreeNode::branch(
            "namespace",
            vec![TreeNode::branch("members", patterns)],
        ))
    }

    type TuplePatternEntryRet = TreeNode;

    fn visit_tuple_pattern_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePatternEntry<'c>>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error> {
        let walk::TuplePatternEntry { name, pattern } =
            walk::walk_tuple_pattern_entry(self, ctx, node)?;

        Ok(TreeNode::branch(
            "entry",
            name.map(|t| TreeNode::branch("name", vec![t]))
                .into_iter()
                .chain(iter::once(TreeNode::branch("pattern", vec![pattern])))
                .collect(),
        ))
    }

    type TuplePatternRet = TreeNode;
    fn visit_tuple_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        let walk::TuplePattern { elements } = walk::walk_tuple_pattern(self, ctx, node)?;
        Ok(TreeNode::branch("tuple", elements))
    }

    type ListPatternRet = TreeNode;
    fn visit_list_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListPattern<'c>>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        let walk::ListPattern { elements } = walk::walk_list_pattern(self, ctx, node)?;
        Ok(TreeNode::branch("list", elements))
    }

    type StrLiteralPatternRet = TreeNode;
    fn visit_str_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        Ok(TreeNode::leaf(labelled(
            "str",
            STRING_LITERAL_MAP.lookup(node.0),
            "\"",
        )))
    }

    type CharLiteralPatternRet = TreeNode;
    fn visit_char_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("char", node.0, "\'")))
    }

    type IntLiteralPatternRet = TreeNode;
    fn visit_int_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("int", node.0, "")))
    }

    type FloatLiteralPatternRet = TreeNode;
    fn visit_float_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("float", node.0, "")))
    }

    type BoolLiteralPatternRet = TreeNode;
    fn visit_bool_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("bool", node.0, "")))
    }

    type LiteralPatternRet = TreeNode;
    fn visit_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error> {
        walk::walk_literal_pattern_same_children(self, ctx, node)
    }

    type OrPatternRet = TreeNode;
    fn visit_or_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::OrPattern<'c>>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        let walk::OrPattern { variants } = walk::walk_or_pattern(self, ctx, node)?;
        Ok(TreeNode::branch("or", variants))
    }

    type IfPatternRet = TreeNode;
    fn visit_if_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IfPattern<'c>>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        let walk::IfPattern { condition, pattern } = walk::walk_if_pattern(self, ctx, node)?;
        Ok(TreeNode::branch(
            "if",
            vec![
                TreeNode::branch("condition", vec![condition]),
                TreeNode::branch("pattern", vec![pattern]),
            ],
        ))
    }

    type BindingPatternRet = TreeNode;
    fn visit_binding_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BindingPattern<'c>>,
    ) -> Result<Self::BindingPatternRet, Self::Error> {
        let walk::BindingPattern(name) = walk::walk_binding_pattern(self, ctx, node)?;
        Ok(TreeNode::leaf(labelled("binding", name.label, "\"")))
    }

    type SpreadPatternRet = TreeNode;
    fn visit_spread_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SpreadPattern<'c>>,
    ) -> Result<Self::SpreadPatternRet, Self::Error> {
        let walk::SpreadPattern { name } = walk::walk_spread_pattern(self, ctx, node)?;

        if let Some(name) = name {
            Ok(TreeNode::leaf(labelled("spread", name.label, "\"")))
        } else {
            Ok(TreeNode::leaf("spread"))
        }
    }

    type IgnorePatternRet = TreeNode;
    fn visit_ignore_pattern(
        &mut self,
        _: &Self::Ctx,
        _: ast::AstNodeRef<ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        Ok(TreeNode::leaf("ignore"))
    }

    type DestructuringPatternRet = TreeNode;
    fn visit_destructuring_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DestructuringPattern<'c>>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error> {
        let walk::DestructuringPattern { name, pattern } =
            walk::walk_destructuring_pattern(self, ctx, node)?;
        Ok(TreeNode::branch(
            labelled("binding", name.label, "\""),
            vec![pattern],
        ))
    }

    type ModuleRet = TreeNode;
    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Module<'c>>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let walk::Module { contents } = walk::walk_module(self, ctx, node)?;
        Ok(TreeNode::branch("module", contents))
    }
}
