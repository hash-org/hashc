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
                .map(|p| IDENTIFIER_MAP.get_ident(*p))
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

    type IntrinsicKeyRet = TreeNode;
    fn visit_intrinsic_key(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntrinsicKey>,
    ) -> Result<Self::IntrinsicKeyRet, Self::Error> {
        Ok(TreeNode::leaf(labelled(
            "intrinsic",
            IDENTIFIER_MAP.get_ident(node.name),
            "\"",
        )))
    }

    type FunctionCallArgsRet = TreeNode;
    fn visit_function_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> Result<Self::FunctionCallArgsRet, Self::Error> {
        Ok(TreeNode::branch(
            "args",
            walk::walk_function_call_args(self, ctx, node)?.entries,
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
        let walk::NamedType { name, type_args } = walk::walk_named_type(self, ctx, node)?;
        let children = {
            if type_args.is_empty() {
                vec![]
            } else {
                vec![TreeNode::branch("type_args", type_args)]
            }
        };
        Ok(TreeNode::branch(
            labelled("named", name.label, "\""),
            children,
        ))
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

    type TypeVarRet = TreeNode;
    fn visit_type_var(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeVar<'c>>,
    ) -> Result<Self::TypeVarRet, Self::Error> {
        let walk::TypeVar { name } = walk::walk_type_var(self, ctx, node)?;
        Ok(TreeNode::leaf(labelled("var", name.label, "\"")))
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

    type IntLiteralRet = TreeNode;
    fn visit_int_literal(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("int", node.0, "")))
    }

    type StructLiteralRet = TreeNode;
    fn visit_struct_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructLiteral<'c>>,
    ) -> Result<Self::StructLiteralRet, Self::Error> {
        let walk::StructLiteral {
            name: _,
            type_args,
            entries,
        } = walk::walk_struct_literal(self, ctx, node)?;
        Ok(TreeNode::branch(
            "struct",
            vec![
                TreeNode::branch("type_args", type_args),
                TreeNode::branch("entries", entries),
            ],
        ))
    }

    type StructLiteralEntryRet = TreeNode;
    fn visit_struct_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructLiteralEntry<'c>>,
    ) -> Result<Self::StructLiteralEntryRet, Self::Error> {
        let walk::StructLiteralEntry { name, value } =
            walk::walk_struct_literal_entry(self, ctx, node)?;
        Ok(TreeNode::branch(
            "entry",
            vec![
                TreeNode::branch("name", vec![name]),
                TreeNode::branch("value", vec![value]),
            ],
        ))
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
                .chain(
                    return_ty
                        .map(|r| TreeNode::branch("return_type", vec![r]))
                        .into_iter(),
                )
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
        let walk::FunctionDefArg { name, ty } = walk::walk_function_def_arg(self, ctx, node)?;
        Ok(TreeNode::branch(
            "arg",
            iter::once(TreeNode::branch("name", vec![name]))
                .chain(ty.into_iter())
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

    type StatementRet = TreeNode;
    fn visit_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Statement<'c>>,
    ) -> Result<Self::StatementRet, Self::Error> {
        walk::walk_statement_same_children(self, ctx, node)
    }

    type ExprStatementRet = TreeNode;
    fn visit_expr_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ExprStatement<'c>>,
    ) -> Result<Self::ExprStatementRet, Self::Error> {
        Ok(walk::walk_expr_statement(self, ctx, node)?.0)
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

    type BlockStatementRet = TreeNode;
    fn visit_block_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BlockStatement<'c>>,
    ) -> Result<Self::BlockStatementRet, Self::Error> {
        Ok(walk::walk_block_statement(self, ctx, node)?.0)
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

    type LetStatementRet = TreeNode;
    fn visit_let_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LetStatement<'c>>,
    ) -> Result<Self::LetStatementRet, Self::Error> {
        let walk::LetStatement {
            pattern,
            ty,
            bound,
            value,
        } = walk::walk_let_statement(self, ctx, node)?;
        Ok(TreeNode::branch(
            "let",
            iter::once(TreeNode::branch("pattern", vec![pattern]))
                .chain(ty.map(|t| TreeNode::branch("type", vec![t])).into_iter())
                .chain(bound.into_iter())
                .chain(
                    value
                        .map(|v| TreeNode::branch("value", vec![v]))
                        .into_iter(),
                )
                .collect(),
        ))
    }

    type AssignStatementRet = TreeNode;
    fn visit_assign_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AssignStatement<'c>>,
    ) -> Result<Self::AssignStatementRet, Self::Error> {
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
        let walk::StructDef {
            name: _,
            entries,
            bound,
        } = walk::walk_struct_def(self, ctx, node)?;
        Ok(TreeNode::branch(
            "struct_def",
            bound
                .into_iter()
                .chain(iter::once(TreeNode::branch("fields", entries)))
                .collect(),
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
        let walk::EnumDef {
            name,
            entries,
            bound,
        } = walk::walk_enum_def(self, ctx, node)?;
        Ok(TreeNode::branch(
            "enum_def",
            iter::once(TreeNode::leaf(labelled("name", name.label, "\"")))
                .chain(bound.into_iter())
                .chain(iter::once(TreeNode::branch("variants", entries)))
                .collect(),
        ))
    }

    type TraitDefRet = TreeNode;
    fn visit_trait_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitDef<'c>>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let walk::TraitDef {
            name: _,
            bound,
            trait_type,
        } = walk::walk_trait_def(self, ctx, node)?;
        Ok(TreeNode::branch(
            "trait_def",
            vec![bound, TreeNode::branch("type", vec![trait_type])],
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

    type TraitBoundRet = TreeNode;
    fn visit_trait_bound(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitBound<'c>>,
    ) -> Result<Self::TraitBoundRet, Self::Error> {
        let walk::TraitBound { name, type_args } = walk::walk_trait_bound(self, ctx, node)?;
        Ok(TreeNode::branch(
            labelled("requires", name.label, "\""),
            vec![TreeNode::branch("args", type_args)],
        ))
    }

    type BoundRet = TreeNode;
    fn visit_bound(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Bound<'c>>,
    ) -> Result<Self::BoundRet, Self::Error> {
        let walk::Bound {
            type_args,
            trait_bounds,
        } = walk::walk_bound(self, ctx, node)?;
        Ok(TreeNode::branch(
            "bound",
            vec![
                TreeNode::branch("vars", type_args),
                TreeNode::branch("traits", trait_bounds),
            ],
        ))
    }

    type EnumPatternRet = TreeNode;
    fn visit_enum_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::EnumPattern<'c>>,
    ) -> Result<Self::EnumPatternRet, Self::Error> {
        let walk::EnumPattern { args, name } = walk::walk_enum_pattern(self, ctx, node)?;
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

    type StructPatternRet = TreeNode;
    fn visit_struct_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructPattern<'c>>,
    ) -> Result<Self::StructPatternRet, Self::Error> {
        let walk::StructPattern { name, entries } = walk::walk_struct_pattern(self, ctx, node)?;
        Ok(TreeNode::branch(
            "struct",
            iter::once(TreeNode::leaf(labelled("name", name.label, "\"")))
                .chain(
                    (if entries.is_empty() {
                        None
                    } else {
                        Some(TreeNode::branch("fields", entries))
                    })
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

    type TuplePatternRet = TreeNode;
    fn visit_tuple_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        let walk::TuplePattern { elements } = walk::walk_tuple_pattern(self, ctx, node)?;
        Ok(TreeNode::branch("tuple", elements))
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
