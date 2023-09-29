//! AST visualisation utilities.

use std::{convert::Infallible, iter};

use hash_ast::{
    ast,
    visitor::{walk, AstVisitor},
};
use hash_utils::{itertools::Itertools, tree_writing::TreeNode};

/// Struct implementing [crate::visitor::AstVisitor], for the purpose of
/// transforming the AST tree into a [TreeNode] tree, for visualisation
/// purposes.
pub struct AstTreePrinter;

/// Easy way to format a [TreeNode] label with a main label as well as short
/// contents, and a quoting string.
fn labelled(label: impl ToString, contents: impl ToString, quote_str: &str) -> String {
    format!("{} {quote_str}{}{quote_str}", label.to_string(), contents.to_string())
}

impl AstVisitor for AstTreePrinter {
    type Error = Infallible;

    type NameRet = TreeNode;
    fn visit_name(&self, node: ast::AstNodeRef<ast::Name>) -> Result<Self::NameRet, Self::Error> {
        Ok(TreeNode::leaf(node.ident))
    }

    type LitRet = TreeNode;
    fn visit_lit(&self, node: ast::AstNodeRef<ast::Lit>) -> Result<Self::LitRet, Self::Error> {
        walk::walk_lit_same_children(self, node)
    }

    type ArrayLitRet = TreeNode;
    fn visit_array_lit(
        &self,
        node: ast::AstNodeRef<ast::ArrayLit>,
    ) -> Result<Self::ArrayLitRet, Self::Error> {
        let children = walk::walk_array_lit(self, node)?;
        Ok(TreeNode::branch("array", children.elements))
    }

    type TupleLitEntryRet = TreeNode;
    fn visit_tuple_lit_entry(
        &self,
        node: ast::AstNodeRef<ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        let walk::TupleLitEntry { name, ty, value } = walk::walk_tuple_lit_entry(self, node)?;

        Ok(TreeNode::branch(
            "entry",
            name.map(|t| TreeNode::branch("name", vec![t]))
                .into_iter()
                .chain(ty.map(|t| TreeNode::branch("type", vec![t])))
                .chain(iter::once(TreeNode::branch("value", vec![value])))
                .collect(),
        ))
    }

    type TupleLitRet = TreeNode;

    fn visit_tuple_lit(
        &self,
        node: ast::AstNodeRef<ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        let children = walk::walk_tuple_lit(self, node)?;
        Ok(TreeNode::branch("tuple", children.elements))
    }

    type StrLitRet = TreeNode;
    fn visit_str_lit(
        &self,
        node: ast::AstNodeRef<ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("str", format!("{:?}", node.data), "")))
    }

    type ByteLitRet = TreeNode;
    fn visit_byte_lit(
        &self,
        node: ast::AstNodeRef<ast::ByteLit>,
    ) -> Result<Self::CharLitRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("byte", node.data, "'")))
    }

    type CharLitRet = TreeNode;
    fn visit_char_lit(
        &self,
        node: ast::AstNodeRef<ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("char", node.data, "'")))
    }

    type FloatLitRet = TreeNode;
    fn visit_float_lit(
        &self,
        _: ast::AstNodeRef<ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        Ok(TreeNode::leaf("float"))
    }

    type BoolLitRet = TreeNode;
    fn visit_bool_lit(
        &self,
        node: ast::AstNodeRef<ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("bool", node.data, "")))
    }

    type IntLitRet = TreeNode;
    fn visit_int_lit(
        &self,
        _: ast::AstNodeRef<ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error> {
        Ok(TreeNode::leaf("integer"))
    }

    type BinOpRet = TreeNode;
    fn visit_bin_op(
        &self,
        node: ast::AstNodeRef<ast::BinOp>,
    ) -> Result<Self::BinOpRet, Self::Error> {
        Ok(TreeNode::leaf(format!("operator `{}`", node.body())))
    }

    type UnOpRet = TreeNode;
    fn visit_un_op(&self, node: ast::AstNodeRef<ast::UnOp>) -> Result<Self::UnOpRet, Self::Error> {
        Ok(TreeNode::leaf(format!("operator `{}`", node.body())))
    }

    type ExprRet = TreeNode;
    fn visit_expr(&self, node: ast::AstNodeRef<ast::Expr>) -> Result<Self::ExprRet, Self::Error> {
        walk::walk_expr_same_children(self, node)
    }

    type VariableExprRet = TreeNode;
    fn visit_variable_expr(
        &self,
        node: ast::AstNodeRef<ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        let walk::VariableExpr { name } = walk::walk_variable_expr(self, node)?;
        Ok(TreeNode::branch("variable", vec![TreeNode::leaf(labelled("named", name.label, "\""))]))
    }

    type ExprArgRet = TreeNode;
    fn visit_expr_arg(
        &self,
        node: ast::AstNodeRef<ast::ExprArg>,
    ) -> Result<Self::ExprArgRet, Self::Error> {
        if let Some(name) = &node.name {
            Ok(TreeNode::branch(
                "arg",
                vec![
                    TreeNode::leaf(labelled("named", name.ident, "\"")),
                    TreeNode::branch("value", vec![self.visit_expr(node.value.ast_ref())?]),
                ],
            ))
        } else {
            self.visit_expr(node.value.ast_ref())
        }
    }

    type ConstructorCallExprRet = TreeNode;
    fn visit_constructor_call_expr(
        &self,
        node: ast::AstNodeRef<ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        let walk::ConstructorCallExpr { subject, args } =
            walk::walk_constructor_call_expr(self, node)?;

        let children = if !node.args.is_empty() {
            vec![TreeNode::branch("subject", vec![subject]), TreeNode::branch("args", args)]
        } else {
            vec![TreeNode::branch("subject", vec![subject])]
        };

        Ok(TreeNode::branch("constructor", children))
    }

    type PropertyKindRet = TreeNode;
    fn visit_property_kind(
        &self,
        node: ast::AstNodeRef<ast::PropertyKind>,
    ) -> Result<Self::PropertyKindRet, Self::Error> {
        Ok(match node.body() {
            ast::PropertyKind::NamedField(name) => TreeNode::leaf(labelled("property", name, "\"")),
            ast::PropertyKind::NumericField(name) => {
                TreeNode::leaf(labelled("numeric_property", name, "\""))
            }
        })
    }

    type AccessExprRet = TreeNode;
    fn visit_access_expr(
        &self,
        node: ast::AstNodeRef<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let walk::AccessExpr { subject, property, .. } = walk::walk_access_expr(self, node)?;
        Ok(TreeNode::branch(
            "access",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::branch("property", vec![property]),
                TreeNode::leaf(labelled("kind", node.kind, "\"")),
            ],
        ))
    }

    type AccessKindRet = TreeNode;
    fn visit_access_kind(
        &self,
        node: ast::AstNodeRef<ast::AccessKind>,
    ) -> Result<Self::AccessKindRet, Self::Error> {
        match node.body() {
            ast::AccessKind::Property => Ok(TreeNode::leaf("property")),
            ast::AccessKind::Namespace => Ok(TreeNode::leaf("namespace")),
        }
    }

    type RefExprRet = TreeNode;
    fn visit_ref_expr(
        &self,
        node: ast::AstNodeRef<ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let walk::RefExpr { inner_expr, mutability, kind: _ } = walk::walk_ref_expr(self, node)?;
        Ok(TreeNode::branch(
            "ref",
            iter::once(inner_expr)
                .chain(mutability.map(|inner| TreeNode::branch("mutability", vec![inner])))
                .collect(),
        ))
    }

    type DerefExprRet = TreeNode;
    fn visit_deref_expr(
        &self,
        node: ast::AstNodeRef<ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::DerefExpr { data } = walk::walk_deref_expr(self, node)?;
        Ok(TreeNode::branch("deref", vec![data]))
    }

    type UnsafeExprRet = TreeNode;
    fn visit_unsafe_expr(
        &self,
        node: ast::AstNodeRef<ast::UnsafeExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::UnsafeExpr { data } = walk::walk_unsafe_expr(self, node)?;
        Ok(TreeNode::branch("unsafe", vec![data]))
    }

    type LitExprRet = TreeNode;
    fn visit_lit_expr(
        &self,
        node: ast::AstNodeRef<ast::LitExpr>,
    ) -> Result<Self::LitExprRet, Self::Error> {
        let walk::LitExpr { data } = walk::walk_lit_expr(self, node)?;
        Ok(data)
    }

    type CastExprRet = TreeNode;
    fn visit_cast_expr(
        &self,
        node: ast::AstNodeRef<ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let walk::CastExpr { ty, expr } = walk::walk_cast_expr(self, node)?;
        Ok(TreeNode::branch(
            "cast",
            vec![TreeNode::branch("subject", vec![expr]), TreeNode::branch("type", vec![ty])],
        ))
    }

    type TyExprRet = TreeNode;
    fn visit_ty_expr(
        &self,
        node: ast::AstNodeRef<ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error> {
        let walk::TyExpr { ty } = walk::walk_ty_expr(self, node)?;

        Ok(TreeNode::branch("type_expr", vec![ty]))
    }

    type BlockExprRet = TreeNode;
    fn visit_block_expr(
        &self,
        node: ast::AstNodeRef<ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        Ok(walk::walk_block_expr(self, node)?.data)
    }

    type ImportRet = TreeNode;
    fn visit_import(
        &self,
        node: ast::AstNodeRef<ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        Ok(TreeNode::leaf(labelled("import", node.path, "\"")))
    }

    type ImportExprRet = TreeNode;
    fn visit_import_expr(
        &self,
        node: ast::AstNodeRef<ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(walk::walk_import_expr(self, node)?.data)
    }

    type TyRet = TreeNode;
    fn visit_ty(&self, node: ast::AstNodeRef<ast::Ty>) -> Result<Self::TyRet, Self::Error> {
        walk::walk_ty_same_children(self, node)
    }

    type TupleTyRet = TreeNode;
    fn visit_tuple_ty(
        &self,
        node: ast::AstNodeRef<ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        let walk::TupleTy { entries } = walk::walk_tuple_ty(self, node)?;

        Ok(TreeNode::branch("tuple", vec![entries]))
    }

    type ArrayTyRet = TreeNode;
    fn visit_array_ty(
        &self,
        node: ast::AstNodeRef<ast::ArrayTy>,
    ) -> Result<Self::ArrayTyRet, Self::Error> {
        let walk::ArrayTy { inner, len } = walk::walk_array_ty(self, node)?;

        Ok(TreeNode::branch(
            "array",
            iter::once(TreeNode::branch("element", vec![inner]))
                .chain(len.map(|inner| TreeNode::branch("length", vec![inner])))
                .collect(),
        ))
    }

    type TyArgRet = TreeNode;
    fn visit_ty_arg(
        &self,
        node: ast::AstNodeRef<ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        let walk::TyArg { name, ty, macros } = walk::walk_ty_arg(self, node)?;

        if name.is_some() || macros.is_some() {
            let children = iter::empty()
                .chain(name.map(|t| TreeNode::branch("name", vec![t])))
                .chain(iter::once(TreeNode::branch("type", vec![ty])))
                .chain(macros)
                .collect_vec();

            Ok(TreeNode::branch("field", children))
        } else {
            Ok(ty)
        }
    }

    type FnTyRet = TreeNode;
    fn visit_fn_ty(&self, node: ast::AstNodeRef<ast::FnTy>) -> Result<Self::FnTyRet, Self::Error> {
        let walk::FnTy { params, return_ty } = walk::walk_fn_ty(self, node)?;

        let return_child = TreeNode::branch("return", vec![return_ty]);

        let children = {
            if params.children.is_empty() {
                vec![return_child]
            } else {
                vec![params, return_child]
            }
        };

        Ok(TreeNode::branch("function", children))
    }

    type TyFnTyRet = TreeNode;
    fn visit_ty_fn_ty(
        &self,
        node: ast::AstNodeRef<ast::TyFnTy>,
    ) -> Result<Self::TyFnTyRet, Self::Error> {
        let walk::TyFnTy { params, return_ty } = walk::walk_ty_fn_ty(self, node)?;

        Ok(TreeNode::branch(
            "type_function",
            vec![params, TreeNode::branch("return", vec![return_ty])],
        ))
    }

    type TyFnCallRet = TreeNode;
    fn visit_ty_fn_call(
        &self,
        node: ast::AstNodeRef<ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error> {
        let walk::TyFnCall { subject, args } = walk::walk_ty_fn_call(self, node)?;

        Ok(TreeNode::branch(
            "type_function_call",
            vec![TreeNode::branch("subject", vec![subject]), TreeNode::branch("arguments", args)],
        ))
    }

    type NamedTyRet = TreeNode;
    fn visit_named_ty(
        &self,
        node: ast::AstNodeRef<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        let walk::NamedTy { name } = walk::walk_named_ty(self, node)?;
        Ok(TreeNode::leaf(labelled("named", name.label, "\"")))
    }

    type AccessTyRet = TreeNode;
    fn visit_access_ty(
        &self,
        node: ast::AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        let walk::AccessTy { subject, .. } = walk::walk_access_ty(self, node)?;
        Ok(TreeNode::branch(
            "access",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::leaf(labelled("property", node.property.ident, "\"")),
            ],
        ))
    }

    type RefTyRet = TreeNode;
    fn visit_ref_ty(
        &self,
        node: ast::AstNodeRef<ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error> {
        let walk::RefTy { inner, mutability, .. } = walk::walk_ref_ty(self, node)?;

        let label = if node.kind.as_ref().map_or(false, |t| *t.body() == ast::RefKind::Raw) {
            "raw_ref"
        } else {
            "ref"
        };

        Ok(TreeNode::branch(
            label,
            iter::once(inner)
                .chain(mutability.map(|t| TreeNode::branch("mutability", vec![t])))
                .collect(),
        ))
    }

    type MergeTyRet = TreeNode;
    fn visit_merge_ty(
        &self,
        node: ast::AstNodeRef<ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error> {
        let walk::MergeTy { lhs, rhs } = walk::walk_merge_ty(self, node)?;

        Ok(TreeNode::branch(
            "merge_ty",
            vec![TreeNode::branch("lhs", vec![lhs]), TreeNode::branch("rhs", vec![rhs])],
        ))
    }

    type UnionTyRet = TreeNode;
    fn visit_union_ty(
        &self,
        node: ast::AstNodeRef<ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error> {
        let walk::UnionTy { lhs, rhs } = walk::walk_union_ty(self, node)?;

        Ok(TreeNode::branch(
            "union",
            vec![TreeNode::branch("lhs", vec![lhs]), TreeNode::branch("rhs", vec![rhs])],
        ))
    }

    type ExprTyRet = TreeNode;

    fn visit_expr_ty(
        &self,
        node: ast::AstNodeRef<ast::ExprTy>,
    ) -> Result<Self::ExprTyRet, Self::Error> {
        let walk::ExprTy { expr } = walk::walk_expr_ty(self, node)?;

        Ok(TreeNode::branch("expr", vec![expr]))
    }

    type TyFnDefRet = TreeNode;
    fn visit_ty_fn_def(
        &self,
        node: ast::AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let walk::TyFnDef { params, return_ty, ty_fn_body } = walk::walk_ty_fn_def(self, node)?;

        Ok(TreeNode::branch(
            "type_function",
            iter::once(params)
                .chain(return_ty.map(|r| TreeNode::branch("return_type", vec![r])))
                .chain(iter::once(TreeNode::branch("body", vec![ty_fn_body])))
                .collect(),
        ))
    }

    type FnDefRet = TreeNode;
    fn visit_fn_def(
        &self,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let walk::FnDef { params, fn_body, return_ty } = walk::walk_fn_def(self, node)?;

        Ok(TreeNode::branch(
            "function_def",
            iter::once(params)
                .chain(return_ty.map(|r| TreeNode::branch("return_type", vec![r])))
                .chain(iter::once(fn_body))
                .collect(),
        ))
    }

    type ParamsRet = TreeNode;
    fn visit_params(
        &self,
        node: ast::AstNodeRef<ast::Params>,
    ) -> Result<Self::TyParamsRet, Self::Error> {
        let walk::Params { params } = walk::walk_params(self, node)?;
        Ok(TreeNode::branch(format!("{}s", node.origin.field_name()), params))
    }

    type ParamRet = TreeNode;
    fn visit_param(
        &self,
        node: ast::AstNodeRef<ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        let walk::Param { name, ty, default, macros } = walk::walk_param(self, node)?;

        let children = iter::empty()
            .chain(name.map(|t| TreeNode::branch("name", vec![t])))
            .chain(ty.map(|t| TreeNode::branch("type", vec![t])))
            .chain(default.map(|d| TreeNode::branch("default", vec![d])))
            .chain(macros)
            .collect_vec();

        Ok(TreeNode::branch("param", children))
    }

    type TyParamRet = TreeNode;
    fn visit_ty_param(
        &self,
        node: ast::AstNodeRef<ast::TyParam>,
    ) -> Result<Self::ParamRet, Self::Error> {
        let walk::TyParam { name, ty, default, macros } = walk::walk_ty_param(self, node)?;

        let children = iter::empty()
            .chain(name.map(|t| TreeNode::branch("name", vec![t])))
            .chain(ty.map(|t| TreeNode::branch("type", vec![t])))
            .chain(default.map(|d| TreeNode::branch("default", vec![d])))
            .chain(macros)
            .collect_vec();

        Ok(TreeNode::branch("ty_param", children))
    }

    type TyParamsRet = TreeNode;
    fn visit_ty_params(
        &self,
        node: ast::AstNodeRef<ast::TyParams>,
    ) -> Result<Self::TyParamsRet, Self::Error> {
        let walk::TyParams { params } = walk::walk_ty_params(self, node)?;
        Ok(TreeNode::branch("ty_params", params))
    }

    type BlockRet = TreeNode;
    fn visit_block(
        &self,
        node: ast::AstNodeRef<ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        walk::walk_block_same_children(self, node)
    }

    type MatchCaseRet = TreeNode;

    fn visit_match_case(
        &self,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let walk::MatchCase { expr, pat, macros } = walk::walk_match_case(self, node)?;

        let mut children = vec![pat, TreeNode::branch("branch", vec![expr])];

        if let Some(macros) = macros {
            children.push(macros)
        }

        Ok(TreeNode::branch("case", children))
    }

    type MatchBlockRet = TreeNode;

    fn visit_match_block(
        &self,
        node: ast::AstNodeRef<ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let walk::MatchBlock { cases, subject } = walk::walk_match_block(self, node)?;

        Ok(TreeNode::branch(
            "match",
            vec![TreeNode::branch("subject", vec![subject]), TreeNode::branch("cases", cases)],
        ))
    }

    type LoopBlockRet = TreeNode;
    fn visit_loop_block(
        &self,
        node: ast::AstNodeRef<ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let walk::LoopBlock { contents } = walk::walk_loop_block(self, node)?;
        Ok(TreeNode::branch("loop", vec![contents]))
    }

    type ForLoopBlockRet = TreeNode;
    fn visit_for_loop_block(
        &self,
        node: ast::AstNodeRef<ast::ForLoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let walk::ForLoopBlock { pat: pattern, iterator, for_body } =
            walk::walk_for_loop_block(self, node)?;

        Ok(TreeNode::branch("for_loop", vec![pattern, iterator, for_body]))
    }

    type WhileLoopBlockRet = TreeNode;
    fn visit_while_loop_block(
        &self,
        node: ast::AstNodeRef<ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        let walk::WhileLoopBlock { condition, while_body } =
            walk::walk_while_loop_block(self, node)?;
        Ok(TreeNode::branch("while_loop", vec![condition, while_body]))
    }

    type ModDefRet = TreeNode;
    fn visit_mod_def(
        &self,
        node: ast::AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        let walk::ModDef { block, ty_params } = walk::walk_mod_def(self, node)?;
        let children = {
            if let Some(ty_params) = ty_params {
                vec![ty_params, block]
            } else {
                vec![block]
            }
        };

        Ok(TreeNode::branch("mod", children))
    }

    type IfClauseRet = TreeNode;
    fn visit_if_clause(
        &self,
        node: ast::AstNodeRef<ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        let walk::IfClause { condition, if_body } = walk::walk_if_clause(self, node)?;

        Ok(TreeNode::branch(
            "clause",
            vec![
                TreeNode::branch("condition", vec![condition]),
                TreeNode::branch("body", vec![if_body]),
            ],
        ))
    }

    type IfBlockRet = TreeNode;
    fn visit_if_block(
        &self,
        node: ast::AstNodeRef<ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        let walk::IfBlock { clauses, otherwise } = walk::walk_if_block(self, node)?;

        let mut children = vec![TreeNode::branch("clauses", clauses)];

        if let Some(else_clause) = otherwise {
            children.push(TreeNode::branch("otherwise", vec![else_clause]))
        }

        Ok(TreeNode::branch("if", children))
    }

    type BodyBlockRet = TreeNode;
    fn visit_body_block(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let walk::BodyBlock { statements, expr } = walk::walk_body_block(self, node)?;

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
        &self,
        node: ast::AstNodeRef<ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let walk::ReturnStatement { expr } = walk::walk_return_statement(self, node)?;
        Ok(TreeNode::branch("return", expr.into_iter().collect()))
    }

    type BreakStatementRet = TreeNode;
    fn visit_break_statement(
        &self,
        _: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        Ok(TreeNode::leaf("break"))
    }

    type ContinueStatementRet = TreeNode;
    fn visit_continue_statement(
        &self,
        _: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        Ok(TreeNode::leaf("continue"))
    }

    type VisibilityRet = TreeNode;
    fn visit_visibility(
        &self,
        node: ast::AstNodeRef<ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        match node.body() {
            ast::Visibility::Private => Ok(TreeNode::leaf("private")),
            ast::Visibility::Public => Ok(TreeNode::leaf("public")),
        }
    }

    type MutabilityRet = TreeNode;

    fn visit_mutability(
        &self,
        node: ast::AstNodeRef<ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error> {
        match node.body() {
            ast::Mutability::Mutable => Ok(TreeNode::leaf("mutable")),
            ast::Mutability::Immutable => Ok(TreeNode::leaf("immutable")),
        }
    }

    type RefKindRet = ();

    fn visit_ref_kind(
        &self,
        _: ast::AstNodeRef<ast::RefKind>,
    ) -> Result<Self::RefKindRet, Self::Error> {
        Ok(())
    }

    type DeclarationRet = TreeNode;
    fn visit_declaration(
        &self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let walk::Declaration { pat: pattern, ty, value } = walk::walk_declaration(self, node)?;

        Ok(TreeNode::branch(
            "declaration",
            iter::once(TreeNode::branch("pattern", vec![pattern]))
                .chain(ty.map(|t| TreeNode::branch("type", vec![t])))
                .chain(value.map(|t| TreeNode::branch("value", vec![t])))
                .collect(),
        ))
    }

    type AssignExprRet = TreeNode;
    fn visit_assign_expr(
        &self,
        node: ast::AstNodeRef<ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error> {
        let walk::AssignExpr { lhs, rhs } = walk::walk_assign_expr(self, node)?;
        Ok(TreeNode::branch(
            "assign",
            vec![TreeNode::branch("lhs", vec![lhs]), TreeNode::branch("rhs", vec![rhs])],
        ))
    }

    type AssignOpExprRet = TreeNode;
    fn visit_assign_op_expr(
        &self,
        node: ast::AstNodeRef<ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error> {
        let walk::AssignOpExpr { lhs, rhs, operator } = walk::walk_assign_op_expr(self, node)?;
        Ok(TreeNode::branch(
            "assign",
            vec![operator, TreeNode::branch("lhs", vec![lhs]), TreeNode::branch("rhs", vec![rhs])],
        ))
    }

    type BinaryExprRet = TreeNode;
    fn visit_binary_expr(
        &self,
        node: ast::AstNodeRef<ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error> {
        let walk::BinaryExpr { operator, lhs, rhs } = walk::walk_binary_expr(self, node)?;

        Ok(TreeNode::branch(
            "binary_expr",
            vec![operator, TreeNode::branch("lhs", vec![lhs]), TreeNode::branch("rhs", vec![rhs])],
        ))
    }

    type UnaryExprRet = TreeNode;

    fn visit_unary_expr(
        &self,
        node: ast::AstNodeRef<ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error> {
        let walk::UnaryExpr { operator, expr } = walk::walk_unary_expr(self, node)?;

        Ok(TreeNode::branch("unary_expr", vec![operator, TreeNode::branch("expr", vec![expr])]))
    }

    type IndexExprRet = TreeNode;
    fn visit_index_expr(
        &self,
        node: ast::AstNodeRef<ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error> {
        let walk::IndexExpr { subject, index_expr } = walk::walk_index_expr(self, node)?;

        Ok(TreeNode::branch(
            "index",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::branch("index_expr", vec![index_expr]),
            ],
        ))
    }

    type RepeatExprRet = TreeNode;

    fn visit_repeat_expr(
        &self,
        node: ast::AstNodeRef<ast::RepeatExpr>,
    ) -> Result<Self::RepeatExprRet, Self::Error> {
        let walk::RepeatExpr { subject, repeat } = walk::walk_repeat_expr(self, node)?;

        Ok(TreeNode::branch(
            "repeat_expr",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::branch("repeat", vec![repeat]),
            ],
        ))
    }

    type StructDefRet = TreeNode;
    fn visit_struct_def(
        &self,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let walk::StructDef { fields, ty_params } = walk::walk_struct_def(self, node)?;

        let children = {
            if let Some(ty_params) = ty_params && !ty_params.children.is_empty() {
                vec![ty_params, fields]
            } else {
                vec![fields]
            }
        };

        Ok(TreeNode::branch("struct_def", children))
    }

    type EnumDefEntryRet = TreeNode;
    fn visit_enum_def_entry(
        &self,
        node: ast::AstNodeRef<ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        let walk::EnumDefEntry { name, fields, ty, macros } =
            walk::walk_enum_def_entry(self, node)?;

        let children = iter::once(TreeNode::leaf("variant"))
            .chain(macros)
            .chain(fields)
            .chain(ty.map(|t| TreeNode::branch("type", vec![t])))
            .collect_vec();

        Ok(TreeNode::branch(labelled("variant", name.label, "\""), children))
    }

    type EnumDefRet = TreeNode;
    fn visit_enum_def(
        &self,
        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let walk::EnumDef { entries, ty_params } = walk::walk_enum_def(self, node)?;

        let variants = TreeNode::branch("variants", entries);
        let children = {
            if let Some(ty_params) = ty_params && !ty_params.children.is_empty() {
                vec![ty_params, variants]
            } else {
                vec![variants]
            }
        };

        Ok(TreeNode::branch("enum_def", children))
    }

    type PatRet = TreeNode;
    fn visit_pat(&self, node: ast::AstNodeRef<ast::Pat>) -> Result<Self::PatRet, Self::Error> {
        walk::walk_pat_same_children(self, node)
    }

    type AccessPatRet = TreeNode;
    fn visit_access_pat(
        &self,
        node: ast::AstNodeRef<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        let walk::AccessPat { subject, .. } = walk::walk_access_pat(self, node)?;
        Ok(TreeNode::branch(
            "access",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::leaf(labelled("property", node.property.ident, "\"")),
            ],
        ))
    }

    type ConstructorPatRet = TreeNode;
    fn visit_constructor_pat(
        &self,
        node: ast::AstNodeRef<ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        let walk::ConstructorPat { subject, mut fields, spread } =
            walk::walk_constructor_pat(self, node)?;

        // If the pattern contains a spread, place it in the position that it
        // was specified in the source.
        if let Some(spread) = spread && let Some(spread_node) = &node.spread {
            fields.insert(spread_node.position, TreeNode::branch("spread", vec![spread]));
        }

        let children = if !node.fields.is_empty() {
            vec![TreeNode::branch("subject", vec![subject]), TreeNode::branch("fields", fields)]
        } else {
            vec![TreeNode::branch("subject", vec![subject])]
        };

        Ok(TreeNode::branch("constructor", children))
    }

    type PatArgRet = TreeNode;
    fn visit_pat_arg(
        &self,
        node: ast::AstNodeRef<ast::PatArg>,
    ) -> Result<Self::PatArgRet, Self::Error> {
        let walk::PatArg { name, pat, macros } = walk::walk_pat_arg(self, node)?;

        let mut children = name
            .map(|t| TreeNode::branch("name", vec![t]))
            .into_iter()
            .chain(iter::once(TreeNode::branch("pattern", vec![pat])))
            .collect_vec();

        if let Some(macros) = macros {
            children.push(macros);
        }

        Ok(TreeNode::branch("entry", children))
    }

    type TuplePatRet = TreeNode;
    fn visit_tuple_pat(
        &self,
        node: ast::AstNodeRef<ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        let walk::TuplePat { mut fields, spread } = walk::walk_tuple_pat(self, node)?;

        // If the pattern contains a spread, place it in the position that it
        // was specified in the source.
        if let Some(spread) = spread && let Some(spread_node) = &node.spread {
            fields.insert(spread_node.position, TreeNode::branch("spread", vec![spread]));
        }

        Ok(TreeNode::branch("tuple", fields))
    }

    type ArrayPatRet = TreeNode;
    fn visit_array_pat(
        &self,
        node: ast::AstNodeRef<ast::ArrayPat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        let walk::ArrayPat { mut fields, spread } = walk::walk_array_pat(self, node)?;

        // If the pattern contains a spread, place it in the position that it
        // was specified in the source.
        if let Some(spread) = spread && let Some(spread_node) = node.spread.as_ref() {
            fields.insert(spread_node.position, spread)
        }

        Ok(TreeNode::branch("list", fields))
    }

    type SpreadPatRet = TreeNode;
    fn visit_spread_pat(
        &self,
        node: ast::AstNodeRef<ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error> {
        let walk::SpreadPat { name } = walk::walk_spread_pat(self, node)?;

        if let Some(name) = name {
            Ok(TreeNode::leaf(labelled("spread", name.label, "\"")))
        } else {
            Ok(TreeNode::leaf("spread"))
        }
    }

    type LitPatRet = TreeNode;
    fn visit_lit_pat(
        &self,
        node: ast::AstNodeRef<ast::LitPat>,
    ) -> Result<Self::LitPatRet, Self::Error> {
        let walk::LitPat { data } = walk::walk_lit_pat(self, node)?;
        Ok(data)
    }

    type RangePatRet = TreeNode;
    fn visit_range_pat(
        &self,
        node: ast::AstNodeRef<ast::RangePat>,
    ) -> Result<Self::RangePatRet, Self::Error> {
        let walk::RangePat { lo, hi } = walk::walk_range_pat(self, node)?;
        let mut branches = vec![];

        if let Some(lo) = lo {
            branches.push(TreeNode::branch("lo", vec![lo]))
        }
        if let Some(hi) = hi {
            branches.push(TreeNode::branch("hi", vec![hi]))
        }
        branches.push(TreeNode::leaf(labelled("end", format!("{}", node.body().end), "`")));
        Ok(TreeNode::branch("range", branches))
    }

    type OrPatRet = TreeNode;
    fn visit_or_pat(
        &self,
        node: ast::AstNodeRef<ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error> {
        let walk::OrPat { variants } = walk::walk_or_pat(self, node)?;
        Ok(TreeNode::branch("or", variants))
    }

    type IfPatRet = TreeNode;

    fn visit_if_pat(
        &self,
        node: ast::AstNodeRef<ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error> {
        let walk::IfPat { condition, pat } = walk::walk_if_pat(self, node)?;
        Ok(TreeNode::branch(
            "if",
            vec![
                TreeNode::branch("condition", vec![condition]),
                TreeNode::branch("pattern", vec![pat]),
            ],
        ))
    }

    type BindingPatRet = TreeNode;

    fn visit_binding_pat(
        &self,
        node: ast::AstNodeRef<ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        let walk::BindingPat { name, .. } = walk::walk_binding_pat(self, node)?;

        Ok(TreeNode::branch(
            "binding",
            iter::once(TreeNode::leaf(labelled("name", name.label, "\"")))
                .chain(
                    node.visibility
                        .as_ref()
                        .map(|t| TreeNode::leaf(labelled("visibility", t.body(), "\""))),
                )
                .chain(
                    node.mutability
                        .as_ref()
                        .map(|t| TreeNode::leaf(labelled("mutability", t.body(), "\""))),
                )
                .collect(),
        ))
    }

    type WildPatRet = TreeNode;

    fn visit_wild_pat(
        &self,
        _: ast::AstNodeRef<ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error> {
        Ok(TreeNode::leaf("ignore"))
    }

    type ModulePatEntryRet = TreeNode;

    fn visit_module_pat_entry(
        &self,
        node: ast::AstNodeRef<ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        let walk::ModulePatEntry { name, pat: pattern } = walk::walk_module_pat_entry(self, node)?;
        Ok(TreeNode::branch(labelled("assign", name.label, "\""), vec![pattern]))
    }

    type ModulePatRet = TreeNode;

    fn visit_module_pat(
        &self,
        node: ast::AstNodeRef<ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error> {
        let walk::ModulePat { fields } = walk::walk_module_pat(self, node)?;
        Ok(TreeNode::branch("module", vec![TreeNode::branch("members", fields)]))
    }

    type ModuleRet = TreeNode;

    fn visit_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let walk::Module { contents, macros } = walk::walk_module(self, node)?;
        let children = if !macros.children.is_empty() {
            vec![TreeNode::branch("contents", contents), macros]
        } else {
            contents
        };

        Ok(TreeNode::branch("module", children))
    }
    type TokenStreamRet = TreeNode;

    fn visit_token_stream(
        &self,
        _: ast::AstNodeRef<ast::TokenStream>,
    ) -> Result<Self::TokenStreamRet, Self::Error> {
        Ok(TreeNode::leaf("stream"))
    }

    type TokenMacroRet = TreeNode;

    fn visit_token_macro(
        &self,
        node: ast::AstNodeRef<ast::TokenMacro>,
    ) -> Result<Self::TokenMacroRet, Self::Error> {
        let walk::TokenMacro { args, .. } = walk::walk_token_macro(self, node)?;

        let mut children = vec![TreeNode::leaf(labelled("name", node.name.ident, "\""))];

        if let Some(args) = args {
            children.push(args)
        }

        Ok(TreeNode::branch("token_macro", children))
    }

    type TokenMacroInvocationRet = TreeNode;

    fn visit_token_macro_invocation(
        &self,
        node: ast::AstNodeRef<ast::TokenMacroInvocation>,
    ) -> Result<Self::TokenMacroInvocationRet, Self::Error> {
        let walk::TokenMacroInvocation { mac, stream } =
            walk::walk_token_macro_invocation(self, node)?;
        Ok(TreeNode::branch("token_macro_invocation", vec![mac, stream]))
    }

    type MacroInvocationArgRet = TreeNode;

    fn visit_macro_invocation_arg(
        &self,
        node: ast::AstNodeRef<ast::MacroInvocationArg>,
    ) -> Result<Self::MacroInvocationArgRet, Self::Error> {
        let walk::MacroInvocationArg { value, .. } = walk::walk_macro_invocation_arg(self, node)?;

        if let Some(name) = &node.name {
            Ok(TreeNode::branch(
                "arg",
                vec![
                    TreeNode::leaf(labelled("named", name.ident, "\"")),
                    TreeNode::branch("value", vec![value]),
                ],
            ))
        } else {
            Ok(value)
        }
    }

    type MacroInvocationRet = TreeNode;

    fn visit_macro_invocation(
        &self,
        node: ast::AstNodeRef<ast::MacroInvocation>,
    ) -> Result<Self::MacroInvocationRet, Self::Error> {
        let walk::MacroInvocation { args, .. } = walk::walk_macro_invocation(self, node)?;

        let mut children = vec![TreeNode::leaf(labelled("name", node.name.ident, "\""))];

        if let Some(args) = args {
            children.push(args)
        }

        Ok(TreeNode::branch("macro", children))
    }

    type MacroInvocationsRet = TreeNode;

    fn visit_macro_invocations(
        &self,
        node: ast::AstNodeRef<ast::MacroInvocations>,
    ) -> Result<Self::MacroInvocationsRet, Self::Error> {
        let walk::MacroInvocations { invocations } = walk::walk_macro_invocations(self, node)?;

        Ok(TreeNode::branch("macro_invocations", invocations))
    }

    type PatMacroInvocationRet = TreeNode;

    fn visit_pat_macro_invocation(
        &self,
        node: ast::AstNodeRef<ast::PatMacroInvocation>,
    ) -> Result<Self::PatMacroInvocationRet, Self::Error> {
        let walk::PatMacroInvocation { macros, subject } =
            walk::walk_pat_macro_invocation(self, node)?;

        Ok(TreeNode::branch(
            "pattern_macro",
            vec![macros, TreeNode::branch("pattern", vec![subject])],
        ))
    }

    type ExprMacroInvocationRet = TreeNode;

    fn visit_expr_macro_invocation(
        &self,
        node: ast::AstNodeRef<ast::ExprMacroInvocation>,
    ) -> Result<Self::ExprMacroInvocationRet, Self::Error> {
        let walk::ExprMacroInvocation { macros, subject } =
            walk::walk_expr_macro_invocation(self, node)?;

        Ok(TreeNode::branch("expr_macro", vec![macros, TreeNode::branch("expr", vec![subject])]))
    }

    type TyMacroInvocationRet = TreeNode;

    fn visit_ty_macro_invocation(
        &self,
        node: ast::AstNodeRef<ast::TyMacroInvocation>,
    ) -> Result<Self::TyMacroInvocationRet, Self::Error> {
        let walk::TyMacroInvocation { macros, subject } =
            walk::walk_ty_macro_invocation(self, node)?;

        Ok(TreeNode::branch("type_macro", vec![macros, TreeNode::branch("type", vec![subject])]))
    }

    type MacroInvocationArgsRet = TreeNode;

    fn visit_macro_invocation_args(
        &self,
        node: ast::AstNodeRef<ast::MacroInvocationArgs>,
    ) -> Result<Self::MacroInvocationArgsRet, Self::Error> {
        let walk::MacroInvocationArgs { args } = walk::walk_macro_invocation_args(self, node)?;

        Ok(TreeNode::branch("args", args))
    }
}
