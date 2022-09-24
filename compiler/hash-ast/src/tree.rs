//! AST visualisation utilities.

use std::{convert::Infallible, iter};

use hash_utils::tree_writing::TreeNode;

use crate::{
    ast::{self, FloatLit, IntLit},
    visitor::{walk, AstVisitor},
};

/// Struct implementing [crate::visitor::AstVisitor], for the purpose of
/// transforming the AST tree into a [TreeNode] tree, for visualisation
/// purposes.
pub struct AstTreeGenerator;

/// Easy way to format a [TreeNode] label with a main label as well as short
/// contents, and a quoting string.
fn labelled(label: impl ToString, contents: impl ToString, quote_str: &str) -> String {
    format!("{} {}{}{}", label.to_string(), quote_str, contents.to_string(), quote_str)
}

impl AstVisitor for AstTreeGenerator {
    type Error = Infallible;

    type NameRet = TreeNode;
    fn visit_name(&self, node: ast::AstNodeRef<ast::Name>) -> Result<Self::NameRet, Self::Error> {
        Ok(TreeNode::leaf(node.ident))
    }

    type LitRet = TreeNode;
    fn visit_lit(&self, node: ast::AstNodeRef<ast::Lit>) -> Result<Self::LitRet, Self::Error> {
        walk::walk_lit_same_children(self, node)
    }

    type MapLitRet = TreeNode;
    fn visit_map_lit(
        &self,
        node: ast::AstNodeRef<ast::MapLit>,
    ) -> Result<Self::MapLitRet, Self::Error> {
        Ok(TreeNode::branch("map", walk::walk_map_lit(self, node)?.elements))
    }

    type MapLitEntryRet = TreeNode;
    fn visit_map_lit_entry(
        &self,
        node: ast::AstNodeRef<ast::MapLitEntry>,
    ) -> Result<Self::MapLitEntryRet, Self::Error> {
        let walk::MapLitEntry { key, value } = walk::walk_map_lit_entry(self, node)?;
        Ok(TreeNode::branch(
            "entry",
            vec![TreeNode::branch("key", vec![key]), TreeNode::branch("value", vec![value])],
        ))
    }

    type ListLitRet = TreeNode;
    fn visit_list_lit(
        &self,
        node: ast::AstNodeRef<ast::ListLit>,
    ) -> Result<Self::ListLitRet, Self::Error> {
        let children = walk::walk_list_lit(self, node)?;
        Ok(TreeNode::branch("list", children.elements))
    }

    type SetLitRet = TreeNode;
    fn visit_set_lit(
        &self,

        node: ast::AstNodeRef<ast::SetLit>,
    ) -> Result<Self::SetLitRet, Self::Error> {
        let children = walk::walk_set_lit(self, node)?;
        Ok(TreeNode::branch("set", children.elements))
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
                .chain(ty.map(|t| TreeNode::branch("type", vec![t])).into_iter())
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
        Ok(TreeNode::leaf(labelled("str", node.data, "\"")))
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

        node: ast::AstNodeRef<ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        let FloatLit { value, kind } = node.body();

        Ok(TreeNode::leaf(labelled("float", format!("{value}{kind}"), "")))
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

        node: ast::AstNodeRef<ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error> {
        let IntLit { value, kind } = node.body();

        Ok(TreeNode::leaf(labelled("int", format!("{value}{kind}"), "")))
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
        Ok(walk::walk_expr(self, node)?.kind)
    }

    type VariableExprRet = TreeNode;
    fn visit_variable_expr(
        &self,

        node: ast::AstNodeRef<ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        let walk::VariableExpr { name } = walk::walk_variable_expr(self, node)?;

        Ok(TreeNode::branch("variable", vec![TreeNode::leaf(labelled("named", name.label, "\""))]))
    }

    type DirectiveExprRet = TreeNode;
    fn visit_directive_expr(
        &self,

        node: ast::AstNodeRef<ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let walk::DirectiveExpr { subject, .. } = walk::walk_directive_expr(self, node)?;

        Ok(TreeNode::branch(labelled("directive", node.name.ident, "\""), vec![subject]))
    }

    type ConstructorCallArgRet = TreeNode;
    fn visit_constructor_call_arg(
        &self,

        node: ast::AstNodeRef<ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
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
    fn visit_access_kind(&self, node: ast::AccessKind) -> Result<Self::AccessKindRet, Self::Error> {
        match node {
            ast::AccessKind::Property => Ok(TreeNode::leaf("property")),
            ast::AccessKind::Namespace => Ok(TreeNode::leaf("namespace")),
        }
    }

    type RefExprRet = TreeNode;
    fn visit_ref_expr(
        &self,

        node: ast::AstNodeRef<ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let walk::RefExpr { inner_expr, mutability } = walk::walk_ref_expr(self, node)?;
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
        let walk::DerefExpr(inner_expr) = walk::walk_deref_expr(self, node)?;
        Ok(TreeNode::branch("deref", vec![inner_expr]))
    }

    type UnsafeExprRet = TreeNode;
    fn visit_unsafe_expr(
        &self,

        node: ast::AstNodeRef<ast::UnsafeExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::UnsafeExpr(inner_expr) = walk::walk_unsafe_expr(self, node)?;
        Ok(TreeNode::branch("unsafe", vec![inner_expr]))
    }

    type LitExprRet = TreeNode;
    fn visit_lit_expr(
        &self,

        node: ast::AstNodeRef<ast::LitExpr>,
    ) -> Result<Self::LitExprRet, Self::Error> {
        let walk::LitExpr(lit) = walk::walk_lit_expr(self, node)?;
        Ok(lit)
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
        let walk::TyExpr(ty) = walk::walk_ty_expr(self, node)?;

        Ok(TreeNode::branch("type_expr", vec![ty]))
    }

    type BlockExprRet = TreeNode;
    fn visit_block_expr(
        &self,

        node: ast::AstNodeRef<ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        Ok(walk::walk_block_expr(self, node)?.0)
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
        Ok(walk::walk_import_expr(self, node)?.0)
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

        Ok(TreeNode::branch("tuple", entries))
    }

    type ListTyRet = TreeNode;
    fn visit_list_ty(
        &self,

        node: ast::AstNodeRef<ast::ListTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        let walk::ListTy { inner } = walk::walk_list_ty(self, node)?;

        Ok(TreeNode::branch("list", vec![inner]))
    }

    type SetTyRet = TreeNode;
    fn visit_set_ty(
        &self,

        node: ast::AstNodeRef<ast::SetTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        let walk::SetTy { inner: key } = walk::walk_set_ty(self, node)?;

        Ok(TreeNode::branch("set", vec![key]))
    }

    type MapTyRet = TreeNode;
    fn visit_map_ty(
        &self,

        node: ast::AstNodeRef<ast::MapTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        let walk::MapTy { key, value } = walk::walk_map_ty(self, node)?;

        Ok(TreeNode::branch(
            "map",
            vec![TreeNode::branch("key", vec![key]), TreeNode::branch("key", vec![value])],
        ))
    }

    type TyArgRet = TreeNode;
    fn visit_ty_arg(
        &self,

        node: ast::AstNodeRef<ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        let walk::TyArg { name, ty } = walk::walk_ty_arg(self, node)?;

        if let Some(name) = name {
            Ok(TreeNode::branch(
                "field",
                vec![TreeNode::branch("name", vec![name]), TreeNode::branch("type", vec![ty])],
            ))
        } else {
            Ok(ty)
        }
    }

    type FnTyRet = TreeNode;
    fn visit_fn_ty(&self, node: ast::AstNodeRef<ast::FnTy>) -> Result<Self::FnTyRet, Self::Error> {
        let walk::FnTy { params, return_ty } = walk::walk_fn_ty(self, node)?;

        let return_child = TreeNode::branch("return", vec![return_ty]);

        let children = {
            if params.is_empty() {
                vec![return_child]
            } else {
                vec![TreeNode::branch("parameters", params), return_child]
            }
        };

        Ok(TreeNode::branch("function", children))
    }

    type TyFnRet = TreeNode;
    fn visit_ty_fn(&self, node: ast::AstNodeRef<ast::TyFn>) -> Result<Self::TyFnRet, Self::Error> {
        let walk::TyFn { params, return_ty } = walk::walk_ty_fn(self, node)?;

        let mut children = vec![TreeNode::branch("return", vec![return_ty])];

        // Add the parameters branch to the start
        if !params.is_empty() {
            children.insert(0, TreeNode::branch("parameters", params));
        }

        Ok(TreeNode::branch("type_function", children))
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

    type TyFnDefRet = TreeNode;
    fn visit_ty_fn_def(
        &self,

        node: ast::AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let walk::TyFnDef { params: args, return_ty, body } = walk::walk_ty_fn_def(self, node)?;

        Ok(TreeNode::branch(
            "type_function",
            iter::once(TreeNode::branch("args", args))
                .chain(return_ty.map(|r| TreeNode::branch("return_type", vec![r])))
                .chain(iter::once(TreeNode::branch("body", vec![body])))
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
            iter::once(TreeNode::branch("params", params))
                .chain(return_ty.map(|r| TreeNode::branch("return_type", vec![r])))
                .chain(iter::once(TreeNode::branch("body", vec![fn_body])))
                .collect(),
        ))
    }

    type ParamRet = TreeNode;
    fn visit_param(
        &self,

        node: ast::AstNodeRef<ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        let walk::Param { name, ty, default } = walk::walk_param(self, node)?;
        Ok(TreeNode::branch(
            "param",
            iter::empty()
                .chain(name.map(|t| TreeNode::branch("name", vec![t])))
                .chain(ty.map(|t| TreeNode::branch("type", vec![t])))
                .chain(default.map(|d| TreeNode::branch("default", vec![d])))
                .collect(),
        ))
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
        let walk::MatchCase { expr, pat: pattern } = walk::walk_match_case(self, node)?;
        Ok(TreeNode::branch("case", vec![pattern, TreeNode::branch("branch", vec![expr])]))
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
        let walk::LoopBlock(inner) = walk::walk_loop_block(self, node)?;
        Ok(TreeNode::branch("loop", vec![inner]))
    }

    type ForLoopBlockRet = TreeNode;
    fn visit_for_loop_block(
        &self,

        node: ast::AstNodeRef<ast::ForLoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let walk::ForLoopBlock { pat: pattern, iterator, body } =
            walk::walk_for_loop_block(self, node)?;

        Ok(TreeNode::branch("for_loop", vec![pattern, iterator, body]))
    }

    type WhileLoopBlockRet = TreeNode;
    fn visit_while_loop_block(
        &self,

        node: ast::AstNodeRef<ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        let walk::WhileLoopBlock { condition, body } = walk::walk_while_loop_block(self, node)?;

        Ok(TreeNode::branch("while_loop", vec![condition, body]))
    }

    type ModBlockRet = TreeNode;
    fn visit_mod_block(
        &self,

        node: ast::AstNodeRef<ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        let walk::ModBlock { block, ty_params } = walk::walk_mod_block(self, node)?;

        let children = {
            if ty_params.is_empty() {
                vec![block]
            } else {
                vec![TreeNode::branch("ty_params", ty_params), block]
            }
        };

        Ok(TreeNode::branch("mod", children))
    }

    type ImplBlockRet = TreeNode;
    fn visit_impl_block(
        &self,

        node: ast::AstNodeRef<ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        let walk::ImplBlock { block, ty_params } = walk::walk_impl_block(self, node)?;

        let children = {
            if ty_params.is_empty() {
                vec![block]
            } else {
                vec![TreeNode::branch("ty_params", ty_params), block]
            }
        };

        Ok(TreeNode::branch("impl", children))
    }

    type IfClauseRet = TreeNode;
    fn visit_if_clause(
        &self,

        node: ast::AstNodeRef<ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        let walk::IfClause { condition, body } = walk::walk_if_clause(self, node)?;

        Ok(TreeNode::branch(
            "clause",
            vec![
                TreeNode::branch("condition", vec![condition]),
                TreeNode::branch("body", vec![body]),
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
        let walk::ReturnStatement(inner) = walk::walk_return_statement(self, node)?;
        Ok(TreeNode::branch("return", inner.into_iter().collect()))
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
    fn visit_visibility_modifier(
        &self,

        node: ast::AstNodeRef<ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        match node.body() {
            ast::Visibility::Private => Ok(TreeNode::leaf("private")),
            ast::Visibility::Public => Ok(TreeNode::leaf("public")),
        }
    }

    type MutabilityRet = TreeNode;

    fn visit_mutability_modifier(
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

    type MergeDeclarationRet = TreeNode;
    fn visit_merge_declaration(
        &self,

        node: ast::AstNodeRef<ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        let walk::MergeDeclaration { decl: pattern, value } =
            walk::walk_merge_declaration(self, node)?;

        Ok(TreeNode::branch("merge_declaration", vec![pattern, value]))
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
        let walk::AssignOpStatement { lhs, rhs, operator } =
            walk::walk_assign_op_statement(self, node)?;
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

    type StructDefRet = TreeNode;
    fn visit_struct_def(
        &self,

        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let walk::StructDef { fields, ty_params } = walk::walk_struct_def(self, node)?;

        let children = {
            if ty_params.is_empty() {
                vec![TreeNode::branch("fields", fields)]
            } else {
                vec![TreeNode::branch("ty_params", ty_params), TreeNode::branch("fields", fields)]
            }
        };

        Ok(TreeNode::branch("struct_def", children))
    }

    type EnumDefEntryRet = TreeNode;
    fn visit_enum_def_entry(
        &self,

        node: ast::AstNodeRef<ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        let walk::EnumDefEntry { name, fields } = walk::walk_enum_def_entry(self, node)?;
        Ok(TreeNode::branch(
            labelled("variant", name.label, "\""),
            if fields.is_empty() { vec![] } else { vec![TreeNode::branch("fields", fields)] },
        ))
    }

    type EnumDefRet = TreeNode;
    fn visit_enum_def(
        &self,

        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let walk::EnumDef { entries, ty_params } = walk::walk_enum_def(self, node)?;

        let children = {
            if ty_params.is_empty() {
                vec![TreeNode::branch("variants", entries)]
            } else {
                vec![
                    TreeNode::branch("ty_params", ty_params),
                    TreeNode::branch("variants", entries),
                ]
            }
        };

        Ok(TreeNode::branch("enum_def", children))
    }

    type TraitDefRet = TreeNode;
    fn visit_trait_def(
        &self,

        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let walk::TraitDef { members } = walk::walk_trait_def(self, node)?;

        Ok(TreeNode::branch("trait_def", vec![TreeNode::branch("members", members)]))
    }

    type TraitImplRet = TreeNode;

    fn visit_trait_impl(
        &self,

        node: ast::AstNodeRef<ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let walk::TraitImpl { body, ty } = walk::walk_trait_impl(self, node)?;

        Ok(TreeNode::branch(
            "trait_impl",
            vec![TreeNode::branch("ty", vec![ty]), TreeNode::branch("body", body)],
        ))
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
        let walk::ConstructorPat { subject, args } = walk::walk_constructor_pat(self, node)?;

        let children = if !node.fields.is_empty() {
            vec![TreeNode::branch("subject", vec![subject]), TreeNode::branch("args", args)]
        } else {
            vec![TreeNode::branch("subject", vec![subject])]
        };

        Ok(TreeNode::branch("constructor", children))
    }

    type TuplePatEntryRet = TreeNode;
    fn visit_tuple_pat_entry(
        &self,

        node: ast::AstNodeRef<ast::TuplePatEntry>,
    ) -> Result<Self::TuplePatEntryRet, Self::Error> {
        let walk::TuplePatEntry { name, pat: pattern } = walk::walk_tuple_pat_entry(self, node)?;

        Ok(TreeNode::branch(
            "entry",
            name.map(|t| TreeNode::branch("name", vec![t]))
                .into_iter()
                .chain(iter::once(TreeNode::branch("pattern", vec![pattern])))
                .collect(),
        ))
    }

    type TuplePatRet = TreeNode;
    fn visit_tuple_pat(
        &self,

        node: ast::AstNodeRef<ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        let walk::TuplePat { elements } = walk::walk_tuple_pat(self, node)?;
        Ok(TreeNode::branch("tuple", elements))
    }

    type ListPatRet = TreeNode;
    fn visit_list_pat(
        &self,

        node: ast::AstNodeRef<ast::ListPat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        let walk::ListPat { elements } = walk::walk_list_pat(self, node)?;
        Ok(TreeNode::branch("list", elements))
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
        let walk::LitPat(lit) = walk::walk_lit_pat(self, node)?;
        Ok(lit)
    }

    type RangePatRet = TreeNode;
    fn visit_range_pat(
        &self,

        node: ast::AstNodeRef<ast::RangePat>,
    ) -> Result<Self::RangePatRet, Self::Error> {
        let walk::RangePat { lo, hi } = walk::walk_range_pat(self, node)?;

        Ok(TreeNode::branch(
            "range",
            vec![
                TreeNode::branch("lo", vec![lo]),
                TreeNode::branch("hi", vec![hi]),
                TreeNode::leaf(labelled("end", format!("{}", node.body().end), "`")),
            ],
        ))
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
        let walk::IfPat { condition, pat: pattern } = walk::walk_if_pat(self, node)?;
        Ok(TreeNode::branch(
            "if",
            vec![
                TreeNode::branch("condition", vec![condition]),
                TreeNode::branch("pattern", vec![pattern]),
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
        let walk::ModulePat { fields: patterns } = walk::walk_module_pat(self, node)?;
        Ok(TreeNode::branch("module", vec![TreeNode::branch("members", patterns)]))
    }

    type ModuleRet = TreeNode;

    fn visit_module(
        &self,

        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let walk::Module { contents } = walk::walk_module(self, node)?;
        Ok(TreeNode::branch("module", contents))
    }

    type ExprKindRet = TreeNode;
    fn visit_expr_kind(
        &self,
        node: ast::AstNodeRef<ast::ExprKind>,
    ) -> Result<Self::ExprKindRet, Self::Error> {
        walk::walk_expr_kind_same_children(self, node)
    }
}
