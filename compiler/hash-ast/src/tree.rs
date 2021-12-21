use std::iter;

use hash_utils::tree_writing::TreeNode;

use crate::ident::IDENTIFIER_MAP;
use crate::literal::STRING_LITERAL_MAP;
use crate::{ast, visitor::walk, visitor::AstVisitor};

struct AstTreeGenerator;

fn labeled(label: impl ToString, contents: impl ToString, quote_str: &str) -> String {
    format!(
        "{} {}{}{}",
        label.to_string(),
        quote_str,
        contents.to_string(),
        quote_str
    )
}

impl<'c> AstVisitor<'c> for AstTreeGenerator {
    type CollectionContainer<T> = Vec<T>;

    type ImportRet = TreeNode;
    fn visit_import(&mut self, node: ast::AstNodeRef<ast::Import>) -> Self::ImportRet {
        TreeNode::leaf(labeled(
            "import",
            STRING_LITERAL_MAP.lookup(node.path),
            "\"",
        ))
    }

    type NameRet = TreeNode;
    fn visit_name(&mut self, node: ast::AstNodeRef<ast::Name>) -> Self::NameRet {
        TreeNode::leaf(IDENTIFIER_MAP.ident_name(node.ident))
    }

    type AccessNameRet = TreeNode;
    fn visit_access_name(
        &mut self,
        node: ast::AstNodeRef<ast::AccessName<'c>>,
    ) -> Self::AccessNameRet {
        TreeNode::leaf(
            node.path
                .iter()
                .map(|p| IDENTIFIER_MAP.ident_name(*p))
                .intersperse("::")
                .collect::<String>(),
        )
    }

    type LiteralRet = TreeNode;
    fn visit_literal(&mut self, node: ast::AstNodeRef<ast::Literal<'c>>) -> Self::LiteralRet {
        walk::walk_literal_same_children(self, node)
    }

    type ExpressionRet = TreeNode;
    fn visit_expression(
        &mut self,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Self::ExpressionRet {
        walk::walk_expression_same_children(self, node)
    }

    type VariableExprRet = TreeNode;
    fn visit_variable_expr(
        &mut self,
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> Self::VariableExprRet {
        let walk::VariableExpr { name, type_args } = walk::walk_variable_expr(self, node);
        TreeNode::branch(
            "variable",
            vec![name, TreeNode::branch("type_args", type_args)],
        )
    }

    type IntrinsicKeyRet = TreeNode;
    fn visit_intrinsic_key(
        &mut self,
        node: ast::AstNodeRef<ast::IntrinsicKey>,
    ) -> Self::IntrinsicKeyRet {
        TreeNode::leaf(labeled(
            "intrinsic",
            IDENTIFIER_MAP.ident_name(node.name),
            "\"",
        ))
    }

    type FunctionCallArgsRet = TreeNode;
    fn visit_function_call_args(
        &mut self,
        node: ast::AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> Self::FunctionCallArgsRet {
        TreeNode::branch("args", walk::walk_function_call_args(self, node).entries)
    }

    type FunctionCallExprRet = TreeNode;
    fn visit_function_call_expr(
        &mut self,
        node: ast::AstNodeRef<ast::FunctionCallExpr<'c>>,
    ) -> Self::FunctionCallExprRet {
        let walk::FunctionCallExpr { subject, args } = walk::walk_function_call_expr(self, node);
        TreeNode::branch(
            "function_call",
            vec![TreeNode::branch("subject", vec![subject]), args],
        )
    }

    type PropertyAccessExprRet = TreeNode;
    fn visit_property_access_expr(
        &mut self,
        node: ast::AstNodeRef<ast::PropertyAccessExpr<'c>>,
    ) -> Self::PropertyAccessExprRet {
        let walk::PropertyAccessExpr { subject, property } =
            walk::walk_property_access_expr(self, node);
        TreeNode::branch(
            "property_access",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::branch("property", vec![property]),
            ],
        )
    }

    type RefExprRet = TreeNode;
    fn visit_ref_expr(&mut self, node: ast::AstNodeRef<ast::RefExpr<'c>>) -> Self::RefExprRet {
        let walk::RefExpr { inner_expr } = walk::walk_ref_expr(self, node);
        TreeNode::branch("ref", vec![inner_expr])
    }

    type DerefExprRet = TreeNode;
    fn visit_deref_expr(
        &mut self,
        node: ast::AstNodeRef<ast::DerefExpr<'c>>,
    ) -> Self::DerefExprRet {
        let walk::DerefExpr(inner_expr) = walk::walk_deref_expr(self, node);
        TreeNode::branch("deref", vec![inner_expr])
    }

    type LiteralExprRet = TreeNode;
    fn visit_literal_expr(
        &mut self,
        node: ast::AstNodeRef<ast::LiteralExpr<'c>>,
    ) -> Self::LiteralExprRet {
        let walk::LiteralExpr(literal) = walk::walk_literal_expr(self, node);
        literal
    }

    type TypedExprRet = TreeNode;
    fn visit_typed_expr(
        &mut self,
        node: ast::AstNodeRef<ast::TypedExpr<'c>>,
    ) -> Self::TypedExprRet {
        let walk::TypedExpr { ty, expr } = walk::walk_typed_expr(self, node);
        TreeNode::branch(
            "typed_expr",
            vec![
                TreeNode::branch("subject", vec![expr]),
                TreeNode::branch("type", vec![ty]),
            ],
        )
    }

    type BlockExprRet = TreeNode;
    fn visit_block_expr(
        &mut self,
        node: ast::AstNodeRef<ast::BlockExpr<'c>>,
    ) -> Self::BlockExprRet {
        walk::walk_block_expr(self, node).0
    }

    type ImportExprRet = TreeNode;
    fn visit_import_expr(
        &mut self,
        node: ast::AstNodeRef<ast::ImportExpr<'c>>,
    ) -> Self::ImportExprRet {
        walk::walk_import_expr(self, node).0
    }

    type TypeRet = TreeNode;
    fn visit_type(&mut self, node: ast::AstNodeRef<ast::Type<'c>>) -> Self::TypeRet {
        walk::walk_type_same_children(self, node)
    }

    type NamedTypeRet = TreeNode;
    fn visit_named_type(
        &mut self,
        node: ast::AstNodeRef<ast::NamedType<'c>>,
    ) -> Self::NamedTypeRet {
        let walk::NamedType { name, type_args } = walk::walk_named_type(self, node);
        let children = {
            if type_args.is_empty() {
                vec![]
            } else {
                vec![TreeNode::branch("type_args", type_args)]
            }
        };
        TreeNode::branch(labeled("name", name.label, ""), children)
    }

    type RefTypeRet = TreeNode;
    fn visit_ref_type(&mut self, node: ast::AstNodeRef<ast::RefType<'c>>) -> Self::RefTypeRet {
        let walk::RefType(inner) = walk::walk_ref_type(self, node);
        TreeNode::branch("ref", vec![inner])
    }

    type RawRefTypeRet = TreeNode;
    fn visit_raw_ref_type(
        &mut self,
        node: ast::AstNodeRef<ast::RawRefType<'c>>,
    ) -> Self::RawRefTypeRet {
        let walk::RawRefType(inner) = walk::walk_raw_ref_type(self, node);
        TreeNode::branch("raw_ref", vec![inner])
    }

    type TypeVarRet = TreeNode;
    fn visit_type_var(&mut self, node: ast::AstNodeRef<ast::TypeVar<'c>>) -> Self::TypeVarRet {
        let walk::TypeVar { name } = walk::walk_type_var(self, node);
        TreeNode::leaf(labeled("var", name.label, ""))
    }

    type ExistentialTypeRet = TreeNode;
    fn visit_existential_type(
        &mut self,
        _: ast::AstNodeRef<ast::ExistentialType>,
    ) -> Self::ExistentialTypeRet {
        TreeNode::leaf("existential")
    }

    type InferTypeRet = TreeNode;
    fn visit_infer_type(&mut self, _: ast::AstNodeRef<ast::InferType>) -> Self::InferTypeRet {
        TreeNode::leaf("infer")
    }

    type MapLiteralRet = TreeNode;
    fn visit_map_literal(
        &mut self,
        node: ast::AstNodeRef<ast::MapLiteral<'c>>,
    ) -> Self::MapLiteralRet {
        TreeNode::branch("map", walk::walk_map_literal(self, node).entries)
    }

    type MapLiteralEntryRet = TreeNode;
    fn visit_map_literal_entry(
        &mut self,
        node: ast::AstNodeRef<ast::MapLiteralEntry<'c>>,
    ) -> Self::MapLiteralEntryRet {
        let walk::MapLiteralEntry { key, value } = walk::walk_map_literal_entry(self, node);
        TreeNode::branch(
            "entry",
            vec![
                TreeNode::branch("key", vec![key]),
                TreeNode::branch("value", vec![value]),
            ],
        )
    }

    type ListLiteralRet = TreeNode;
    fn visit_list_literal(
        &mut self,
        node: ast::AstNodeRef<ast::ListLiteral<'c>>,
    ) -> Self::ListLiteralRet {
        let children = walk::walk_list_literal(self, node);
        TreeNode::branch("list", children.elements)
    }

    type SetLiteralRet = TreeNode;
    fn visit_set_literal(
        &mut self,
        node: ast::AstNodeRef<ast::SetLiteral<'c>>,
    ) -> Self::SetLiteralRet {
        let children = walk::walk_set_literal(self, node);
        TreeNode::branch("set", children.elements)
    }

    type TupleLiteralRet = TreeNode;
    fn visit_tuple_literal(
        &mut self,
        node: ast::AstNodeRef<ast::TupleLiteral<'c>>,
    ) -> Self::TupleLiteralRet {
        let children = walk::walk_tuple_literal(self, node);
        TreeNode::branch("tuple", children.elements)
    }

    type StrLiteralRet = TreeNode;
    fn visit_str_literal(&mut self, node: ast::AstNodeRef<ast::StrLiteral>) -> Self::StrLiteralRet {
        TreeNode::leaf(labeled("str", STRING_LITERAL_MAP.lookup(node.0), "\""))
    }

    type CharLiteralRet = TreeNode;
    fn visit_char_literal(
        &mut self,
        node: ast::AstNodeRef<ast::CharLiteral>,
    ) -> Self::CharLiteralRet {
        TreeNode::leaf(labeled("char", node.0, "'"))
    }

    type FloatLiteralRet = TreeNode;
    fn visit_float_literal(
        &mut self,
        node: ast::AstNodeRef<ast::FloatLiteral>,
    ) -> Self::FloatLiteralRet {
        TreeNode::leaf(labeled("float", node.0, ""))
    }

    type IntLiteralRet = TreeNode;
    fn visit_int_literal(&mut self, node: ast::AstNodeRef<ast::IntLiteral>) -> Self::IntLiteralRet {
        TreeNode::leaf(labeled("int", node.0, ""))
    }

    type StructLiteralRet = TreeNode;
    fn visit_struct_literal(
        &mut self,
        node: ast::AstNodeRef<ast::StructLiteral<'c>>,
    ) -> Self::StructLiteralRet {
        let walk::StructLiteral {
            name: _,
            type_args,
            entries,
        } = walk::walk_struct_literal(self, node);
        TreeNode::branch(
            "struct",
            vec![
                TreeNode::branch("type_args", type_args),
                TreeNode::branch("entries", entries),
            ],
        )
    }

    type StructLiteralEntryRet = TreeNode;
    fn visit_struct_literal_entry(
        &mut self,
        node: ast::AstNodeRef<ast::StructLiteralEntry<'c>>,
    ) -> Self::StructLiteralEntryRet {
        let walk::StructLiteralEntry { name, value } = walk::walk_struct_literal_entry(self, node);
        TreeNode::branch(
            "entry",
            vec![
                TreeNode::branch("name", vec![name]),
                TreeNode::branch("value", vec![value]),
            ],
        )
    }

    type FunctionDefRet = TreeNode;
    fn visit_function_def(
        &mut self,
        node: ast::AstNodeRef<ast::FunctionDef<'c>>,
    ) -> Self::FunctionDefRet {
        let walk::FunctionDef {
            args,
            fn_body,
            return_ty,
        } = walk::walk_function_def(self, node);

        TreeNode::branch(
            "function_def",
            iter::once(TreeNode::branch("args", args))
                .chain(
                    return_ty
                        .map(|r| TreeNode::branch("return_type", vec![r]))
                        .into_iter(),
                )
                .chain(iter::once(TreeNode::branch("body", vec![fn_body])))
                .collect(),
        )
    }

    type FunctionDefArgRet = TreeNode;
    fn visit_function_def_arg(
        &mut self,
        node: ast::AstNodeRef<ast::FunctionDefArg<'c>>,
    ) -> Self::FunctionDefArgRet {
        let walk::FunctionDefArg { name, ty } = walk::walk_function_def_arg(self, node);
        TreeNode::branch(
            "arg",
            iter::once(TreeNode::branch("name", vec![name]))
                .chain(ty.into_iter())
                .collect(),
        )
    }

    type BlockRet = TreeNode;
    fn visit_block(&mut self, node: ast::AstNodeRef<ast::Block<'c>>) -> Self::BlockRet {
        walk::walk_block_same_children(self, node)
    }

    type MatchCaseRet = TreeNode;
    fn visit_match_case(
        &mut self,
        node: ast::AstNodeRef<ast::MatchCase<'c>>,
    ) -> Self::MatchCaseRet {
        let walk::MatchCase { expr, pattern } = walk::walk_match_case(self, node);
        TreeNode::branch(
            "case",
            vec![pattern, TreeNode::branch("branch", vec![expr])],
        )
    }

    type MatchBlockRet = TreeNode;
    fn visit_match_block(
        &mut self,
        node: ast::AstNodeRef<ast::MatchBlock<'c>>,
    ) -> Self::MatchBlockRet {
        let walk::MatchBlock { cases, subject } = walk::walk_match_block(self, node);

        TreeNode::branch(
            "match",
            vec![
                TreeNode::branch("subject", vec![subject]),
                TreeNode::branch("cases", cases),
            ],
        )
    }

    type LoopBlockRet = TreeNode;
    fn visit_loop_block(
        &mut self,
        node: ast::AstNodeRef<ast::LoopBlock<'c>>,
    ) -> Self::LoopBlockRet {
        let walk::LoopBlock(inner) = walk::walk_loop_block(self, node);
        TreeNode::branch("loop", inner.children)
    }

    type BodyBlockRet = TreeNode;
    fn visit_body_block(
        &mut self,
        node: ast::AstNodeRef<ast::BodyBlock<'c>>,
    ) -> Self::BodyBlockRet {
        let walk::BodyBlock { statements, expr } = walk::walk_body_block(self, node);

        let mut children = Vec::new();
        if !statements.is_empty() {
            children.push(TreeNode::branch("statements", statements));
        }
        if let Some(expr) = expr {
            children.push(TreeNode::branch("expr", vec![expr]));
        }

        TreeNode::branch("body", children)
    }

    type StatementRet = TreeNode;
    fn visit_statement(&mut self, node: ast::AstNodeRef<ast::Statement<'c>>) -> Self::StatementRet {
        walk::walk_statement_same_children(self, node)
    }

    type ExprStatementRet = TreeNode;
    fn visit_expr_statement(
        &mut self,
        node: ast::AstNodeRef<ast::ExprStatement<'c>>,
    ) -> Self::ExprStatementRet {
        walk::walk_expr_statement(self, node).0
    }

    type ReturnStatementRet = TreeNode;
    fn visit_return_statement(
        &mut self,
        node: ast::AstNodeRef<ast::ReturnStatement<'c>>,
    ) -> Self::ReturnStatementRet {
        let walk::ReturnStatement(inner) = walk::walk_return_statement(self, node);
        TreeNode::branch("return", inner.into_iter().collect())
    }

    type BlockStatementRet = TreeNode;
    fn visit_block_statement(
        &mut self,
        node: ast::AstNodeRef<ast::BlockStatement<'c>>,
    ) -> Self::BlockStatementRet {
        walk::walk_block_statement(self, node).0
    }

    type BreakStatementRet = TreeNode;
    fn visit_break_statement(
        &mut self,
        _node: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Self::BreakStatementRet {
        TreeNode::leaf("break")
    }

    type ContinueStatementRet = TreeNode;
    fn visit_continue_statement(
        &mut self,
        _node: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Self::ContinueStatementRet {
        TreeNode::leaf("continue")
    }

    type LetStatementRet = TreeNode;
    fn visit_let_statement(
        &mut self,
        node: ast::AstNodeRef<ast::LetStatement<'c>>,
    ) -> Self::LetStatementRet {
        let walk::LetStatement {
            pattern,
            ty,
            bound,
            value,
        } = walk::walk_let_statement(self, node);
        TreeNode::branch(
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
        )
    }

    type AssignStatementRet = TreeNode;
    fn visit_assign_statement(
        &mut self,
        node: ast::AstNodeRef<ast::AssignStatement<'c>>,
    ) -> Self::AssignStatementRet {
        let walk::AssignStatement { lhs, rhs } = walk::walk_assign_statement(self, node);
        TreeNode::branch(
            "assign",
            vec![
                TreeNode::branch("lhs", vec![lhs]),
                TreeNode::branch("rhs", vec![rhs]),
            ],
        )
    }

    type StructDefEntryRet = TreeNode;
    fn visit_struct_def_entry(
        &mut self,
        node: ast::AstNodeRef<ast::StructDefEntry<'c>>,
    ) -> Self::StructDefEntryRet {
        let walk::StructDefEntry { name, ty, default } = walk::walk_struct_def_entry(self, node);
        TreeNode::branch(
            labeled("field", name.label, "\""),
            ty.map(|t| TreeNode::branch("type", vec![t]))
                .into_iter()
                .chain(default.map(|d| TreeNode::branch("default", vec![d])))
                .collect(),
        )
    }

    type StructDefRet = TreeNode;
    fn visit_struct_def(
        &mut self,
        node: ast::AstNodeRef<ast::StructDef<'c>>,
    ) -> Self::StructDefRet {
        let walk::StructDef {
            name: _,
            entries,
            bound,
        } = walk::walk_struct_def(self, node);
        TreeNode::branch(
            "struct_def",
            bound
                .into_iter()
                .chain(iter::once(TreeNode::branch("fields", entries)))
                .collect(),
        )
    }

    type EnumDefEntryRet = TreeNode;
    fn visit_enum_def_entry(
        &mut self,
        node: ast::AstNodeRef<ast::EnumDefEntry<'c>>,
    ) -> Self::EnumDefEntryRet {
        let walk::EnumDefEntry { name, args } = walk::walk_enum_def_entry(self, node);
        TreeNode::branch(
            labeled("variant", name.label, "\""),
            if args.is_empty() { vec![] } else { vec![TreeNode::branch("args", args)] },
        )
    }

    type EnumDefRet = TreeNode;
    fn visit_enum_def(&mut self, node: ast::AstNodeRef<ast::EnumDef<'c>>) -> Self::EnumDefRet {
        let walk::EnumDef {
            name,
            entries,
            bound,
        } = walk::walk_enum_def(self, node);
        TreeNode::branch(
            "enum_def",
            iter::once(TreeNode::leaf(labeled("name", name.label, "\"")))
                .chain(bound.into_iter())
                .chain(iter::once(TreeNode::branch("variants", entries)))
                .collect(),
        )
    }

    type TraitDefRet = TreeNode;
    fn visit_trait_def(&mut self, node: ast::AstNodeRef<ast::TraitDef<'c>>) -> Self::TraitDefRet {
        let walk::TraitDef {
            name: _,
            bound,
            trait_type,
        } = walk::walk_trait_def(self, node);
        TreeNode::branch(
            "trait_def",
            vec![bound, TreeNode::branch("type", vec![trait_type])],
        )
    }

    type PatternRet = TreeNode;
    fn visit_pattern(&mut self, node: ast::AstNodeRef<ast::Pattern<'c>>) -> Self::PatternRet {
        walk::walk_pattern_same_children(self, node)
    }

    type TraitBoundRet = TreeNode;
    fn visit_trait_bound(
        &mut self,
        node: ast::AstNodeRef<ast::TraitBound<'c>>,
    ) -> Self::TraitBoundRet {
        let walk::TraitBound { name, type_args } = walk::walk_trait_bound(self, node);
        TreeNode::branch(
            labeled("requires", name.label, "\""),
            vec![TreeNode::branch("args", type_args)],
        )
    }

    type BoundRet = TreeNode;
    fn visit_bound(&mut self, node: ast::AstNodeRef<ast::Bound<'c>>) -> Self::BoundRet {
        let walk::Bound {
            type_args,
            trait_bounds,
        } = walk::walk_bound(self, node);
        TreeNode::branch(
            "bound",
            vec![
                TreeNode::branch("vars", type_args),
                TreeNode::branch("traits", trait_bounds),
            ],
        )
    }

    type EnumPatternRet = TreeNode;
    fn visit_enum_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::EnumPattern<'c>>,
    ) -> Self::EnumPatternRet {
        let walk::EnumPattern { args, name } = walk::walk_enum_pattern(self, node);
        TreeNode::branch(
            "enum",
            iter::once(TreeNode::leaf(labeled("name", name.label, "\"")))
                .chain(
                    (if args.is_empty() { None } else { Some(TreeNode::branch("args", args)) })
                        .into_iter(),
                )
                .collect(),
        )
    }

    type StructPatternRet = TreeNode;
    fn visit_struct_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::StructPattern<'c>>,
    ) -> Self::StructPatternRet {
        let walk::StructPattern { name, entries } = walk::walk_struct_pattern(self, node);
        TreeNode::branch(
            "struct",
            iter::once(TreeNode::leaf(labeled("name", name.label, "\"")))
                .chain(
                    (if entries.is_empty() {
                        None
                    } else {
                        Some(TreeNode::branch("fields", entries))
                    })
                    .into_iter(),
                )
                .collect(),
        )
    }

    type NamespacePatternRet = TreeNode;
    fn visit_namespace_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> Self::NamespacePatternRet {
        let walk::NamespacePattern { patterns } = walk::walk_namespace_pattern(self, node);
        TreeNode::branch("namespace", vec![TreeNode::branch("members", patterns)])
    }

    type TuplePatternRet = TreeNode;
    fn visit_tuple_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Self::TuplePatternRet {
        let walk::TuplePattern { elements } = walk::walk_tuple_pattern(self, node);
        TreeNode::branch("tuple", elements)
    }

    type StrLiteralPatternRet = TreeNode;
    fn visit_str_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::StrLiteralPattern>,
    ) -> Self::StrLiteralPatternRet {
        TreeNode::leaf(labeled("str", STRING_LITERAL_MAP.lookup(node.0), "\""))
    }

    type CharLiteralPatternRet = TreeNode;
    fn visit_char_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::CharLiteralPattern>,
    ) -> Self::CharLiteralPatternRet {
        TreeNode::leaf(labeled("char", node.0, "\'"))
    }

    type IntLiteralPatternRet = TreeNode;
    fn visit_int_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::IntLiteralPattern>,
    ) -> Self::IntLiteralPatternRet {
        TreeNode::leaf(labeled("int", node.0, ""))
    }

    type FloatLiteralPatternRet = TreeNode;
    fn visit_float_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::FloatLiteralPattern>,
    ) -> Self::FloatLiteralPatternRet {
        TreeNode::leaf(labeled("float", node.0, ""))
    }

    type LiteralPatternRet = TreeNode;
    fn visit_literal_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Self::LiteralPatternRet {
        walk::walk_literal_pattern_same_children(self, node)
    }

    type OrPatternRet = TreeNode;
    fn visit_or_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::OrPattern<'c>>,
    ) -> Self::OrPatternRet {
        let walk::OrPattern { variants } = walk::walk_or_pattern(self, node);
        TreeNode::branch("or", variants)
    }

    type IfPatternRet = TreeNode;
    fn visit_if_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::IfPattern<'c>>,
    ) -> Self::IfPatternRet {
        let walk::IfPattern { condition, pattern } = walk::walk_if_pattern(self, node);
        TreeNode::branch(
            "if",
            vec![
                TreeNode::branch("condition", vec![condition]),
                TreeNode::branch("pattern", vec![pattern]),
            ],
        )
    }

    type BindingPatternRet = TreeNode;
    fn visit_binding_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::BindingPattern<'c>>,
    ) -> Self::BindingPatternRet {
        let walk::BindingPattern(name) = walk::walk_binding_pattern(self, node);
        TreeNode::leaf(labeled("binding", name.label, "\""))
    }

    type IgnorePatternRet = TreeNode;
    fn visit_ignore_pattern(
        &mut self,
        _node: ast::AstNodeRef<ast::IgnorePattern>,
    ) -> Self::IgnorePatternRet {
        TreeNode::leaf("ignore")
    }

    type DestructuringPatternRet = TreeNode;
    fn visit_destructuring_pattern(
        &mut self,
        node: ast::AstNodeRef<ast::DestructuringPattern<'c>>,
    ) -> Self::DestructuringPatternRet {
        let walk::DestructuringPattern { name, pattern } =
            walk::walk_destructuring_pattern(self, node);
        TreeNode::branch(labeled("binding", name.label, "\""), vec![pattern])
    }

    type ModuleRet = TreeNode;
    fn visit_module(&mut self, node: ast::AstNodeRef<ast::Module<'c>>) -> Self::ModuleRet {
        let walk::Module { contents } = walk::walk_module(self, node);
        TreeNode::branch("module", contents)
    }
}
