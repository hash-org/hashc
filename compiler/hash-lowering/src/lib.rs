#![feature(generic_associated_types)]
#![allow(unreachable_code, unused)] // @@Temporary

use std::convert::Infallible;

use hash_alloc::{collections::row::Row, Castle, Wall};
use hash_ast::{
    ast::{
        self, AccessName, AstNode, AstNodes, Block, BlockExpr, BodyBlock, BoolLiteral,
        BoolLiteralPattern, BreakStatement, ConstructorPattern, Expression, ExpressionKind,
        ForLoopBlock, FunctionCallArg, FunctionCallArgs, FunctionCallExpr, IfBlock, IfClause,
        IfPattern, IgnorePattern, Literal, LiteralExpr, LiteralPattern, LoopBlock, MatchBlock,
        MatchCase, MatchOrigin, Pattern, TuplePatternEntry, VariableExpr, WhileLoopBlock,
    },
    ast_nodes,
    ident::IDENTIFIER_MAP,
    visitor::{walk_mut, AstVisitorMut},
};
use hash_pipeline::sources::Sources;

pub struct AstLowering;

/// This function is used to lower all of the AST that is present within
/// the modules to be compatible with the typechecking stage. This is
/// essentially a pass that will transform the following structures
/// into a "simpler" variant:
///
///     - Any for-loops are transformed into a more simpler `loop` construct
///       with an inner match case that verifies that the iterator has no
///       more items that can be consumed.
///
///    - Any while-loops are also transformed into a simpler loop variant with
///      an inner match case that matches on the result of the while-loop
///      `condition` to see if it is `true` or `false`. If it is false, then
///      the loop breaks, otherwise the body of the while-loop is executed.
///
///    - Any if-statements are transformed into equivalent match cases by using
///      the `if-guard` pattern to express all of the branches in the if-statement.
///
/// This function utilised the pipeline thread pool in order to make the transformations
/// as parallel as possible. There is a queue that is queues all of the expressions within
/// each [hash_ast::ast::Module].
pub fn lower_ast_for_typechecking<'pool, 'c>(
    sources: &mut Sources,
    castle: &'c Castle,
    pool: &'pool rayon::ThreadPool,
) -> ()
where
    'c: 'pool,
{
    // Iterate over all of the modules and add the expressions
    // to the queue so it can be distributed over the threads
    pool.scope(|scope| {
        for (_, module) in sources.iter_mut_modules() {
            for expr in module.node_mut().contents.iter_mut() {
                scope.spawn(|_| {
                    AstLowering
                        .visit_expression(&(), expr.ast_ref_mut())
                        .unwrap()
                })
            }
        }
    })
}

impl AstVisitorMut for AstLowering {
    type Ctx = ();

    type CollectionContainer<T> = Vec<T>;

    fn try_collect_items<T, E, I: Iterator<Item = Result<T, E>>>(
        _: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E> {
        items.collect()
    }

    type Error = Infallible;

    type ImportRet = ();

    fn visit_import(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        Ok(())
    }

    type NameRet = ();

    fn visit_name(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        Ok(())
    }

    type AccessNameRet = ();

    fn visit_access_name(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AccessName>,
    ) -> Result<Self::AccessNameRet, Self::Error> {
        Ok(())
    }

    type LiteralRet = ();

    fn visit_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Literal>,
    ) -> Result<Self::LiteralRet, Self::Error> {
        Ok(())
    }

    type BinaryOperatorRet = ();

    fn visit_binary_operator(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinaryOperatorRet, Self::Error> {
        Ok(())
    }

    type UnaryOperatorRet = ();

    fn visit_unary_operator(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnaryOperatorRet, Self::Error> {
        Ok(())
    }

    type ExpressionRet = ();

    fn visit_expression(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Expression>,
    ) -> Result<Self::ExpressionRet, Self::Error> {
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
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        Ok(())
    }

    type FunctionCallArgRet = ();

    fn visit_function_call_arg(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FunctionCallArg>,
    ) -> Result<Self::FunctionCallArgRet, Self::Error> {
        Ok(())
    }

    type FunctionCallArgsRet = ();

    fn visit_function_call_args(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FunctionCallArgs>,
    ) -> Result<Self::FunctionCallArgsRet, Self::Error> {
        Ok(())
    }

    type FunctionCallExprRet = ();

    fn visit_function_call_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FunctionCallExpr>,
    ) -> Result<Self::FunctionCallExprRet, Self::Error> {
        Ok(())
    }

    type PropertyAccessExprRet = ();

    fn visit_property_access_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::PropertyAccessExpr>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        Ok(())
    }

    type RefExprRet = ();

    fn visit_ref_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        Ok(())
    }

    type DerefExprRet = ();

    fn visit_deref_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        Ok(())
    }

    type UnsafeExprRet = ();

    fn visit_unsafe_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        Ok(())
    }

    type LiteralExprRet = ();

    fn visit_literal_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LiteralExpr>,
    ) -> Result<Self::LiteralExprRet, Self::Error> {
        Ok(())
    }

    type CastExprRet = ();

    fn visit_cast_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        Ok(())
    }

    type TypeExprRet = ();

    fn visit_type_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TypeExpr>,
    ) -> Result<Self::TypeExprRet, Self::Error> {
        Ok(())
    }

    type BlockExprRet = ();

    fn visit_block_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
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

    type TypeRet = ();

    fn visit_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Type>,
    ) -> Result<Self::TypeRet, Self::Error> {
        Ok(())
    }

    type NamedFieldTypeRet = ();

    fn visit_named_field_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::NamedFieldTypeEntry>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error> {
        Ok(())
    }

    type FnTypeRet = ();

    fn visit_function_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FnType>,
    ) -> Result<Self::FnTypeRet, Self::Error> {
        Ok(())
    }

    type TypeFunctionParamRet = ();

    fn visit_type_function_param(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TypeFunctionParam>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error> {
        Ok(())
    }

    type TypeFunctionRet = ();

    fn visit_type_function(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TypeFunction>,
    ) -> Result<Self::TypeFunctionRet, Self::Error> {
        Ok(())
    }

    type TypeFunctionCallRet = ();

    fn visit_type_function_call(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TypeFunctionCall>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error> {
        Ok(())
    }

    type NamedTypeRet = ();

    fn visit_named_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::NamedType>,
    ) -> Result<Self::NamedTypeRet, Self::Error> {
        Ok(())
    }

    type RefTypeRet = ();

    fn visit_ref_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::RefType>,
    ) -> Result<Self::RefTypeRet, Self::Error> {
        Ok(())
    }

    type MergedTypeRet = ();

    fn visit_merged_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MergedType>,
    ) -> Result<Self::MergedTypeRet, Self::Error> {
        Ok(())
    }

    type ExistentialTypeRet = ();

    fn visit_existential_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ExistentialType>,
    ) -> Result<Self::ExistentialTypeRet, Self::Error> {
        Ok(())
    }

    type InferTypeRet = ();

    fn visit_infer_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::InferType>,
    ) -> Result<Self::InferTypeRet, Self::Error> {
        Ok(())
    }

    type MapLiteralRet = ();

    fn visit_map_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapLiteral>,
    ) -> Result<Self::MapLiteralRet, Self::Error> {
        Ok(())
    }

    type MapLiteralEntryRet = ();

    fn visit_map_literal_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapLiteralEntry>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error> {
        Ok(())
    }

    type ListLiteralRet = ();

    fn visit_list_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListLiteral>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        Ok(())
    }

    type SetLiteralRet = ();

    fn visit_set_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SetLiteral>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        Ok(())
    }

    type TupleLiteralEntryRet = ();

    fn visit_tuple_literal_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleLiteralEntry>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error> {
        Ok(())
    }

    type TupleLiteralRet = ();

    fn visit_tuple_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleLiteral>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        Ok(())
    }

    type StrLiteralRet = ();

    fn visit_str_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        Ok(())
    }

    type CharLiteralRet = ();

    fn visit_char_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error> {
        Ok(())
    }

    type FloatLiteralRet = ();

    fn visit_float_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        Ok(())
    }

    type BoolLiteralRet = ();

    fn visit_bool_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error> {
        Ok(())
    }

    type IntLiteralRet = ();

    fn visit_int_literal(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        Ok(())
    }

    type FunctionDefRet = ();

    fn visit_function_def(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FunctionDef>,
    ) -> Result<Self::FunctionDefRet, Self::Error> {
        Ok(())
    }

    type FunctionDefArgRet = ();

    fn visit_function_def_arg(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FunctionDefArg>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error> {
        Ok(())
    }

    type BlockRet = ();

    fn visit_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        Ok(())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        Ok(())
    }

    type MatchBlockRet = ();

    fn visit_match_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        Ok(())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        Ok(())
    }

    type ForLoopBlockRet = ast::Block;

    fn visit_for_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        // Get the right spans for the transformation
        let ForLoopBlock {
            pattern,
            iterator,
            body,
        } = todo!(); // *node.body();

        let for_block_span = node.span();
        let (iter_span, pat_span, body_span) = (iterator.span(), pattern.span(), body.span());

        let make_access_name = |label: &str| -> AstNode<AccessName> {
            // Create the identifier within the map...
            let ident = IDENTIFIER_MAP.create_ident(label);

            AstNode::new(
                AccessName {
                    path: ast_nodes![AstNode::new(ident, iter_span)],
                },
                iter_span,
            )
        };

        // Copy the bodies of the inner components of the for-loop by moving out the
        // brick and then re-make the node.
        // let iterator = AstNode::new(iterator.into_body().move_out(), iter_span, ctx);

        // Here want to transform the for-loop into just a loop block
        Ok(Block::Loop(LoopBlock(AstNode::new(
            Block::Match(MatchBlock {
                subject: AstNode::new(
                    Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                        subject: AstNode::new(
                            Expression::new(ExpressionKind::Variable(VariableExpr {
                                name: make_access_name("next"),
                                type_args: ast_nodes![],
                            })),
                            iter_span,
                        ),
                        args: AstNode::new(
                            FunctionCallArgs {
                                entries: ast_nodes![AstNode::new(
                                    FunctionCallArg {
                                        name: None,
                                        value: iterator,
                                    },
                                    iter_span
                                )],
                            },
                            iter_span,
                        ),
                    })),
                    for_block_span,
                ),
                cases: ast_nodes![
                    AstNode::new(
                        MatchCase {
                            pattern: AstNode::new(
                                Pattern::Constructor(ConstructorPattern {
                                    name: make_access_name("Some"),
                                    fields: ast_nodes![AstNode::new(
                                        TuplePatternEntry {
                                            name: None,
                                            pattern
                                        },
                                        pat_span
                                    )]
                                }),
                                pat_span
                            ),
                            expr: AstNode::new(
                                Expression::new(ExpressionKind::Block(BlockExpr(body))),
                                body_span
                            )
                        },
                        pat_span
                    ),
                    AstNode::new(
                        MatchCase {
                            pattern: AstNode::new(
                                Pattern::Constructor(ConstructorPattern {
                                    name: make_access_name("None",),
                                    fields: ast_nodes![],
                                },),
                                pat_span
                            ),
                            expr: AstNode::new(
                                Expression::new(ExpressionKind::Break(BreakStatement)),
                                body_span
                            ),
                        },
                        pat_span
                    ),
                ],
                origin: MatchOrigin::For,
            }),
            for_block_span,
        ))))
    }

    type WhileLoopBlockRet = Block;

    fn visit_while_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        let while_block_span = node.span();

        // Get the right spans for the transformation
        let WhileLoopBlock { condition, body } = todo!(); // *node.body();

        let (body_span, condition_span) = (body.span(), condition.span());

        Ok(Block::Loop(LoopBlock(AstNode::new(
            Block::Match(MatchBlock {
                subject: condition,
                cases: ast_nodes![
                    AstNode::new(
                        MatchCase {
                            pattern: AstNode::new(
                                Pattern::Literal(LiteralPattern::Bool(BoolLiteralPattern(true))),
                                condition_span
                            ),
                            expr: AstNode::new(
                                Expression::new(ExpressionKind::Block(BlockExpr(body))),
                                body_span
                            ),
                        },
                        condition_span
                    ),
                    AstNode::new(
                        MatchCase {
                            pattern: AstNode::new(
                                Pattern::Literal(LiteralPattern::Bool(BoolLiteralPattern(false))),
                                condition_span
                            ),
                            expr: AstNode::new(
                                Expression::new(ExpressionKind::Break(BreakStatement)),
                                condition_span
                            )
                        },
                        condition_span
                    ),
                ],
                origin: MatchOrigin::While,
            }),
            while_block_span,
        ))))
    }

    type ModBlockRet = ();

    fn visit_mod_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        Ok(())
    }

    type ImplBlockRet = ();

    fn visit_impl_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        Ok(())
    }

    type IfClauseRet = AstNode<MatchCase>;

    fn visit_if_clause(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        let branch_span = node.span();

        let IfClause { condition, body } = todo!(); // *node.body();
        let (body_span, condition_span) = (body.span(), condition.span());

        Ok(AstNode::new(
            MatchCase {
                pattern: AstNode::new(
                    Pattern::If(IfPattern {
                        pattern: AstNode::new(Pattern::Ignore(IgnorePattern), condition_span),
                        condition,
                    }),
                    branch_span,
                ),
                expr: AstNode::new(
                    Expression::new(ExpressionKind::Block(BlockExpr(body))),
                    body_span,
                ),
            },
            branch_span,
        ))
    }

    type IfBlockRet = Block;

    fn visit_if_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        let span = node.span();
        let clauses_span = node.body().clauses.span();

        // We don't case about 'clauses' because we can use the visitor to transform
        // the clauses separately
        let IfBlock { otherwise, .. } = todo!(); // *node.body();

        let walk_mut::IfBlock { mut clauses, .. } = walk_mut::walk_if_block(self, ctx, node)?;

        // Deal with the `otherwise` case, if there is no otherwise case then we can just
        // push an ignore branch and the body of the else block, otherwise it is replaces by
        // just an empty block
        let else_block = if let Some(block) = otherwise {
            let block_span = block.span();

            AstNode::new(
                MatchCase {
                    pattern: AstNode::new(Pattern::Ignore(IgnorePattern), block_span),
                    expr: AstNode::new(
                        Expression::new(ExpressionKind::Block(BlockExpr(block))),
                        block_span,
                    ),
                },
                block_span,
            )
        } else {
            AstNode::new(
                MatchCase {
                    pattern: AstNode::new(Pattern::Ignore(IgnorePattern), span),
                    expr: AstNode::new(
                        Expression::new(ExpressionKind::Block(BlockExpr(AstNode::new(
                            Block::Body(BodyBlock {
                                statements: AstNodes::empty(),
                                expr: None,
                            }),
                            span,
                        )))),
                        span,
                    ),
                },
                span,
            )
        };

        clauses.push(else_block);

        Ok(Block::Match(MatchBlock {
            subject: AstNode::new(
                Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(AstNode::new(
                    Literal::Bool(BoolLiteral(true)),
                    span,
                )))),
                span,
            ),
            cases: AstNodes::new(clauses, clauses_span),
            origin: MatchOrigin::If,
        }))
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        Ok(())
    }

    type ReturnStatementRet = ();

    fn visit_return_statement(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
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
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        Ok(())
    }

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        Ok(())
    }

    type AssignExpressionRet = ();

    fn visit_assign_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AssignExpression>,
    ) -> Result<Self::AssignExpressionRet, Self::Error> {
        Ok(())
    }

    type AssignOpExpressionRet = ();

    fn visit_assign_op_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AssignOpExpression>,
    ) -> Result<Self::AssignOpExpressionRet, Self::Error> {
        Ok(())
    }

    type BinaryExpressionRet = ();

    fn visit_binary_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BinaryExpression>,
    ) -> Result<Self::BinaryExpressionRet, Self::Error> {
        Ok(())
    }

    type UnaryExpressionRet = ();

    fn visit_unary_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnaryExpression>,
    ) -> Result<Self::UnaryExpressionRet, Self::Error> {
        Ok(())
    }

    type IndexExpressionRet = ();

    fn visit_index_expr(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IndexExpression>,
    ) -> Result<Self::IndexExpressionRet, Self::Error> {
        Ok(())
    }

    type StructDefEntryRet = ();

    fn visit_struct_def_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StructDefEntry>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        Ok(())
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
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
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        Ok(())
    }

    type PatternRet = ();

    fn visit_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Pattern>,
    ) -> Result<Self::PatternRet, Self::Error> {
        Ok(())
    }

    type TraitImplRet = ();

    fn visit_trait_impl(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        Ok(())
    }

    type TypeFunctionDefRet = ();

    fn visit_type_function_def(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TypeFunctionDef>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error> {
        Ok(())
    }

    type TypeFunctionDefArgRet = ();

    fn visit_type_function_def_arg(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TypeFunctionDefArg>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error> {
        Ok(())
    }

    type ConstructorPatternRet = ();

    fn visit_constructor_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorPattern>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error> {
        Ok(())
    }

    type NamespacePatternRet = ();

    fn visit_namespace_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::NamespacePattern>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        Ok(())
    }

    type TuplePatternEntryRet = ();

    fn visit_tuple_pattern_entry(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TuplePatternEntry>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error> {
        Ok(())
    }

    type TuplePatternRet = ();

    fn visit_tuple_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TuplePattern>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        Ok(())
    }

    type ListPatternRet = ();

    fn visit_list_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListPattern>,
    ) -> Result<Self::ListPatternRet, Self::Error> {
        Ok(())
    }

    type TupleTypeRet = ();

    fn visit_tuple_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleType>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        Ok(())
    }

    type ListTypeRet = ();

    fn visit_list_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListType>,
    ) -> Result<Self::ListTypeRet, Self::Error> {
        Ok(())
    }

    type SetTypeRet = ();

    fn visit_set_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SetType>,
    ) -> Result<Self::SetTypeRet, Self::Error> {
        Ok(())
    }

    type MapTypeRet = ();

    fn visit_map_type(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapType>,
    ) -> Result<Self::MapTypeRet, Self::Error> {
        Ok(())
    }

    type StrLiteralPatternRet = ();

    fn visit_str_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type CharLiteralPatternRet = ();

    fn visit_char_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type IntLiteralPatternRet = ();

    fn visit_int_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type FloatLiteralPatternRet = ();

    fn visit_float_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type BoolLiteralPatternRet = ();

    fn visit_bool_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error> {
        Ok(())
    }

    type LiteralPatternRet = ();

    fn visit_literal_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error> {
        Ok(())
    }

    type OrPatternRet = ();

    fn visit_or_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::OrPattern>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        Ok(())
    }

    type IfPatternRet = ();

    fn visit_if_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfPattern>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        Ok(())
    }

    type BindingPatternRet = ();

    fn visit_binding_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BindingPattern>,
    ) -> Result<Self::BindingPatternRet, Self::Error> {
        Ok(())
    }

    type SpreadPatternRet = ();

    fn visit_spread_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SpreadPattern>,
    ) -> Result<Self::SpreadPatternRet, Self::Error> {
        Ok(())
    }

    type IgnorePatternRet = ();

    fn visit_ignore_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        Ok(())
    }

    type DestructuringPatternRet = ();

    fn visit_destructuring_pattern(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::DestructuringPattern>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error> {
        Ok(())
    }

    type ModuleRet = ();

    fn visit_module(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        Ok(())
    }
}
