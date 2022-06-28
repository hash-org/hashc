//! Hash AST lowering passes crate. This crate holds an implementation for the
//! visitor pattern on the AST in order to `lower` it to a simpler version so
//! that later stages can work on it without having to operate on similar
//! constructs and duplicating logic.
#![feature(generic_associated_types)]

use hash_ast::{
    ast::{
        AccessName, AstNode, AstNodes, Block, BlockExpr, BodyBlock, BoolLiteral,
        BoolLiteralPattern, BreakStatement, ConstructorCallArg, ConstructorCallArgs,
        ConstructorCallExpr, ConstructorPattern, Expression, ExpressionKind, ForLoopBlock, IfBlock,
        IfClause, IfPattern, IgnorePattern, Literal, LiteralExpr, LiteralPattern, LoopBlock,
        MatchBlock, MatchCase, MatchOrigin, OwnsAstNode, Pattern, TuplePatternEntry, VariableExpr,
        WhileLoopBlock,
    },
    ast_nodes,
    visitor::{walk_mut, AstVisitorMut},
};
use hash_pipeline::{sources::Sources, traits::Desugar, CompilerResult};
use hash_source::{location::Span, SourceId};
use std::{collections::HashSet, convert::Infallible};

pub struct AstDesugaring;

impl<'pool> Desugar<'pool> for AstDesugaring {
    type State = HashSet<SourceId>;

    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(HashSet::default())
    }

    /// This function is used to lower all of the AST that is present within
    /// the modules to be compatible with the typechecking stage. This is
    /// essentially a pass that will transform the following structures
    /// into a "simpler" variant:
    ///
    /// Any for-loops are transformed into a more simpler "loop" construct
    /// with an inner match case that verifies that the iterator has no
    /// more items that can be consumed.
    ///
    /// Any while-loops are also transformed into a simpler loop variant with
    /// an inner match case that matches on the result of the while-loop
    /// "condition" to see if it is "true" or "false". If it is false, then
    /// the loop breaks, otherwise the body of the while-loop is executed.
    ///
    /// Any if-statements are transformed into equivalent match cases by using
    /// the "if-guard" pattern to express all of the branches in the
    /// if-statement.
    ///
    /// This function utilised the pipeline thread pool in order to make the
    /// transformations as parallel as possible. There is a queue that is
    /// queues all of the expressions within each [hash_ast::ast::Module].
    fn desugar(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> hash_pipeline::traits::CompilerResult<()> {
        pool.scope(|scope| {
            // De-sugar the target if it isn't already de-sugared
            if !state.contains(&entry_point) {
                if let SourceId::Interactive(id) = entry_point {
                    let source = sources.get_interactive_block_mut(id);

                    AstDesugaring.visit_body_block(&(), source.node_ref_mut()).unwrap();
                }
            }

            // Iterate over all of the modules and add the expressions
            // to the queue so it can be distributed over the threads
            for (id, module) in sources.iter_mut_modules() {
                // Skip any modules that have already been de-sugared
                if state.contains(&SourceId::Module(id)) {
                    continue;
                }

                // @@Future: So here, it would be nice that the de-sugaring visitor could have a
                // context that has access to the pool so that it could just push other jobs
                // into the queue rather than only splitting the job by top-level expressions.
                // This would work by the visitor pushing expressions into the work queue
                // whenever it hits body-blocks that have a list of expressions. This would
                // definitely make this process even faster, but it might add overhead to the
                // process of adding these items to the queue. However, it might be worth
                // investigating this in the future.
                for expr in module.node_mut().contents.iter_mut() {
                    scope
                        .spawn(|_| AstDesugaring.visit_expression(&(), expr.ast_ref_mut()).unwrap())
                }
            }
        });

        // Add all of the ids into the cache
        state.insert(entry_point);
        state.extend(sources.iter_modules().map(|(id, _)| SourceId::Module(id)));

        Ok(())
    }
}

/// This function is responsible for converting a [ForLoopBlock] into a
/// simpler [LoopBlock]. This is not obvious from the function definition
/// because it accepts a [AstNode<Block>], not specifically a [ForLoopBlock].
/// This is because it operates by using [AstNode::replace] in order to convert
/// the for-loop into a de-sugared loop.
///
/// The process is as follows: de-sugaring a for-loop from:
/// ```text
/// for <pat> in <iterator> {
///     <body>
/// }
/// ```
///
/// Into:
///
/// ```text
/// loop {
///     match next(<iterator>) {
///         Some(<pat>) => <block>;
///         None        => break;
///     }
/// }
/// ```
///
/// So essentially the for-loop becomes a simple loop with a match block on the
/// given iterator since for-loops only support iterators.
fn desugar_for_loop_block(node: Block, parent_span: Span) -> Block {
    // Since this function expects it to be a for-loop block, we match it and unwrap
    let block = match node {
        Block::For(body) => body,
        block => panic!("Expected for-loop within for-loop lowering, got {}", block.as_str()),
    };

    let ForLoopBlock { pattern, iterator, body } = block;

    let (iter_span, pat_span, body_span) = (iterator.span(), pattern.span(), body.span());

    let make_access_name = |label: &str| -> AstNode<AccessName> {
        // Create the identifier within the map...
        AstNode::new(
            AccessName { path: ast_nodes![AstNode::new(label.into(), iter_span)] },
            iter_span,
        )
    };

    // Convert the pattern into a constructor pattern like `Some(<pat>)`
    let pattern = AstNode::new(
        Pattern::Constructor(ConstructorPattern {
            name: make_access_name("Some"),
            fields: ast_nodes![AstNode::new(TuplePatternEntry { name: None, pattern }, pat_span)],
        }),
        pat_span,
    );

    // Create the match cases, one for when the iterator is `Some(_)` and the
    // other is `None` so that it should break.
    let match_cases = ast_nodes![
        AstNode::new(
            MatchCase {
                pattern,
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
                        name: make_access_name("None"),
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
    ];

    // Here want to transform the for-loop into just a loop block
    Block::Loop(LoopBlock(AstNode::new(
        Block::Match(MatchBlock {
            subject: AstNode::new(
                Expression::new(ExpressionKind::ConstructorCall(ConstructorCallExpr {
                    subject: AstNode::new(
                        Expression::new(ExpressionKind::Variable(VariableExpr {
                            name: make_access_name("next"),
                            type_args: ast_nodes![],
                        })),
                        iter_span,
                    ),
                    args: AstNode::new(
                        ConstructorCallArgs {
                            entries: ast_nodes![AstNode::new(
                                ConstructorCallArg { name: None, value: iterator },
                                iter_span
                            )],
                        },
                        parent_span,
                    ),
                })),
                body_span,
            ),
            cases: match_cases,
            origin: MatchOrigin::For,
        }),
        parent_span,
    )))
}

/// This function is responsible for converting a [WhileLoopBlock] into a
/// [LoopBlock]. This is not obvious from the function definition
/// because it accepts a [AstNode<Block>], not specifically a [WhileLoopBlock].
/// This is because it operates by using [AstNode::replace] in order to convert
/// the while-loop into a de-sugared loop.
///
/// The process is as follows: de-sugaring a for-loop from:
/// ```text
/// while <condition> {
///      <block>
/// }
/// ```
///
/// Is converted to:
///
/// ```text
/// loop {
///     match <condition> {
///         true  => <block>;
///         false => break;
///     }
/// }
/// ```
///
/// The de-sugaring process is similar to the for-loop de-sugaring
/// process. The condition that is specified for the while-loop to continue
/// executing is treated like a matchable pattern, and then matched on whether
/// if it is true or not. If it is true, the body block is executed, otherwise
/// the loop breaks.
fn desugar_while_loop_block(node: Block, parent_span: Span) -> Block {
    // Since this function expects it to be a for-loop block, we match it and unwrap
    let block = match node {
        Block::While(body) => body,
        block => panic!("Expected while-block within while-block lowering, got {}", block.as_str()),
    };

    let WhileLoopBlock { condition, body } = block;
    let (body_span, condition_span) = (body.span(), condition.span());

    Block::Loop(LoopBlock(AstNode::new(
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
        parent_span,
    )))
}

/// This function converts a [AstNode<IfClause>] into a [AstNode<MatchCase>].
/// This is part of the de-sugaring process for if-statements. Each branch in
/// the if-block is converted into a branch within a match block using the
/// `if-guard` pattern.
///
/// For example, take the branch:
///
/// ```text
/// if <condition> { <body> }
/// ```
///
/// This is converted into the following match case:
///
/// ```text
/// // match true {
///     _ if <condition> => <body>;
///     ...
/// // }
/// ```
///
/// This function is not responsible for generating the match block, but only
/// de-sugaring the specific [IfClause] into a [MatchCase].
fn desugar_if_clause(node: AstNode<IfClause>) -> AstNode<MatchCase> {
    let branch_span = node.span();

    let IfClause { condition, body } = node.into_body();
    let (body_span, condition_span) = (body.span(), condition.span());

    AstNode::new(
        MatchCase {
            pattern: AstNode::new(
                Pattern::If(IfPattern {
                    pattern: AstNode::new(Pattern::Ignore(IgnorePattern), condition_span),
                    condition,
                }),
                branch_span,
            ),
            expr: AstNode::new(Expression::new(ExpressionKind::Block(BlockExpr(body))), body_span),
        },
        branch_span,
    )
}

/// This function is responsible for de-sugaring an if-block into a match case.
/// This function converts a [IfBlock] into a [MatchBlock]. This is not obvious
/// from the function definition because it accepts a [Block], not specifically
/// a [IfBlock]. This is because it operates by using [AstNode<T>::replace] in
/// order to convert the if-block into a match-block.
///
/// The de-sugaring process is as follows, take the following if block:
///
/// ```text
/// if a { a_branch } else if b { b_branch } else { c_branch }
/// ```
///
/// will be transformed into...
///
/// ```text
/// match true {
///     _ if a => a_branch
///     _ if b => b_branch
///     _ => c_branch
/// }
/// ```
///
/// The condition of the if-branch is converted into a
/// [hash_ast::ast::MatchCase] by using the `if-guard` pattern with the
/// condition being the guard. As can be seen in the example, the condition that
/// the match-block is matching is `true`. This is essentially a filler for
/// the de-sugaring process and will be optimised out. This process is done so
/// that the later stages of the compiler don't need to deal with multiple
/// constructs that resemble each other in functionality. An if-block is
/// de-sugared into a match-block because it captures all of the features of an
/// if-block, but the relationship is not mutual and thus converting to a
/// match-block is the only case.
///
/// In the event that there is no `else` branch, this function will add a
/// default branch that adds a default branch with an empty block like so:
///
/// ```text
/// if x == 3 { <body> }
/// ```
///
/// Transforms to the following:
///
/// ```text
/// match true {
///     _ if x == 3 { <body> };
///     _ => {};
/// }
/// ```
///
/// This is done so that the typechecker can perform that the whole block
/// returns the same type. If the previous branches do not return anything,
/// omitting an `else` case is ok and this will pass later stages,however
/// when an if block returns something from a previous branch, then this will
/// fail compilation and it will be reported.
///
/// @@Note: We could just add some flag on the match-case to say that when it
/// was lowered from a if-block, it was missing an else case, and this would
/// mean we don't always have to add it. However, this might complicate things
/// with pattern exhaustiveness because then there would be no base case branch,
/// thus the exhaustiveness checking would also need to know about the omitted
/// else branch.
fn desugar_if_block(node: Block, parent_span: Span) -> Block {
    // Since this function expects it to be a for-loop block, we match it and unwrap
    let block = match node {
        Block::If(body) => body,
        block => panic!("Expected if-block within if-block lowering, got {}", block.as_str()),
    };

    // We don't case about 'clauses' because we can use the visitor to transform
    // the clauses separately
    let IfBlock { clauses, otherwise } = block;
    let clauses_span = clauses.span();

    // Iterate over the clauses and transform them
    let mut clauses = clauses.nodes.into_iter().map(desugar_if_clause).collect::<Vec<_>>();

    // Deal with the `otherwise` case, if there is no otherwise case then we can
    // just push an ignore branch and the body of the else block, otherwise it
    // is replaces by just an empty block
    let else_block = if let Some(block) = otherwise {
        let else_block_span = block.span();

        AstNode::new(
            MatchCase {
                pattern: AstNode::new(Pattern::Ignore(IgnorePattern), else_block_span),
                expr: AstNode::new(
                    Expression::new(ExpressionKind::Block(BlockExpr(block))),
                    else_block_span,
                ),
            },
            else_block_span,
        )
    } else {
        // @@Hack: We don't have a span for the branch, so we rely on using the span of
        // the entire if-clause. This might not be the exactly right approach because
        // some later checks (within typechecking) might report errors that are related
        // to a missing else-branch because the return type of the block doesn't become
        // the same anymore. Therefore, we might later want to re-think which span we
        // use for generating the else-branch.
        AstNode::new(
            MatchCase {
                pattern: AstNode::new(Pattern::Ignore(IgnorePattern), parent_span),
                expr: AstNode::new(
                    Expression::new(ExpressionKind::Block(BlockExpr(AstNode::new(
                        Block::Body(BodyBlock { statements: AstNodes::empty(), expr: None }),
                        parent_span,
                    )))),
                    parent_span,
                ),
            },
            parent_span,
        )
    };

    // In either case, we still push the the else_block branch into the match cases
    // generated from the if-clause pass.
    clauses.push(else_block);

    Block::Match(MatchBlock {
        subject: AstNode::new(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(AstNode::new(
                Literal::Bool(BoolLiteral(true)),
                parent_span,
            )))),
            parent_span,
        ),
        cases: AstNodes::new(clauses, clauses_span),
        origin: MatchOrigin::If,
    })
}

impl AstVisitorMut for AstDesugaring {
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Expression>,
    ) -> Result<Self::ExpressionRet, Self::Error> {
        let _ = walk_mut::walk_expression(self, ctx, node);
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let _ = walk_mut::walk_directive_expr(self, ctx, node);
        Ok(())
    }

    type ConstructorCallArgRet = ();

    fn visit_constructor_call_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
        let _ = walk_mut::walk_constructor_call_arg(self, ctx, node);
        Ok(())
    }

    type ConstructorCallArgsRet = ();

    fn visit_constructor_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorCallArgs>,
    ) -> Result<Self::ConstructorCallArgsRet, Self::Error> {
        let _ = walk_mut::walk_constructor_call_args(self, ctx, node);
        Ok(())
    }

    type ConstructorCallExprRet = ();

    fn visit_constructor_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        let _ = walk_mut::walk_constructor_call_expr(self, ctx, node);
        Ok(())
    }

    type PropertyAccessExprRet = ();

    fn visit_property_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::PropertyAccessExpr>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        let _ = walk_mut::walk_property_access_expr(self, ctx, node);
        Ok(())
    }

    type RefExprRet = ();

    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let _ = walk_mut::walk_ref_expr(self, ctx, node);
        Ok(())
    }

    type DerefExprRet = ();

    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let _ = walk_mut::walk_deref_expr(self, ctx, node);
        Ok(())
    }

    type UnsafeExprRet = ();

    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        let _ = walk_mut::walk_unsafe_expr(self, ctx, node);
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let _ = walk_mut::walk_cast_expr(self, ctx, node);
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

    #[inline]
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        let _ = walk_mut::walk_block_expr(self, ctx, node)?;

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

    type MapLiteralRet = ();

    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapLiteral>,
    ) -> Result<Self::MapLiteralRet, Self::Error> {
        let _ = walk_mut::walk_map_literal(self, ctx, node);
        Ok(())
    }

    type MapLiteralEntryRet = ();

    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MapLiteralEntry>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error> {
        let _ = walk_mut::walk_map_literal_entry(self, ctx, node);
        Ok(())
    }

    type ListLiteralRet = ();

    fn visit_list_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ListLiteral>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        let _ = walk_mut::walk_list_literal(self, ctx, node);
        Ok(())
    }

    type SetLiteralRet = ();

    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::SetLiteral>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        let _ = walk_mut::walk_set_literal(self, ctx, node);
        Ok(())
    }

    type TupleLiteralEntryRet = ();

    fn visit_tuple_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleLiteralEntry>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error> {
        let _ = walk_mut::walk_tuple_literal_entry(self, ctx, node);
        Ok(())
    }

    type TupleLiteralRet = ();

    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TupleLiteral>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        let _ = walk_mut::walk_tuple_literal(self, ctx, node);
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FunctionDef>,
    ) -> Result<Self::FunctionDefRet, Self::Error> {
        let _ = walk_mut::walk_function_def(self, ctx, node);
        Ok(())
    }

    type FunctionDefParamRet = ();

    fn visit_function_def_param(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::FunctionDefParam>,
    ) -> Result<Self::FunctionDefParamRet, Self::Error> {
        let _ = walk_mut::walk_function_def_param(self, ctx, node);
        Ok(())
    }

    type BlockRet = ();

    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        mut node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        let parent_span = node.span();

        // Check if this is a for, while, or if block and then apply the appropriate
        // transformations.
        match node.body() {
            Block::For(_) => {
                node.replace(|old| desugar_for_loop_block(old, parent_span));
            }
            Block::While(_) => {
                node.replace(|old| desugar_while_loop_block(old, parent_span));
            }
            Block::If(_) => {
                node.replace(|old| desugar_if_block(old, parent_span));
            }
            _ => {}
        };

        // We still need to walk the block now
        let _ = walk_mut::walk_block(self, ctx, node);

        Ok(())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let _ = walk_mut::walk_match_case(self, ctx, node);
        Ok(())
    }

    type MatchBlockRet = ();

    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let _ = walk_mut::walk_match_block(self, ctx, node);
        Ok(())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let _ = walk_mut::walk_loop_block(self, ctx, node);

        Ok(())
    }

    type ForLoopBlockRet = ();

    fn visit_for_loop_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type WhileLoopBlockRet = ();

    fn visit_while_loop_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type IfClauseRet = ();

    fn visit_if_clause(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type IfBlockRet = ();

    fn visit_if_block(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        // Specifically left empty since this should never fire!
        Ok(())
    }

    type ModBlockRet = ();

    fn visit_mod_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        let _ = walk_mut::walk_mod_block(self, ctx, node);
        Ok(())
    }

    type ImplBlockRet = ();

    fn visit_impl_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        let _ = walk_mut::walk_impl_block(self, ctx, node);
        Ok(())
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let _ = walk_mut::walk_body_block(self, ctx, node);
        Ok(())
    }

    type ReturnStatementRet = ();

    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let _ = walk_mut::walk_return_statement(self, ctx, node);
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let _ = walk_mut::walk_declaration(self, ctx, node);
        Ok(())
    }

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        // @@Note: We probably don't have to walk this??
        let _ = walk_mut::walk_merge_declaration(self, ctx, node);
        Ok(())
    }

    type AssignExpressionRet = ();

    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AssignExpression>,
    ) -> Result<Self::AssignExpressionRet, Self::Error> {
        let _ = walk_mut::walk_assign_statement(self, ctx, node);
        Ok(())
    }

    type AssignOpExpressionRet = ();

    fn visit_assign_op_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::AssignOpExpression>,
    ) -> Result<Self::AssignOpExpressionRet, Self::Error> {
        let _ = walk_mut::walk_assign_op_statement(self, ctx, node);
        Ok(())
    }

    type BinaryExpressionRet = ();

    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::BinaryExpression>,
    ) -> Result<Self::BinaryExpressionRet, Self::Error> {
        let _ = walk_mut::walk_binary_expr(self, ctx, node);
        Ok(())
    }

    type UnaryExpressionRet = ();

    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::UnaryExpression>,
    ) -> Result<Self::UnaryExpressionRet, Self::Error> {
        let _ = walk_mut::walk_unary_expr(self, ctx, node);
        Ok(())
    }

    type IndexExpressionRet = ();

    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IndexExpression>,
    ) -> Result<Self::IndexExpressionRet, Self::Error> {
        let _ = walk_mut::walk_index_expr(self, ctx, node);
        Ok(())
    }

    type StructDefEntryRet = ();

    fn visit_struct_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StructDefEntry>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        let _ = walk_mut::walk_struct_def_entry(self, ctx, node);
        Ok(())
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let _ = walk_mut::walk_struct_def(self, ctx, node);
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let _ = walk_mut::walk_trait_def(self, ctx, node);
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let _ = walk_mut::walk_trait_impl(self, ctx, node);
        Ok(())
    }

    type TypeFunctionDefRet = ();

    fn visit_type_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TypeFunctionDef>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error> {
        let _ = walk_mut::walk_type_function_def(self, ctx, node);
        Ok(())
    }

    type TypeFunctionDefArgRet = ();

    fn visit_type_function_def_param(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRefMut<hash_ast::ast::TypeFunctionDefParam>,
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::IfPattern>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        let _ = walk_mut::walk_if_pattern(self, ctx, node);
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
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let _ = walk_mut::walk_module(self, ctx, node);
        Ok(())
    }
}
