//! AST De-sugaring standalone function that are called from the visitor
//! implementation.
use hash_ast::{
    ast::{
        AstNode, AstNodes, Block, BlockExpr, BodyBlock, BoolLit, BoolLitPat, BreakStatement,
        ConstructorCallArg, ConstructorCallArgs, ConstructorCallExpr, ConstructorPat, Expr,
        ExprKind, ForLoopBlock, IfBlock, IfClause, IfPat, IgnorePat, Lit, LitExpr, LitPat,
        LoopBlock, MatchBlock, MatchCase, MatchOrigin, Name, Pat, TuplePatEntry, VariableExpr,
        WhileLoopBlock,
    },
    ast_nodes,
};
use hash_reporting::macros::panic_on_span;
use hash_source::location::Span;

use crate::visitor::AstDesugaring;

impl<'s> AstDesugaring<'s> {
    /// This function is responsible for converting a [ForLoopBlock] into a
    /// simpler [LoopBlock]. This is not obvious from the function definition
    /// because it accepts a [AstNode<Block>], not specifically a
    /// [ForLoopBlock]. This is because it operates by using
    /// [AstNode::replace] in order to convert the for-loop into a
    /// de-sugared loop.
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
    /// So essentially the for-loop becomes a simple loop with a match block on
    /// the given iterator since for-loops only support iterators.
    pub(crate) fn desugar_for_loop_block(&self, node: Block, parent_span: Span) -> Block {
        // Since this function expects it to be a for-loop block, we match it and unwrap
        let block = match node {
            Block::For(body) => body,
            block => panic_on_span!(
                self.source_location(parent_span),
                self.source_map,
                "Expected for-loop within for-loop lowering, got {}",
                block.as_str()
            ),
        };

        let ForLoopBlock { pat, iterator, body } = block;

        let (iter_span, pat_span, body_span) = (iterator.span(), pat.span(), body.span());

        let make_access_pat = |_label: &str| -> AstNode<Pat> {
            // // Create the identifier within the map...
            // AstNode::new(
            //     Namespace { path: ast_nodes![AstNode::new(label.into(), iter_span)] },
            //     iter_span,
            // )
            todo!()
        };

        // Convert the pattern into a constructor pattern like `Some(<pat>)`
        let pat = AstNode::new(
            Pat::Constructor(ConstructorPat {
                subject: make_access_pat("Some"),
                fields: ast_nodes![AstNode::new(TuplePatEntry { name: None, pat }, pat_span)],
            }),
            pat_span,
        );

        // Create the match cases, one for when the iterator is `Some(_)` and the
        // other is `None` so that it should break.
        let match_cases = ast_nodes![
            AstNode::new(
                MatchCase {
                    pat,
                    expr: AstNode::new(Expr::new(ExprKind::Block(BlockExpr(body))), body_span)
                },
                pat_span
            ),
            AstNode::new(
                MatchCase {
                    pat: AstNode::new(
                        Pat::Constructor(ConstructorPat {
                            subject: make_access_pat("None"),
                            fields: ast_nodes![],
                        },),
                        pat_span
                    ),
                    expr: AstNode::new(Expr::new(ExprKind::Break(BreakStatement)), body_span),
                },
                pat_span
            ),
        ];

        // Here want to transform the for-loop into just a loop block
        Block::Loop(LoopBlock(AstNode::new(
            Block::Match(MatchBlock {
                subject: AstNode::new(
                    Expr::new(ExprKind::ConstructorCall(ConstructorCallExpr {
                        subject: AstNode::new(
                            Expr::new(ExprKind::Variable(VariableExpr {
                                name: AstNode::new(Name { ident: "next".into() }, iter_span),
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
    /// because it accepts a [AstNode<Block>], not specifically a
    /// [WhileLoopBlock]. This is because it operates by using
    /// [AstNode::replace] in order to convert the while-loop into a
    /// de-sugared loop.
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
    /// executing is treated like a matchable pattern, and then matched on
    /// whether if it is true or not. If it is true, the body block is
    /// executed, otherwise the loop breaks.
    pub(crate) fn desugar_while_loop_block(&self, node: Block, parent_span: Span) -> Block {
        // Since this function expects it to be a for-loop block, we match it and unwrap
        let block = match node {
            Block::While(body) => body,
            block => panic_on_span!(
                self.source_location(parent_span),
                self.source_map,
                "Expected while-block within while-block lowering, got {}",
                block.as_str()
            ),
        };

        let WhileLoopBlock { condition, body } = block;
        let (body_span, condition_span) = (body.span(), condition.span());

        Block::Loop(LoopBlock(AstNode::new(
            Block::Match(MatchBlock {
                subject: condition,
                cases: ast_nodes![
                    AstNode::new(
                        MatchCase {
                            pat: AstNode::new(
                                Pat::Lit(LitPat::Bool(BoolLitPat(true))),
                                condition_span
                            ),
                            expr: AstNode::new(
                                Expr::new(ExprKind::Block(BlockExpr(body))),
                                body_span
                            ),
                        },
                        condition_span
                    ),
                    AstNode::new(
                        MatchCase {
                            pat: AstNode::new(
                                Pat::Lit(LitPat::Bool(BoolLitPat(false))),
                                condition_span
                            ),
                            expr: AstNode::new(
                                Expr::new(ExprKind::Break(BreakStatement)),
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

    /// This function converts a [AstNode<IfClause>] into a
    /// [AstNode<MatchCase>]. This is part of the de-sugaring process for
    /// if-statements. Each branch in the if-block is converted into a
    /// branch within a match block using the `if-guard` pattern.
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
    /// This function is not responsible for generating the match block, but
    /// only de-sugaring the specific [IfClause] into a [MatchCase].
    fn desugar_if_clause(&self, node: AstNode<IfClause>) -> AstNode<MatchCase> {
        let branch_span = node.span();

        let IfClause { condition, body } = node.into_body();
        let (body_span, condition_span) = (body.span(), condition.span());

        AstNode::new(
            MatchCase {
                pat: AstNode::new(
                    Pat::If(IfPat {
                        pat: AstNode::new(Pat::Ignore(IgnorePat), condition_span),
                        condition,
                    }),
                    branch_span,
                ),
                expr: AstNode::new(Expr::new(ExprKind::Block(BlockExpr(body))), body_span),
            },
            branch_span,
        )
    }

    /// This function is responsible for de-sugaring an if-block into a match
    /// case. This function converts a [IfBlock] into a [MatchBlock]. This
    /// is not obvious from the function definition because it accepts a
    /// [Block], not specifically a [IfBlock]. This is because it operates
    /// by using [AstNode<T>::replace] in order to convert the if-block into
    /// a match-block.
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
    /// condition being the guard. As can be seen in the example, the condition
    /// that the match-block is matching is `true`. This is essentially a
    /// filler for the de-sugaring process and will be optimised out. This
    /// process is done so that the later stages of the compiler don't need
    /// to deal with multiple constructs that resemble each other in
    /// functionality. An if-block is de-sugared into a match-block because
    /// it captures all of the features of an if-block, but the relationship
    /// is not mutual and thus converting to a match-block is the only case.
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
    /// when an if block returns something from a previous branch, then this
    /// will fail compilation and it will be reported.
    ///
    /// @@Note: We could just add some flag on the match-case to say that when
    /// it was lowered from a if-block, it was missing an else case, and
    /// this would mean we don't always have to add it. However, this might
    /// complicate things with pattern exhaustiveness because then there
    /// would be no base case branch, thus the exhaustiveness checking would
    /// also need to know about the omitted else branch.
    pub(crate) fn desugar_if_block(&self, node: Block, parent_span: Span) -> Block {
        // Since this function expects it to be a for-loop block, we match it and unwrap
        let block = match node {
            Block::If(body) => body,
            block => panic_on_span!(
                self.source_location(parent_span),
                self.source_map,
                "Expected if-block within if-block lowering, got {}",
                block.as_str()
            ),
        };

        // We don't case about 'clauses' because we can use the visitor to transform
        // the clauses separately
        let IfBlock { clauses, otherwise } = block;
        let clauses_span = clauses.span();

        // Iterate over the clauses and transform them
        let mut clauses = clauses
            .nodes
            .into_iter()
            .map(|clause| self.desugar_if_clause(clause))
            .collect::<Vec<_>>();

        // Deal with the `otherwise` case, if there is no otherwise case then we can
        // just push an ignore branch and the body of the else block, otherwise it
        // is replaces by just an empty block
        let else_block = if let Some(block) = otherwise {
            let else_block_span = block.span();

            AstNode::new(
                MatchCase {
                    pat: AstNode::new(Pat::Ignore(IgnorePat), else_block_span),
                    expr: AstNode::new(
                        Expr::new(ExprKind::Block(BlockExpr(block))),
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
                    pat: AstNode::new(Pat::Ignore(IgnorePat), parent_span),
                    expr: AstNode::new(
                        Expr::new(ExprKind::Block(BlockExpr(AstNode::new(
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
                Expr::new(ExprKind::LitExpr(LitExpr(AstNode::new(
                    Lit::Bool(BoolLit(true)),
                    parent_span,
                )))),
                parent_span,
            ),
            cases: AstNodes::new(clauses, clauses_span),
            origin: MatchOrigin::If,
        })
    }
}
