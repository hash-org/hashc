//! AST De-sugaring standalone function that are called from the visitor
//! implementation.
use hash_ast::ast;
use hash_reporting::macros::panic_on_span;
use hash_source::location::Span;
use hash_utils::thin_vec::{ThinVec, thin_vec};

use crate::visitor::AstDesugaring;

impl AstDesugaring {
    /// This function is responsible for converting a [ForLoopBlock] into a
    /// simpler [ast::LoopBlock]. This is not obvious from the function
    /// definition because it accepts a [ast::AstNode<ast::Block>], not
    /// specifically a [ast::ForLoopBlock]. This is because it operates by
    /// using [`ast::AstNodeRefMut::replace`] in order to convert the
    /// for-loop into a de-sugared loop.
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
    pub(crate) fn desugar_for_loop_block(&self, node: ast::Block, parent_span: Span) -> ast::Block {
        // Since this function expects it to be a for-loop block, we match it and unwrap
        let block = match node {
            ast::Block::For(body) => body,
            block => {
                panic_on_span!(parent_span, "lowering: expected for-loop, got {}", block.as_str())
            }
        };

        let ast::ForLoopBlock { pat, iterator, for_body } = block;
        let (iter_span, pat_span, body_span) = (iterator.span(), pat.span(), for_body.span());

        // Utility to create binding patterns for when de-sugaring the result of the
        // iterator.
        let make_binding_pat = |label: &str| -> ast::AstNode<ast::Pat> {
            ast::AstNode::new(
                ast::Pat::Binding(ast::BindingPat {
                    name: ast::AstNode::new(ast::Name { ident: label.into() }, iter_span),
                    visibility: None,
                    mutability: None,
                }),
                iter_span,
            )
        };

        // Convert the pattern into a constructor pattern like `Some(<pat>)`
        let pat = ast::AstNode::new(
            ast::Pat::Constructor(ast::ConstructorPat {
                subject: make_binding_pat("Some"),
                spread: None,
                fields: ast::AstNodes::new(
                    thin_vec![ast::AstNode::new(
                        ast::PatArg { name: None, pat, macros: None },
                        pat_span
                    )],
                    pat_span,
                ),
            }),
            pat_span,
        );

        // Create the match cases, one for when the iterator is `Some(_)` and the
        // other is `None` so that it should break.
        let match_cases = ast::AstNodes::new(
            thin_vec![
                ast::AstNode::new(
                    ast::MatchCase {
                        pat,
                        expr: ast::AstNode::new(
                            ast::Expr::Block(ast::BlockExpr { data: for_body }),
                            body_span
                        ),
                        macros: None
                    },
                    pat_span
                ),
                ast::AstNode::new(
                    ast::MatchCase {
                        pat: ast::AstNode::new(
                            ast::Pat::Constructor(ast::ConstructorPat {
                                subject: make_binding_pat("None"),
                                spread: None,
                                fields: ast::AstNodes::empty(pat_span),
                            },),
                            pat_span,
                        ),
                        macros: None,
                        expr: ast::AstNode::new(
                            ast::Expr::Break(ast::BreakStatement {}),
                            body_span
                        ),
                    },
                    pat_span
                )
            ],
            parent_span,
        );

        // Here want to transform the for-loop into just a loop block
        ast::Block::Loop(ast::LoopBlock {
            contents: ast::AstNode::new(
                ast::Block::Match(ast::MatchBlock {
                    subject: ast::AstNode::new(
                        ast::Expr::Call(ast::CallExpr {
                            subject: ast::AstNode::new(
                                ast::Expr::Variable(ast::VariableExpr {
                                    name: ast::AstNode::new(
                                        ast::Name { ident: "next".into() },
                                        iter_span,
                                    ),
                                }),
                                iter_span,
                            ),
                            args: ast::AstNodes::new(
                                thin_vec![ast::AstNode::new(
                                    ast::ExprArg { name: None, value: iterator, macros: None },
                                    iter_span
                                )],
                                iter_span,
                            ),
                        }),
                        body_span,
                    ),
                    cases: match_cases,
                    origin: ast::MatchOrigin::For,
                }),
                parent_span,
            ),
        })
    }

    /// This function is responsible for converting a [WhileLoopBlock] into a
    /// [ast::LoopBlock]. This is not obvious from the function definition
    /// because it accepts a [ast::AstNode<ast::Block>], not specifically a
    /// [ast::WhileLoopBlock]. This is because it operates by using
    /// [`ast::AstNodeRefMut::replace`] in order to convert the
    /// while-loop into a de-sugared loop.
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
    pub(crate) fn desugar_while_loop_block(
        &self,
        node: ast::Block,
        parent_span: Span,
    ) -> ast::Block {
        // Since this function expects it to be a for-loop block, we match it and unwrap
        let block = match node {
            ast::Block::While(body) => body,
            block => panic_on_span!(
                parent_span,
                "lowering: expected while-block, got {}",
                block.as_str()
            ),
        };

        let ast::WhileLoopBlock { condition, while_body } = block;
        let (body_span, condition_span) = (while_body.span(), condition.span());

        ast::Block::Loop(ast::LoopBlock {
            contents: ast::AstNode::new(
                ast::Block::Match(ast::MatchBlock {
                    subject: condition,
                    cases: ast::AstNodes::new(
                        thin_vec![
                            ast::AstNode::new(
                                ast::MatchCase {
                                    pat: ast::AstNode::new(
                                        ast::Pat::Lit(ast::LitPat {
                                            data: ast::AstNode::new(
                                                ast::Lit::Bool(ast::BoolLit { data: true }),
                                                condition_span
                                            )
                                        }),
                                        condition_span
                                    ),
                                    expr: ast::AstNode::new(
                                        ast::Expr::Block(ast::BlockExpr { data: while_body }),
                                        body_span
                                    ),
                                    macros: None
                                },
                                condition_span
                            ),
                            ast::AstNode::new(
                                ast::MatchCase {
                                    pat: ast::AstNode::new(
                                        ast::Pat::Lit(ast::LitPat {
                                            data: ast::AstNode::new(
                                                ast::Lit::Bool(ast::BoolLit { data: false }),
                                                condition_span
                                            )
                                        }),
                                        condition_span
                                    ),
                                    expr: ast::AstNode::new(
                                        ast::Expr::Break(ast::BreakStatement {}),
                                        condition_span
                                    ),
                                    macros: None
                                },
                                condition_span
                            )
                        ],
                        parent_span,
                    ),
                    origin: ast::MatchOrigin::While,
                }),
                parent_span,
            ),
        })
    }

    /// This function converts a [ast::AstNode<ast::IfClause>] into a
    /// [ast::AstNode<ast::MatchCase>]. This is part of the de-sugaring process
    /// for if-statements. Each branch in the if-block is converted into a
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
    /// only de-sugaring the specific [ast::IfClause] into a [ast::MatchCase].
    fn desugar_if_clause(&self, node: ast::AstNode<ast::IfClause>) -> ast::AstNode<ast::MatchCase> {
        let branch_span = node.span();

        let ast::IfClause { condition, if_body } = node.into_body();
        let (body_span, condition_span) = (if_body.span(), condition.span());

        ast::AstNode::new(
            ast::MatchCase {
                pat: ast::AstNode::new(
                    ast::Pat::If(ast::IfPat {
                        pat: ast::AstNode::new(ast::Pat::Wild(ast::WildPat {}), condition_span),
                        condition,
                    }),
                    branch_span,
                ),
                expr: ast::AstNode::new(
                    ast::Expr::Block(ast::BlockExpr { data: if_body }),
                    body_span,
                ),
                macros: None,
            },
            branch_span,
        )
    }

    /// This function is responsible for de-sugaring an if-block into a match
    /// case. This function converts a [ast::IfBlock] into a [MatchBlock]. This
    /// is not obvious from the function definition because it accepts a
    /// [ast::Block], not specifically a [ast::IfBlock]. This is because it
    /// operates by using [`ast::AstNodeRefMut::replace`] in order to
    /// convert the if-block into a match-block.
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
    /// [ast::MatchCase] by using the `if-guard` pattern with the
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
    /// ##Note: We could just add some flag on the match-case to say that when
    /// it was lowered from a if-block, it was missing an else case, and
    /// this would mean we don't always have to add it. However, this might
    /// complicate things with pattern exhaustiveness because then there
    /// would be no base case branch, thus the exhaustiveness checking would
    /// also need to know about the omitted else branch.
    pub(crate) fn desugar_if_block(&self, node: ast::Block, parent_span: Span) -> ast::Block {
        // Since this function expects it to be a for-loop block, we match it and unwrap
        let block = match node {
            ast::Block::If(body) => body,
            block => {
                panic_on_span!(parent_span, "lowering: expected if-block, got {}", block.as_str())
            }
        };

        // We don't case about 'clauses' because we can use the visitor to transform
        // the clauses separately
        let ast::IfBlock { clauses, otherwise } = block;
        let clauses_span = clauses.span();

        // Iterate over the clauses and transform them
        let mut clauses = clauses
            .nodes
            .into_iter()
            .map(|clause| self.desugar_if_clause(clause))
            .collect::<ThinVec<_>>();

        // Deal with the `otherwise` case, if there is no otherwise case then we can
        // just push an ignore branch and the body of the else block, otherwise it
        // is replaces by just an empty block
        let else_block = if let Some(block) = otherwise {
            let else_block_span = block.span();

            ast::AstNode::new(
                ast::MatchCase {
                    pat: ast::AstNode::new(ast::Pat::Wild(ast::WildPat {}), else_block_span),
                    expr: ast::AstNode::new(
                        ast::Expr::Block(ast::BlockExpr { data: block }),
                        else_block_span,
                    ),
                    macros: None,
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
            ast::AstNode::new(
                ast::MatchCase {
                    pat: ast::AstNode::new(ast::Pat::Wild(ast::WildPat {}), parent_span),
                    expr: ast::AstNode::new(
                        ast::Expr::Block(ast::BlockExpr {
                            data: ast::AstNode::new(
                                ast::Block::Body(ast::BodyBlock {
                                    statements: ast::AstNodes::empty(parent_span),
                                    expr: None,
                                }),
                                parent_span,
                            ),
                        }),
                        parent_span,
                    ),
                    macros: None,
                },
                parent_span,
            )
        };

        // In either case, we still push the the else_block branch into the match cases
        // generated from the if-clause pass.
        clauses.push(else_block);

        ast::Block::Match(ast::MatchBlock {
            subject: ast::AstNode::new(
                ast::Expr::Lit(ast::LitExpr {
                    data: ast::AstNode::new(
                        ast::Lit::Bool(ast::BoolLit { data: true }),
                        parent_span,
                    ),
                }),
                parent_span,
            ),
            cases: ast::AstNodes::new(clauses, clauses_span),
            origin: ast::MatchOrigin::If,
        })
    }
}
