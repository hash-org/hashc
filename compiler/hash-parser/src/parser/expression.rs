//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use std::{path::PathBuf, str::FromStr};

use hash_alloc::{collections::row::Row, row};
use hash_ast::{
    ast::*,
    ast_nodes,
    literal::STRING_LITERAL_MAP,
    operator::{Operator, OperatorKind},
};
use hash_source::location::Location;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Parse a top level [Expression] that are terminated with a semi-colon.
    pub fn parse_top_level_expression(
        &self,
        semi_required: bool,
    ) -> AstGenResult<'c, (bool, AstNode<'c, Expression<'c>>)> {
        let offset = self.offset();
        let start = self.current_location();

        let decl =
            if let Some(pat) = self.peek_resultant_fn(|| self.parse_singular_pattern()) {
                // Check if there is a colon here and if not we have to backtrack and
                // now attempt to parse a simple expression

                match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Colon) => {
                        let decl = self.parse_declaration(pat)?;

                        Some(self.node_with_span(
                            Expression::new(ExpressionKind::Declaration(decl)),
                            start,
                        ))
                    }
                    _ => {
                        self.offset.set(offset);
                        None
                    }
                }
            } else {
                None
            };

        let expr = match decl {
            Some(statement) => Ok(statement),
            None => {
                let (expr, re_assigned) = self.try_parse_expression_with_re_assignment()?;

                if re_assigned {
                    Ok(expr)
                } else {
                    match self.peek() {
                        // We don't skip here because it is handled after the statement has been generated.
                        Some(token) if token.has_kind(TokenKind::Semi) => Ok(expr),
                        Some(token) if token.has_kind(TokenKind::Eq) => {
                            self.skip_token();

                            // Parse the right hand-side of the assignment
                            let rhs = self.parse_expression_with_precedence(0)?;

                            Ok(self.node_with_joined_span(
                                Expression::new(ExpressionKind::Assign(AssignExpression {
                                    lhs: expr,
                                    rhs,
                                })),
                                &start,
                            ))
                        }
                        Some(token) => {
                            self.error(AstGenErrorKind::ExpectedExpression, None, Some(token.kind))
                        }
                        // Special case where there is a expression at the end of the stream and therefore it
                        // is signifying that it is returning the expression value here
                        None => Ok(expr),
                    }
                }
            }
        }?;

        // Depending on whether it's expected of the expression to have a semi-colon, we
        // try and parse one anyway, if so
        let has_semi = if semi_required {
            self.parse_token(TokenKind::Semi)?;
            true
        } else {
            self.parse_token_fast(TokenKind::Semi).is_some()
        };

        Ok((has_semi, expr))
    }

    /// Parse an expression which can be compound.
    pub(crate) fn parse_expression(&self) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let token = self.next_token().ok_or_else(|| {
            self.make_error(
                AstGenErrorKind::ExpectedExpression,
                None,
                None,
                Some(self.next_location()),
            )
        })?;

        // ::CompoundExpressions: firstly, we have to get the initial part of the expression, and then we can check
        // if there are any additional parts in the forms of either property accesses, indexing or infix function calls
        let subject = match &token.kind {
            kind if kind.is_unary_op() => return self.parse_unary_expression(),

            // Handle primitive literals
            kind if kind.is_literal() => self.parse_literal(),
            TokenKind::Ident(ident) => {
                let name = self.parse_access_name(self.node_with_span(*ident, token.span))?;

                // @@Speed: so here we want to be efficient about type_args, we'll just try to
                // see if the next token atom is a 'Lt' rather than using parse_token_atom
                // because it throws an error essentially and thus allocates a stupid amount
                // of strings which at the end of the day aren't even used...
                let type_args = match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Lt) => self
                        .peek_resultant_fn(|| self.parse_type_args(false))
                        .unwrap_or_else(AstNodes::empty),
                    _ => AstNodes::empty(),
                };

                // create the lhs expr.
                self.node_with_joined_span(
                    Expression::new(ExpressionKind::Variable(VariableExpr { name, type_args })),
                    &token.span,
                )
            }
            TokenKind::Lt => self.node_with_joined_span(
                Expression::new(ExpressionKind::TypeFunctionDef(
                    self.parse_type_function_def()?,
                )),
                &token.span,
            ),
            TokenKind::Keyword(Keyword::Struct) => self.node_with_joined_span(
                Expression::new(ExpressionKind::StructDef(self.parse_struct_def()?)),
                &token.span,
            ),
            TokenKind::Keyword(Keyword::Enum) => self.node_with_joined_span(
                Expression::new(ExpressionKind::EnumDef(self.parse_enum_def()?)),
                &token.span,
            ),
            TokenKind::Keyword(Keyword::Trait) => self.node_with_joined_span(
                Expression::new(ExpressionKind::TraitDef(self.parse_trait_def()?)),
                &token.span,
            ),
            // @@Note: This doesn't cover '{' case.
            kind if kind.begins_block() => {
                let start = self.current_location();

                let block = match kind {
                    TokenKind::Keyword(Keyword::For) => self.parse_for_loop()?,
                    TokenKind::Keyword(Keyword::While) => self.parse_while_loop()?,
                    TokenKind::Keyword(Keyword::Loop) => self
                        .node_with_joined_span(Block::Loop(LoopBlock(self.parse_block()?)), &start),
                    TokenKind::Keyword(Keyword::If) => self.parse_if_statement()?,
                    TokenKind::Keyword(Keyword::Match) => self.parse_match_block()?,
                    _ => unreachable!(),
                };

                self.node_with_joined_span(
                    Expression::new(ExpressionKind::Block(BlockExpr(block))),
                    &start,
                )
            }
            // Import
            TokenKind::Keyword(Keyword::Import) => self.parse_import()?,
            // Handle tree literals
            TokenKind::Tree(Delimiter::Brace, tree_index) => {
                let tree = self.token_trees.get(*tree_index).unwrap();

                self.parse_block_or_braced_literal(tree, &self.current_location())?
            }
            TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                let tree = self.token_trees.get(*tree_index).unwrap();

                self.parse_array_literal(tree, &self.current_location())?
            }
            TokenKind::Tree(Delimiter::Paren, tree_index) => {
                let mut is_func = false;

                // Now here we have to look ahead after the token_tree to see if there is an arrow
                // @@Speed: avoid using parse_token_atom() because we don't care about error messages
                //          We just want to purely look if there are is a combination of symbols following
                //          which make up an '=>'.
                let has_arrow = self
                    .peek_resultant_fn(|| -> Result<(), ()> {
                        match self.peek() {
                            Some(token)
                                if token.has_kind(TokenKind::Minus)
                                    || token.has_kind(TokenKind::Eq) =>
                            {
                                self.skip_token();
                                self.parse_token_fast(TokenKind::Gt).ok_or(())?;
                                Ok(())
                            }
                            _ => Err(()),
                        }
                    })
                    .is_some();

                if has_arrow {
                    self.offset.set(self.offset.get() - 2);
                    is_func = true;
                }

                let tree = self.token_trees.get(*tree_index).unwrap();

                match is_func {
                    true => {
                        let gen = self.from_stream(tree, token.span);
                        self.parse_function_literal(&gen)?
                    }
                    false => self.parse_expression_or_tuple(tree, &self.current_location())?,
                }
            }
            TokenKind::Keyword(Keyword::Continue) => self.node_with_span(
                Expression::new(ExpressionKind::Continue(ContinueStatement)),
                token.span,
            ),
            TokenKind::Keyword(Keyword::Break) => self.node_with_span(
                Expression::new(ExpressionKind::Break(BreakStatement)),
                token.span,
            ),
            TokenKind::Keyword(Keyword::Return) => {
                // @@Hack: check if the next token is a semi-colon, if so the return statement
                // has no returned expression...
                let return_expr = match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Semi) => {
                        ExpressionKind::Return(ReturnStatement(None))
                    }
                    Some(_) => ExpressionKind::Return(ReturnStatement(Some(
                        self.parse_expression_with_precedence(0)?,
                    ))),
                    None => ExpressionKind::Return(ReturnStatement(None)),
                };

                self.node_with_joined_span(Expression::new(return_expr), &token.span)
            }
            kind @ TokenKind::Keyword(_) => {
                return self.error_with_location(
                    AstGenErrorKind::Keyword,
                    None,
                    Some(*kind),
                    token.span,
                )
            }
            kind => {
                return self.error_with_location(
                    AstGenErrorKind::ExpectedExpression,
                    None,
                    Some(*kind),
                    token.span,
                )
            }
        };

        self.parse_singular_expression(subject)
    }

    /// Parse an expression whilst taking into account binary precedence operators.
    /// Parse chain of expressions with chain links being binary operators. Whilst
    /// parsing the chain, figure out the applicative precedence of each operator using
    /// Pratt parsing.
    pub(crate) fn parse_expression_with_precedence(
        &self,
        mut min_prec: u8,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        // first of all, we want to get the lhs...
        let mut lhs = self.parse_expression()?;

        // reset the compound_expr flag, since this is a new expression...
        self.is_compound_expr.set(false);

        loop {
            let op_start = self.next_location();
            // this doesn't consider operators that have an 'eq' variant because that is handled at the statement level,
            // since it isn't really a binary operator...
            let (op, consumed_tokens) = self.parse_operator();

            match op {
                // check if the operator here is re-assignable, as in '+=', '/=', if so then we need to stop
                // parsing onwards because this might be an assignable expression...
                // Only perform this check if know prior that the expression is not made of compounded components.
                Some(op) if !op.assigning => {
                    // consume the number of tokens eaten whilst getting the operator...
                    self.offset.update(|x| x + consumed_tokens as usize);

                    let op_span = op_start.join(self.current_location());

                    // check if we have higher precedence than the lhs expression...
                    let (l_prec, r_prec) = op.kind.infix_binding_power();

                    if l_prec < min_prec {
                        self.offset.update(|x| x - consumed_tokens as usize);
                        break;
                    }

                    // if the operator is a non-functional, (e.g. as) we need to perform a different conversion
                    // where we transform the AstNode into a different
                    if matches!(op.kind, OperatorKind::As) {
                        lhs = self.node_with_joined_span(
                            Expression::new(ExpressionKind::Typed(TypedExpr {
                                expr: lhs,
                                ty: self.parse_type()?,
                            })),
                            &op_span,
                        );

                        // since we don't descend, we still need to update the precedence to
                        // being 'r_prec'.
                        min_prec = r_prec;
                    } else {
                        let rhs = self.parse_expression_with_precedence(r_prec)?;
                        self.is_compound_expr.set(true);

                        // transform the operator into an OperatorFn
                        lhs = self.transform_binary_expression(
                            lhs,
                            rhs,
                            self.node_with_span(op, op_span),
                        );
                    }
                }
                _ => break,
            }
        }

        Ok(lhs)
    }

    /// Provided an initial subject expression that is parsed by the parent caller, this function
    /// will check if there are any additional components to the expression; in the form of either
    /// property access, infix function calls, indexing, etc.
    pub(crate) fn parse_singular_expression(
        &self,
        subject: AstNode<'c, Expression<'c>>,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        // record the starting span
        let start = self.current_location();

        let mut lhs_expr = subject;

        // so here we need to peek to see if this is either a index_access, field access or a function call...
        while let Some(next_token) = self.peek() {
            match &next_token.kind {
                // Property access or infix function call
                TokenKind::Dot => {
                    self.skip_token(); // eat the token since there isn't any alternative to being an ident or fn call.

                    let name_or_fn_call = self.parse_name_or_infix_call()?;
                    let kind = name_or_fn_call.into_body().move_out().into_kind();

                    match kind {
                        // The current behaviour is that the lhs is inserted as the first argument:
                        //
                        // `foo.bar()` transpiles to `bar(foo)`
                        //
                        // Additionally, if the RHS has arguments, they are shifted for the LHS to be inserted as the first argument...
                        //
                        // `foo.bar(baz)` transpiles to `bar(foo, baz)`
                        //
                        ExpressionKind::FunctionCall(FunctionCallExpr { subject, mut args }) => {
                            let span = lhs_expr.location();

                            // insert lhs_expr first...
                            args.entries.nodes.insert(
                                0,
                                self.node_with_span(
                                    FunctionCallArg {
                                        name: None,
                                        value: lhs_expr,
                                    },
                                    span,
                                ),
                                &self.wall,
                            );

                            lhs_expr = self.node_with_joined_span(
                                Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                                    subject,
                                    args,
                                })),
                                &start,
                            );
                        }
                        ExpressionKind::Variable(VariableExpr { name, type_args: _ }) => {
                            // @@Cleanup: This produces an AstNode<AccessName> whereas we just want the single name...
                            let ident = name.body().path[0].body();
                            let span = name.location();

                            let node = self.node_with_span(Name { ident: *ident }, span);

                            lhs_expr = self.node_with_span(
                                Expression::new(ExpressionKind::PropertyAccess(
                                    PropertyAccessExpr {
                                        subject: lhs_expr,
                                        property: node,
                                    },
                                )),
                                span,
                            );
                        }
                        _ => self.error(AstGenErrorKind::InfixCall, None, None)?,
                    }
                }
                // Array index access syntax: ident[...]
                TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                    self.skip_token();

                    let tree = self.token_trees.get(*tree_index).unwrap();
                    lhs_expr = self.parse_array_index(lhs_expr, tree, self.current_location())?;
                }
                // Function call
                TokenKind::Tree(Delimiter::Paren, tree_index) => {
                    self.skip_token();

                    let tree = self.token_trees.get(*tree_index).unwrap();
                    lhs_expr = self.parse_function_call(lhs_expr, tree, self.current_location())?;
                }
                _ => break,
            }
        }

        Ok(lhs_expr)
    }

    /// Parsing module import statement which are in the form of a function
    /// call that have a single argument in the form of a string literal.
    /// The syntax is as follows:
    ///
    /// import("./relative/path/to/module")
    ///
    /// The path argument to imports automatically assumes that the path you provide
    /// is references '.hash' extension file or a directory with a 'index.hash' file
    /// contained within the directory.
    pub(crate) fn parse_import(&self) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let pre = self.current_token().span;
        let start = self.current_location();

        let (tree, span) = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            }) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                (tree, *span)
            }
            Some(token) => self.error(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::from_row(
                    row![&self.wall; TokenKind::Delimiter(Delimiter::Paren, true)],
                )),
                Some(token.kind),
            )?,
            None => self.unexpected_eof()?,
        };

        let gen = self.from_stream(tree, span);

        let (raw, path, span) = match gen.peek() {
            Some(Token {
                kind: TokenKind::StrLiteral(str),
                span,
            }) => (str, STRING_LITERAL_MAP.lookup(*str), span),
            _ => gen.error(AstGenErrorKind::ImportPath, None, None)?,
        };

        gen.skip_token(); // eat the string argument
        gen.verify_is_empty()?;

        // Attempt to add the module via the resolver
        let import_path = PathBuf::from_str(path).unwrap_or_else(|err| match err {});
        let resolved_import_path = self
            .resolver
            .parse_import(&import_path, self.source_location(span));

        match resolved_import_path {
            Ok(resolved_import_path) => Ok(self.node_with_joined_span(
                Expression::new(ExpressionKind::Import(ImportExpr(
                    self.node_with_joined_span(
                        Import {
                            path: *raw,
                            resolved_path: resolved_import_path,
                        },
                        &start,
                    ),
                ))),
                &start,
            )),
            Err(err) => self.error_with_location(
                AstGenErrorKind::ErroneousImport(err),
                None,
                None,
                pre.join(self.current_location()),
            ),
        }
    }

    /// Parse a function call which requires that the [AccessName] is pre-parsed and passed
    /// into the function which deals with the call arguments.
    pub(crate) fn parse_function_call(
        &self,
        subject: AstNode<'c, Expression<'c>>,
        tree: &'stream Row<'stream, Token>,
        span: Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, span);
        let mut args = self.node_with_span(
            FunctionCallArgs {
                entries: AstNodes::empty(),
            },
            span,
        );

        while gen.has_token() {
            let start = gen.current_location();

            // here we trying to check if this argument is in form of just an expression or if there is a
            // name being assigned here...
            let name = match (gen.peek(), gen.peek_second()) {
                (
                    Some(Token {
                        kind: TokenKind::Ident(_),
                        ..
                    }),
                    Some(Token {
                        kind: TokenKind::Eq,
                        ..
                    }),
                ) => {
                    let name = gen.parse_name()?;
                    gen.skip_token(); // '='

                    Some(name)
                }
                _ => None,
            };

            // Now here we expect an expression...
            let value = gen.parse_expression_with_precedence(0)?;

            args.entries.nodes.push(
                gen.node_with_span(FunctionCallArg { name, value }, start),
                &self.wall,
            );

            // now we eat the next token, checking that it is a comma
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                _ => break,
            };
        }

        let span = subject.location();

        Ok(gen.node_with_joined_span(
            Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                subject,
                args,
            })),
            &span,
        ))
    }

    /// Parse an array index. Array indexes are constructed with square brackets
    /// wrapping a singular expression.
    pub(crate) fn parse_array_index(
        &self,
        subject: AstNode<'c, Expression<'c>>,
        tree: &'stream Row<'stream, Token>,
        span: Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, span);
        let start = gen.current_location();

        // parse the indexing expression between the square brackets...
        let index_expr = gen.parse_expression_with_precedence(0)?;
        let (index_span, subject_span) = (index_expr.location(), subject.location());
        let span = subject_span.join(index_span);

        // since nothing should be after the expression, we can check that no tokens
        // are left and the generator is empty, otherwise report this as an unexpected_token
        gen.verify_is_empty()?;

        Ok(self.node_with_span(
            Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                subject: self.make_ident("index", &start),
                args: self.node_with_span(
                    FunctionCallArgs {
                        entries: ast_nodes![&self.wall; self.node_with_span(
                                FunctionCallArg {
                                    name: None,
                                    value: subject
                                }, subject_span),
                                self.node_with_span(
                                FunctionCallArg {
                                name: None,
                                value: index_expr
                            }, index_span)],
                    },
                    span,
                ),
            })),
            span,
        ))
    }

    /// Parses a unary operator or expression modifier followed by a singular expression.
    /// Once the unary operator is picked up, the expression is parsed given the specific
    /// rules of the operator or expression modifier.
    pub(crate) fn parse_unary_expression(&self) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let token = self.current_token();
        let start = self.current_location();

        let expr_kind = match &token.kind {
            TokenKind::Star => ExpressionKind::Deref(DerefExpr(self.parse_expression()?)),
            TokenKind::Amp => {
                // Check if this reference is raw...
                match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Raw)) => {
                        self.skip_token();
                        ExpressionKind::Ref(RefExpr {
                            inner_expr: self.parse_expression()?,
                            kind: RefKind::Raw,
                        })
                    }
                    _ => ExpressionKind::Ref(RefExpr {
                        inner_expr: self.parse_expression()?,
                        kind: RefKind::Normal,
                    }),
                }
            }
            kind @ (TokenKind::Plus | TokenKind::Minus) => {
                let value = self.parse_expression()?;
                let span = value.location();

                let fn_name = match kind {
                    TokenKind::Plus => "pos",
                    TokenKind::Minus => "neg",
                    _ => unreachable!(),
                };

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident(fn_name, &start),
                    args: self.node_with_span(
                        FunctionCallArgs {
                            entries: ast_nodes![&self.wall; self.node_with_span(FunctionCallArg {
                                    name: None,
                                    value
                                }, span)],
                        },
                        span,
                    ),
                })
            }
            TokenKind::Tilde => {
                let value = self.parse_expression()?;
                let span = value.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident("notb", &start),
                    args: self.node_with_span(
                        FunctionCallArgs {
                            entries: ast_nodes![&self.wall; self.node_with_span(FunctionCallArg {
                                    name: None,
                                    value
                                }, span)],
                        },
                        span,
                    ),
                })
            }
            TokenKind::Hash => {
                // First get the directive subject, and expect a possible singular expression
                // followed by the directive.
                let name = self.parse_name()?;
                let subject = self.parse_expression()?;

                // create the subject node
                return Ok(self.node_with_joined_span(
                    Expression::new(ExpressionKind::Directive(DirectiveExpr { name, subject })),
                    &start,
                ));
            }
            TokenKind::Exclamation => {
                let value = self.parse_expression()?;
                let span = value.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident("not", &start),
                    args: self.node_with_span(
                        FunctionCallArgs {
                            entries: ast_nodes![&self.wall; self.node_with_span(FunctionCallArg {
                                    name: None,
                                    value
                                }, span)],
                        },
                        span,
                    ),
                })
            }
            TokenKind::Keyword(Keyword::Unsafe) => {
                let arg = self.parse_expression()?;
                ExpressionKind::Unsafe(UnsafeExpr(arg))
            }
            kind => panic!("Expected token to be a unary operator, but got '{}'", kind),
        };

        Ok(self.node_with_joined_span(Expression::new(expr_kind), &start))
    }

    /// Parse a declaration.
    ///
    /// A declaration is either a variable declaration, function declaration, or both.
    /// As such a name is returned before parsing a type, function, or both.
    /// A destructuring pattern, potential for-all statement, optional
    /// type definition and a potential definition of the right hand side. For example:
    /// ```text
    /// some_var...<int>: float = ...;
    /// ^^^^^^^^   ^^^^^  ^^^^^   ^^^─────┐
    ///   pattern  bound   type    the right hand-side expr
    /// ```
    pub(crate) fn parse_declaration(
        &self,
        pattern: AstNode<'c, Pattern<'c>>,
    ) -> AstGenResult<'c, Declaration<'c>> {
        self.parse_token(TokenKind::Colon)?;

        // Attempt to parse an optional type...
        let ty = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Eq) => None,
            _ => Some(self.parse_type()?),
        };

        // Now parse the value after the assignment
        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Eq) => {
                self.skip_token();

                let value = self.parse_expression_with_precedence(0)?;
                Ok(Declaration {
                    pattern,
                    ty,
                    value: Some(value),
                })
            }
            _ => Ok(Declaration {
                pattern,
                ty,
                value: None,
            }),
        }
    }

    /// Given a initial left-hand side expression, attempt to parse a re-assignment operator and
    /// then right hand-side. If a re-assignment operator is successfully parsed, then a right
    /// hand-side is expected and will hard fail. If no re-assignment operator is found, then it
    /// should just return the left-hand side.
    pub(crate) fn try_parse_expression_with_re_assignment(
        &self,
    ) -> AstGenResult<'c, (AstNode<'c, Expression<'c>>, bool)> {
        let lhs = self.parse_expression_with_precedence(0)?;

        if let Some(op) = self.peek_resultant_fn(|| self.parse_re_assignment_op()) {
            // Parse the rhs and the semi
            let rhs = self.parse_expression_with_precedence(0)?;

            // Now we need to transform the re-assignment operator into a function call
            Ok((self.transform_binary_expression(lhs, rhs, op), false))
        } else {
            Ok((lhs, false))
        }
    }

    /// Utility function to transform to some expression into a referenced expression
    /// given some condition. This function is useful when transpiling some types of
    /// operators which might have a side-effect to overwrite the lhs.
    fn transform_expr_into_ref(
        &self,
        expr: AstNode<'c, Expression<'c>>,
        transform: bool,
    ) -> AstNode<'c, Expression<'c>> {
        match transform {
            true => self.node(Expression::new(ExpressionKind::Ref(RefExpr {
                inner_expr: expr,
                kind: RefKind::Normal,
            }))),
            false => expr,
        }
    }

    /// Create an [Expression] from two provided expressions and an [Operator].
    fn transform_binary_expression(
        &self,
        lhs: AstNode<'c, Expression<'c>>,
        rhs: AstNode<'c, Expression<'c>>,
        op: AstNode<'c, Operator>,
    ) -> AstNode<'c, Expression<'c>> {
        let operator_location = op.location();
        let Operator { kind, assigning } = op.body();

        if kind.is_compound() {
            // for compound functions that include ordering, we essentially transpile
            // into a match block that checks the result of the 'ord' fn call to the
            // 'Ord' enum variants. This also happens for operators such as '>=' which
            // essentially means that we have to check if the result of 'ord()' is either
            // 'Eq' or 'Gt'.
            self.transform_compound_ord_fn(*kind, *assigning, lhs, rhs, operator_location)
        } else if kind.is_lazy() {
            // some functions have to exhibit a short-circuiting behaviour, namely
            // the logical 'and' and 'or' operators. To do this, we expect the 'and'
            // 'or' trait (and their assignment counterparts) to expect the rhs part
            // as a lambda. So, we essentially create a lambda that calls the rhs, or
            // in other words, something like this happens:
            //
            // >>> lhs && rhs
            // vvv (transpiles to...)
            // >>> and(lhs, () => rhs)
            //

            let (lhs_span, rhs_span) = (lhs.location(), rhs.location());
            let span = lhs_span.join(rhs_span);

            self.node_with_span(Expression::new(ExpressionKind::FunctionCall(
                    FunctionCallExpr {
                        subject: self.node_with_span(
                            Expression::new(ExpressionKind::Variable(VariableExpr {
                                name: self.make_access_name_from_str(op.body().to_str(), op.location()),
                                type_args: AstNodes::empty(),
                            })),
                            op.location(),
                        ),
                        args: self.node_with_joined_span(
                            FunctionCallArgs {
                            entries: ast_nodes![&self.wall;
                                self.node_with_span(FunctionCallArg {
                                    name: None,
                                    value: self.transform_expr_into_ref(lhs, *assigning),
                                }, lhs_span),
                                self.node(
                                FunctionCallArg {
                                    name: None,
                                    value: self.node_with_span(Expression::new(ExpressionKind::FunctionDef(
                                        FunctionDef {
                                            args: AstNodes::empty(),
                                            return_ty: None,
                                            fn_body: rhs,
                                        })), rhs_span),
                                })
                            ],
                        },  &span),
                    },
                )), span)
        } else {
            let (lhs_span, rhs_span) = (lhs.location(), rhs.location());
            let location = lhs_span.join(rhs_span);

            self.node_with_span(
                Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.node_with_span(
                        Expression::new(ExpressionKind::Variable(VariableExpr {
                            name: self.make_access_name_from_str(op.body().to_str(), op.location()),
                            type_args: AstNodes::empty(),
                        })),
                        op.location(),
                    ),
                    args: self.node_with_joined_span(
                        FunctionCallArgs {
                            entries: ast_nodes![&self.wall;
                                self.node_with_span( {
                                    FunctionCallArg {
                                        name: None,
                                        value: self.transform_expr_into_ref(lhs, *assigning),
                                    }
                                }, lhs_span),
                                self.node_with_span( {
                                    FunctionCallArg {
                                        name: None,
                                        value: rhs,
                                    }
                                }, rhs_span)
                            ],
                        },
                        &location,
                    ),
                })),
                op.location(),
            )
        }
    }

    /// Function that is used to transfer an operator which is of `compound` type into a
    /// `match` statement that involves matching on the return type of the language defined
    /// `ord` trait. The transformation involves converting the initial operator into
    /// a function call that invokes `ord` with the `lhs` and `rhs`.
    ///
    /// The function result is then matched within a match on the [Ord] enumeration
    /// which contains variants that represent the result of the comparison.
    ///
    /// Depending on whether the comparison operator is inclusive or not, multiple variants
    /// within a single comparison branch might be generated. For example, if the
    /// expression `a < 3` is transformed, then the following code is generated:
    ///
    /// ```text
    /// match ord(a, 3) {
    ///     Lt => true,
    ///     _ =>  false
    /// }
    /// ```
    ///
    /// However if the expression was inclusive `a <= 3` then this is generated:
    ///
    /// ```text
    /// match ord(a, 3) {
    ///     Lt | Eq => true,
    ///     _ =>  false
    /// }
    /// ```
    fn transform_compound_ord_fn(
        &self,
        fn_ty: OperatorKind,
        assigning: bool,
        lhs: AstNode<'c, Expression<'c>>,
        rhs: AstNode<'c, Expression<'c>>,
        operator_location: Location,
    ) -> AstNode<'c, Expression<'c>> {
        let location = lhs.location().join(rhs.location());

        // we need to transform the lhs into a reference if the type of function is 'assigning'
        let lhs = self.transform_expr_into_ref(lhs, assigning);
        let (lhs_span, rhs_span) = (lhs.location(), rhs.location());

        let fn_call = self.node(Expression::new(ExpressionKind::FunctionCall(
            FunctionCallExpr {
                subject: self.make_ident("ord", &operator_location),
                args: self.node(FunctionCallArgs {
                    entries: ast_nodes![&self.wall;
                    self.node_with_span(
                        FunctionCallArg {
                            name: None,
                            value: lhs,
                        },
                        lhs_span
                    ),
                    self.node_with_span(
                        FunctionCallArg {
                            name: None,
                            value: rhs,
                        },
                        rhs_span
                    )],
                }),
            },
        )));

        let make_constructor_pattern = |symbol: &str, location: Location| {
            self.node(Pattern::Constructor(ConstructorPattern {
                name: self.make_access_name_from_str(symbol, location),
                fields: AstNodes::empty(),
            }))
        };

        // each tuple bool variant represents a branch the match statement
        // should return 'true' on, and all the rest will return false...
        // the order is (Lt, Eq, Gt)
        let mut branches = match fn_ty {
            OperatorKind::LtEq => {
                ast_nodes![&self.wall; self.node(MatchCase {
                    pattern: self.node(Pattern::Or(OrPattern {
                        variants: ast_nodes![&self.wall;
                        make_constructor_pattern("Lt", location),
                        make_constructor_pattern("Eq", location),
                        ],
                    })),
                    expr: self.make_bool(true)
                })]
            }
            OperatorKind::GtEq => {
                ast_nodes![&self.wall; self.node(MatchCase {
                    pattern: self.node(Pattern::Or(OrPattern {
                        variants: ast_nodes![&self.wall;
                        make_constructor_pattern("Gt", location),
                        make_constructor_pattern("Eq", location),
                        ],
                    })),
                    expr: self.make_bool(true)
                })]
            }
            OperatorKind::Lt => {
                ast_nodes![&self.wall; self.node(MatchCase {
                    pattern: make_constructor_pattern("Lt", location),
                    expr: self.make_bool(true)
                })]
            }
            OperatorKind::Gt => {
                ast_nodes![&self.wall; self.node(MatchCase {
                    pattern: make_constructor_pattern("Gt", location),
                    expr: self.make_bool(true)
                })]
            }
            _ => unreachable!(),
        };

        // add the '_' case to the branches to return false on any other
        // condition
        branches.nodes.push(
            self.node(MatchCase {
                pattern: self.node(Pattern::Ignore(IgnorePattern)),
                expr: self.make_bool(false),
            }),
            &self.wall,
        );

        self.node(Expression::new(ExpressionKind::Block(BlockExpr(
            self.node(Block::Match(MatchBlock {
                subject: fn_call,
                cases: branches,
                origin: MatchOrigin::Match,
            })),
        ))))
    }

    /// Parse an single name or a function call that is applied on the left hand side
    /// expression. Infix calls and name are only separated by infix calls having
    /// parenthesees at the end of the name.
    pub(crate) fn parse_name_or_infix_call(&self) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Dot));

        let start = self.current_location();

        match &self.next_token() {
            Some(Token {
                kind: TokenKind::Ident(id),
                span: id_span,
            }) => {
                let type_args = self
                    .peek_resultant_fn(|| self.parse_type_args(false))
                    .unwrap_or_else(AstNodes::empty);

                // create the subject of the call
                let subject = self.node_with_span(
                    Expression::new(ExpressionKind::Variable(VariableExpr {
                        name: self.make_access_name_from_identifier(*id, *id_span),
                        type_args,
                    })),
                    start.join(self.current_location()),
                );

                match self.peek() {
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                        span,
                    }) => {
                        // Eat the generator now...
                        self.skip_token();

                        // so we know that this is the beginning of the function call, so we have to essentially parse an arbitrary number
                        // of expressions separated by commas as arguments to the call.
                        let tree = self.token_trees.get(*tree_index).unwrap();
                        self.parse_function_call(subject, tree, *span)
                    }
                    _ => Ok(subject),
                }
            }
            _ => self.error(AstGenErrorKind::InfixCall, None, None)?,
        }
    }

    /// Parse either a block, a set, or a map. The function has to parse
    /// an initial expression and then determine the type of needed parsing
    /// by the following operator, whether it is a colon, comma or a semicolon.
    pub(crate) fn parse_block_or_braced_literal(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: &Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);

        // handle two special cases for empty map and set literals, if the only token
        // is a colon, this must be a map literal, or if the only token is a comma it is
        // an empty set literal.
        if gen.stream.len() == 1 {
            match gen.peek().unwrap() {
                token if token.has_kind(TokenKind::Colon) => {
                    return Ok(self.node_with_span(
                        Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                            self.node_with_span(
                                Literal::Map(MapLiteral {
                                    elements: AstNodes::empty(),
                                }),
                                *span,
                            ),
                        ))),
                        *span,
                    ))
                }
                token if token.has_kind(TokenKind::Comma) => {
                    return Ok(self.node_with_span(
                        Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                            self.node_with_span(
                                Literal::Set(SetLiteral {
                                    elements: AstNodes::empty(),
                                }),
                                *span,
                            ),
                        ))),
                        *span,
                    ))
                }
                _ => (),
            }
        }

        // Is this an empty block?
        if !gen.has_token() {
            return Ok(self.node_with_span(
                Expression::new(ExpressionKind::Block(BlockExpr(self.node_with_span(
                    Block::Body(BodyBlock {
                        statements: AstNodes::empty(),
                        expr: None,
                    }),
                    *span,
                )))),
                *span,
            ));
        }

        let parse_block = |initial_offset: usize| -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
            // reset the position and attempt to parse a statement
            gen.offset.set(initial_offset);

            // check here if there is a 'semi', and then convert the expression into a statement.
            let block = self.parse_block_from_gen(&gen, *span, None)?;

            Ok(self.node_with_span(
                Expression::new(ExpressionKind::Block(BlockExpr(block))),
                *span,
            ))
        };

        // Here we have to parse the initial expression and then check if there is a specific
        // separator. We have to check:
        //
        // - If an expression is followed by a comma separator, it must be a set literal.
        //
        // - If an expression is followed by a ':' (colon), it must be a map literal.
        //
        // - Otherwise, it must be a block and we should continue parsing the block from here
        let initial_offset = gen.offset();
        let expr = gen.parse_expression();

        match (gen.peek(), expr) {
            (Some(token), Ok(expr)) if token.has_kind(TokenKind::Comma) => {
                gen.skip_token(); // ','

                let literal = self.parse_set_literal(gen, expr)?;

                Ok(self.node_with_span(
                    Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(literal))),
                    *span,
                ))
            }
            (Some(token), Ok(expr)) if token.has_kind(TokenKind::Colon) => {
                gen.skip_token(); // ':'

                // So problem here is that we don't know if it is a map literal or just a
                // declaration assignment. We can attempt to abort this if we spot that
                // there is a following '=' or parsing the expression doesn't work...
                if gen.parse_token_fast(TokenKind::Eq).is_some() {
                    return parse_block(initial_offset);
                }

                let start_pos = expr.location();
                let entry = self.node_with_joined_span(
                    MapLiteralEntry {
                        key: expr,
                        value: gen.parse_expression_with_precedence(0)?,
                    },
                    &start_pos,
                );

                // Peek ahead to check if there is a comma, if there is then we'll parse more map entries,
                // and pass it into parse_map_literal.
                match gen.peek() {
                    Some(token) if token.has_kind(TokenKind::Comma) => {
                        gen.skip_token();

                        let literal = self.parse_map_literal(gen, entry)?;

                        Ok(self.node_with_span(
                            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(literal))),
                            *span,
                        ))
                    }
                    _ => Ok(self.node_with_span(
                        Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                            self.node_with_span(
                                Literal::Map(MapLiteral {
                                    elements: ast_nodes![&self.wall; entry],
                                }),
                                *span,
                            ),
                        ))),
                        *span,
                    )),
                }
            }
            (Some(_), _) => parse_block(initial_offset),
            (None, Ok(expr)) => {
                // This block is just a block with a single expression

                Ok(self.node_with_span(
                    Expression::new(ExpressionKind::Block(BlockExpr(self.node_with_span(
                        Block::Body(BodyBlock {
                            statements: AstNodes::empty(),
                            expr: Some(expr),
                        }),
                        *span,
                    )))),
                    *span,
                ))
            }
            (None, Err(_)) => {
                // reset the position and attempt to parse a statement
                gen.offset.set(initial_offset);
                let (_, statement) = gen.parse_top_level_expression(false)?;

                Ok(self.node_with_span(
                    Expression::new(ExpressionKind::Block(BlockExpr(self.node_with_span(
                        Block::Body(BodyBlock {
                            statements: ast_nodes![&self.wall; statement],
                            expr: None,
                        }),
                        *span,
                    )))),
                    *span,
                ))
            }
        }
    }

    /// Function to either parse an expression that is wrapped in parentheses or a tuple literal. If this
    /// is a tuple literal, the first expression must be followed by a comma separator, after that the comma
    /// after the expression is optional.
    ///
    ///
    /// Tuples have a familiar syntax with many other languages, but exhibit two distinct differences between the common syntax.
    /// These differences are:
    ///
    /// - Empty tuples: (,)
    /// - Singleton tuple : (A,)
    /// - Many membered tuple: (A, B, C) or (A, B, C,)
    ///
    pub(crate) fn parse_expression_or_tuple(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: &Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);
        let start = self.current_location();

        // Handle the case if it is an empty stream, this means that if it failed to
        // parse a function in the form of `() => ...` for whatever reason, then it
        // is trying to parse either a tuple or an expression.
        // Handle the empty tuple case
        if gen.stream.len() < 2 {
            let tuple = gen.node_with_joined_span(
                Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                    gen.node_with_joined_span(
                        Literal::Tuple(TupleLiteral {
                            elements: ast_nodes![&self.wall;],
                        }),
                        &start,
                    ),
                ))),
                &start,
            );

            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();

                    return Ok(tuple);
                }
                None => return Ok(tuple),
                _ => (),
            };
        }

        let entry = gen.parse_tuple_literal_entry()?;

        // In the special case where this is just an expression that is wrapped within parenthesees, we can
        // check that the 'name' and 'ty' parameters are set to `None` and that there are no extra tokens
        // that are left within the token tree...
        if entry.ty.is_none() && entry.name.is_none() && !gen.has_token() {
            return Ok(entry.into_body().move_out().value);
        }

        let mut elements = ast_nodes![&self.wall; entry];

        loop {
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();

                    // Handles the case where this is a trailing comma and no tokens after...
                    if !gen.has_token() {
                        break;
                    }

                    elements
                        .nodes
                        .push(gen.parse_tuple_literal_entry()?, &self.wall)
                }
                Some(token) => {
                    gen.error(AstGenErrorKind::ExpectedExpression, None, Some(token.kind))?
                }
                None => break,
            }
        }

        Ok(gen.node_with_joined_span(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                gen.node_with_joined_span(Literal::Tuple(TupleLiteral { elements }), &start),
            ))),
            &start,
        ))
    }

    /// Parse a function definition argument, which is made of an identifier and a function type.
    pub(crate) fn parse_function_def_arg(
        &self,
    ) -> AstGenResult<'c, AstNode<'c, FunctionDefArg<'c>>> {
        let name = self.parse_name()?;
        let name_span = name.location();

        let ty = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Colon) => {
                self.skip_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        let default = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Eq) => {
                self.skip_token();
                Some(self.parse_expression_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(self.node_with_joined_span(FunctionDefArg { name, ty, default }, &name_span))
    }

    /// Parse a function literal. Function literals are essentially definitions of lambdas
    /// that can be assigned to variables or passed as arguments into other functions.
    pub(crate) fn parse_function_literal(
        &self,
        gen: &Self,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let start = self.current_location();

        // parse function definition arguments.
        let args = gen.parse_separated_fn(
            || gen.parse_function_def_arg(),
            || gen.parse_token(TokenKind::Comma),
        )?;

        // check if there is a return type
        let return_ty = match self.peek_resultant_fn(|| self.parse_thin_arrow()) {
            Some(_) => Some(self.parse_type()?),
            _ => None,
        };

        self.parse_arrow()?;

        let fn_body = match self.peek() {
            Some(_) => self.parse_expression_with_precedence(0)?,
            None => self.error(AstGenErrorKind::ExpectedFnBody, None, None)?,
        };

        Ok(self.node_with_joined_span(
            Expression::new(ExpressionKind::FunctionDef(FunctionDef {
                args,
                return_ty,
                fn_body,
            })),
            &start,
        ))
    }
}
