//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use std::{path::PathBuf, str::FromStr};

use hash_ast::{ast::*, ast_nodes};
use hash_source::{identifier::Identifier, location::Span};
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a top level [Expression] that are terminated with a semi-colon.
    #[profiling::function]
    pub fn parse_top_level_expression(
        &self,
        semi_required: bool,
    ) -> AstGenResult<(bool, AstNode<Expression>)> {
        let start = self.current_location();

        // So here we want to check that the next token(s) could make up a singular pattern which
        // is then followed by a `:` to denote that this is a declaration.
        let decl = match self.begins_pattern() {
            true => {
                let pat = self.parse_singular_pattern()?;
                self.parse_token(TokenKind::Colon)?;

                let decl = self.parse_declaration(pat)?;

                Some(self.node_with_span(Expression::new(ExpressionKind::Declaration(decl)), start))
            }
            false => None,
        };

        let expr = match decl {
            Some(statement) => Ok(statement),
            None => {
                let (expr, re_assigned) = self.parse_expression_with_re_assignment()?;

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
                        Some(_) => self.error_with_location(
                            AstGenErrorKind::ExpectedOperator,
                            Some(TokenKindVector::from_row(vec![
                                TokenKind::Dot,
                                TokenKind::Eq,
                                TokenKind::Semi,
                            ])),
                            None,
                            self.next_location(),
                        ),
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
    #[profiling::function]
    pub(crate) fn parse_expression(&self) -> AstGenResult<AstNode<Expression>> {
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
                let start = self.node_with_span(*ident, token.span);

                self.node_with_joined_span(
                    Expression::new(ExpressionKind::Variable(
                        self.parse_variable_expression(Some(start))?,
                    )),
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
            TokenKind::Keyword(Keyword::Type) => self.node_with_joined_span(
                Expression::new(ExpressionKind::Type(TypeExpr(self.parse_type()?))),
                &token.span,
            ),
            // @@Note: This doesn't cover '{' case.
            TokenKind::Keyword(Keyword::Impl)
                if self.peek().map_or(false, |tok| !tok.is_brace_tree()) =>
            {
                let ty = self.parse_type()?;
                let implementation = self.parse_expressions_from_braces()?;

                self.node_with_joined_span(
                    Expression::new(ExpressionKind::TraitImpl(TraitImpl { ty, implementation })),
                    &token.span,
                )
            }
            kind if kind.begins_block() => {
                let start = self.current_location();

                let block = match kind {
                    TokenKind::Keyword(Keyword::For) => self.parse_for_loop()?,
                    TokenKind::Keyword(Keyword::While) => self.parse_while_loop()?,
                    TokenKind::Keyword(Keyword::Loop) => self
                        .node_with_joined_span(Block::Loop(LoopBlock(self.parse_block()?)), &start),
                    TokenKind::Keyword(Keyword::If) => self.parse_if_block()?,
                    TokenKind::Keyword(Keyword::Match) => self.parse_match_block()?,
                    TokenKind::Keyword(Keyword::Mod) => self
                        .node_with_joined_span(Block::Mod(ModBlock(self.parse_block()?)), &start),
                    TokenKind::Keyword(Keyword::Impl) => self
                        .node_with_joined_span(Block::Impl(ImplBlock(self.parse_block()?)), &start),
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
                        self.parse_function_definition(&gen)?
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

    fn parse_variable_expression(
        &self,
        start: Option<AstNode<Identifier>>,
    ) -> AstGenResult<VariableExpr> {
        let name = match start {
            Some(node) => self.parse_access_name(node)?,
            None => match self.peek() {
                Some(Token {
                    kind: TokenKind::Ident(ident),
                    span,
                }) => {
                    self.skip_token();
                    self.parse_access_name(self.node_with_span(*ident, *span))?
                }
                token => self.error_with_location(
                    AstGenErrorKind::AccessName,
                    None,
                    token.map(|t| t.kind),
                    token.map_or_else(|| self.next_location(), |tok| tok.span),
                )?,
            },
        };

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

        Ok(VariableExpr { name, type_args })
    }

    /// Parse an expression whilst taking into account binary precedence operators.
    /// Parse chain of expressions with chain links being binary operators. Whilst
    /// parsing the chain, figure out the applicative precedence of each operator using
    /// Pratt parsing.
    pub(crate) fn parse_expression_with_precedence(
        &self,
        mut min_prec: u8,
    ) -> AstGenResult<AstNode<Expression>> {
        // first of all, we want to get the lhs...
        let mut lhs = self.parse_expression()?;
        let lhs_span = lhs.span();

        // reset the compound_expr flag, since this is a new expression...
        self.is_compound_expr.set(false);

        loop {
            let op_start = self.next_location();
            // this doesn't consider operators that have an 'eq' variant because that is handled at the statement level,
            // since it isn't really a binary operator...
            let (op, consumed_tokens) = self.parse_binary_operator();

            // We want to break if it's an operator and it is wanting to re-assign
            if op.is_some_and(|op| op.is_re_assignable())
                && matches!(self.peek_nth(consumed_tokens as usize), Some(token) if token.has_kind(TokenKind::Eq))
            {
                break;
            }

            match op {
                // check if the operator here is re-assignable, as in '+=', '/=', if so then we need to stop
                // parsing onwards because this might be an assignable expression...
                // Only perform this check if know prior that the expression is not made of compounded components.
                Some(op) => {
                    // check if we have higher precedence than the lhs expression...
                    let (l_prec, r_prec) = op.infix_binding_power();

                    if l_prec < min_prec {
                        break;
                    }

                    self.offset.update(|x| x + consumed_tokens as usize);
                    let op_span = op_start.join(self.current_location());

                    // if the operator is a non-functional, (e.g. as) we need to perform a different conversion
                    // where we transform the AstNode into a different
                    if op == BinOp::As {
                        lhs = self.node_with_joined_span(
                            Expression::new(ExpressionKind::As(CastExpr {
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
                        lhs = self.node_with_joined_span(
                            Expression::new(ExpressionKind::BinaryExpr(BinaryExpression {
                                lhs,
                                rhs,
                                operator: self.node_with_span(op, op_span),
                            })),
                            &lhs_span,
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
        subject: AstNode<Expression>,
    ) -> AstGenResult<AstNode<Expression>> {
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
                    let kind = name_or_fn_call.into_body().into_kind();

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
                            let span = lhs_expr.span();

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
                            let span = name.span();

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
    pub(crate) fn parse_import(&self) -> AstGenResult<AstNode<Expression>> {
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
                Some(TokenKindVector::from_row(vec![TokenKind::Delimiter(
                    Delimiter::Paren,
                    true,
                )])),
                Some(token.kind),
            )?,
            None => self.unexpected_eof()?,
        };

        let gen = self.from_stream(tree, span);

        let (raw, path, span) = match gen.peek() {
            Some(Token {
                kind: TokenKind::StrLiteral(str),
                span,
            }) => (str, *str, span),
            _ => gen.error(AstGenErrorKind::ImportPath, None, None)?,
        };

        gen.skip_token(); // eat the string argument
        gen.verify_is_empty()?;

        // Attempt to add the module via the resolver
        let import_path = PathBuf::from_str(path.into()).unwrap_or_else(|err| match err {});
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
        subject: AstNode<Expression>,
        tree: &'stream [Token],
        span: Span,
    ) -> AstGenResult<AstNode<Expression>> {
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

            args.entries
                .nodes
                .push(gen.node_with_span(FunctionCallArg { name, value }, start));

            // now we eat the next token, checking that it is a comma
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                Some(token) => gen.error_with_location(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::singleton(TokenKind::Comma)),
                    Some(token.kind),
                    token.span,
                )?,
                None => break,
            };
        }

        gen.verify_is_empty()?;

        let span = subject.span();

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
        subject: AstNode<Expression>,
        tree: &'stream [Token],
        span: Span,
    ) -> AstGenResult<AstNode<Expression>> {
        let gen = self.from_stream(tree, span);
        let start = gen.current_location();

        // parse the indexing expression between the square brackets...
        let index_expr = gen.parse_expression_with_precedence(0)?;

        // since nothing should be after the expression, we can check that no tokens
        // are left and the generator is empty, otherwise report this as an unexpected_token
        gen.verify_is_empty()?;

        Ok(self.node_with_joined_span(
            Expression::new(ExpressionKind::Index(IndexExpression {
                subject,
                index_expr,
            })),
            &start,
        ))
    }

    /// Parses a unary operator or expression modifier followed by a singular expression.
    /// Once the unary operator is picked up, the expression is parsed given the specific
    /// rules of the operator or expression modifier.
    pub(crate) fn parse_unary_expression(&self) -> AstGenResult<AstNode<Expression>> {
        let token = self.current_token();
        let start = self.current_location();

        let expr_kind = match &token.kind {
            TokenKind::Star => ExpressionKind::Deref(DerefExpr(self.parse_expression()?)),
            TokenKind::Amp => {
                // Check if this reference is raw...
                match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Raw)) => {
                        self.skip_token();

                        // Parse a mutability modifier if any
                        let mutability = self
                            .parse_token_fast(TokenKind::Keyword(Keyword::Mut))
                            .map(|_| {
                                self.node_with_span(Mutability::Mutable, self.current_location())
                            });

                        ExpressionKind::Ref(RefExpr {
                            inner_expr: self.parse_expression()?,
                            kind: RefKind::Raw,
                            mutability,
                        })
                    }
                    Some(Token {
                        kind: TokenKind::Keyword(Keyword::Mut),
                        span,
                    }) => {
                        self.skip_token();
                        ExpressionKind::Ref(RefExpr {
                            inner_expr: self.parse_expression()?,
                            kind: RefKind::Raw,
                            mutability: Some(self.node_with_span(Mutability::Mutable, *span)),
                        })
                    }
                    _ => ExpressionKind::Ref(RefExpr {
                        inner_expr: self.parse_expression()?,
                        kind: RefKind::Normal,
                        mutability: None,
                    }),
                }
            }
            TokenKind::Plus => return self.parse_expression(),
            kind @ (TokenKind::Minus | TokenKind::Exclamation | TokenKind::Tilde) => {
                let expr = self.parse_expression()?;

                let operator = self.node_with_span(
                    match kind {
                        TokenKind::Minus => UnOp::Neg,
                        TokenKind::Exclamation => UnOp::Not,
                        TokenKind::Tilde => UnOp::BitNot,
                        _ => unreachable!(),
                    },
                    start,
                );

                ExpressionKind::UnaryExpr(UnaryExpression { expr, operator })
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
    /// some_var: float = ...;
    /// ^^^^^^^^  ^^^^^   ^^^─────┐
    /// pattern    type    the right hand-side expr
    /// ```
    pub(crate) fn parse_declaration(&self, pattern: AstNode<Pattern>) -> AstGenResult<Declaration> {
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

    /// Function to pass a [MergeDeclaration] which is a pattern on the right-hand side followed
    /// by the `~=` operator and then an expression (which should be either a [ImplBlock] or a [TraitImpl]).
    pub(crate) fn parse_merge_declaration(
        &self,
        decl: AstNode<Expression>,
    ) -> AstGenResult<AstNode<Expression>> {
        self.parse_token(TokenKind::Eq)?;
        let value = self.parse_expression_with_precedence(0)?;
        let decl_span = decl.span();

        Ok(self.node_with_joined_span(
            Expression::new(ExpressionKind::MergeDeclaration(MergeDeclaration {
                decl,
                value,
            })),
            &decl_span,
        ))
    }

    /// Given a initial left-hand side expression, attempt to parse a re-assignment operator and
    /// then right hand-side. If a re-assignment operator is successfully parsed, then a right
    /// hand-side is expected and will hard fail. If no re-assignment operator is found, then it
    /// should just return the left-hand side.
    #[profiling::function]
    pub(crate) fn parse_expression_with_re_assignment(
        &self,
    ) -> AstGenResult<(AstNode<Expression>, bool)> {
        let lhs = self.parse_expression_with_precedence(0)?;
        let lhs_span = lhs.span();

        // Check if we can parse a merge declaration
        if self.parse_token_fast(TokenKind::Tilde).is_some() {
            return Ok((self.parse_merge_declaration(lhs)?, false));
        }

        let start = self.current_location();
        let (operator, consumed_tokens) = self.parse_binary_operator();

        // Look at the token after the consumed tokens and see if it's an equal sign
        match self.peek_nth(consumed_tokens as usize) {
            Some(token) if operator.is_some() && token.has_kind(TokenKind::Eq) => {
                // consume the number of tokens eaten whilst getting the operator...
                self.offset.update(|x| x + 1 + consumed_tokens as usize);
                let operator = self.node_with_joined_span(operator.unwrap(), &start);

                let rhs = self.parse_expression_with_precedence(0)?;

                // Now we need to transform the re-assignment operator into a function call
                Ok((
                    self.node_with_span(
                        Expression::new(ExpressionKind::AssignOp(AssignOpExpression {
                            lhs,
                            rhs,
                            operator,
                        })),
                        lhs_span,
                    ),
                    false,
                ))
            }
            _ => Ok((lhs, false)),
        }
    }

    /// Parse an single name or a function call that is applied on the left hand side
    /// expression. Infix calls and name are only separated by infix calls having
    /// parenthesees at the end of the name.
    pub(crate) fn parse_name_or_infix_call(&self) -> AstGenResult<AstNode<Expression>> {
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
                        name: self.node_with_span(
                            AccessName {
                                path: ast_nodes![self.node_with_span(*id, *id_span)],
                            },
                            *id_span,
                        ),
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
        tree: &'stream [Token],
        span: &Span,
    ) -> AstGenResult<AstNode<Expression>> {
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

        let parse_block = |initial_offset: usize| -> AstGenResult<AstNode<Expression>> {
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

                let start_pos = expr.span();
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
                                    elements: ast_nodes![entry],
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
                            statements: ast_nodes![statement],
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
        tree: &'stream [Token],
        span: &Span,
    ) -> AstGenResult<AstNode<Expression>> {
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
                            elements: ast_nodes![],
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
            return Ok(entry.into_body().value);
        }

        let mut elements = ast_nodes![entry];

        loop {
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();

                    // Handles the case where this is a trailing comma and no tokens after...
                    if !gen.has_token() {
                        break;
                    }

                    elements.nodes.push(gen.parse_tuple_literal_entry()?)
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
    pub(crate) fn parse_function_def_arg(&self) -> AstGenResult<AstNode<FunctionDefArg>> {
        let name = self.parse_name()?;
        let name_span = name.span();

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
    pub(crate) fn parse_function_definition(
        &self,
        gen: &Self,
    ) -> AstGenResult<AstNode<Expression>> {
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

    /// Function to parse a sequence of top-level [Expression]s from a brace-block exhausting all of the
    /// remaining tokens within the block. This function expects that the next token is a [TokenKind::Tree]
    /// and it will consume it producing [Expression]s from it.
    pub(crate) fn parse_expressions_from_braces(&self) -> AstGenResult<AstNodes<Expression>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            }) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                let mut expressions = vec![];

                // Continue eating the generator until no more tokens are present
                while gen.has_token() {
                    let (_, expr) = gen.parse_top_level_expression(true)?;
                    expressions.push(expr);
                }
                gen.verify_is_empty()?;

                Ok(AstNodes::new(expressions, Some(*span)))
            }
            token => self.error_with_location(
                AstGenErrorKind::Block,
                None,
                token.map(|t| t.kind),
                token.map_or_else(|| self.next_location(), |t| t.span),
            )?,
        }
    }
}
