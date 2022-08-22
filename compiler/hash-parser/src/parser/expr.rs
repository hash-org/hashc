//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use std::{path::PathBuf, str::FromStr};

use hash_ast::{ast::*, ast_nodes};
use hash_reporting::diagnostic::Diagnostics;
use hash_source::{constant::CONSTANT_MAP, location::Span};
use hash_token::{delimiter::Delimiter, keyword::Keyword, Sign, Token, TokenKind, TokenKindVector};
use smallvec::smallvec;

use super::AstGen;
use crate::diagnostics::{
    error::{ParseErrorKind, ParseResult},
    warning::{ParseWarning, WarningKind},
};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a top level [Expr] that are terminated with a semi-colon.
    #[profiling::function]
    pub fn parse_top_level_expr(
        &mut self,
        semi_required: bool,
    ) -> ParseResult<(bool, AstNode<Expr>)> {
        let start = self.next_location();

        // So here we want to check that the next token(s) could make up a singular
        // pattern which is then followed by a `:` to denote that this is a
        // declaration.
        let decl = match self.begins_pat() {
            true => {
                let pat = self.parse_singular_pat()?;

                self.parse_token(TokenKind::Colon)?;

                let decl = self.parse_declaration(pat)?;

                Some(self.node_with_span(Expr::new(ExprKind::Declaration(decl)), start))
            }
            false => None,
        };

        let expr = match decl {
            Some(statement) => Ok(statement),
            None => {
                let (expr, re_assigned) = self.parse_expr_with_re_assignment()?;

                if re_assigned {
                    Ok(expr)
                } else {
                    match self.peek() {
                        // We don't skip here because it is handled after the statement has been
                        // generated.
                        Some(token) if token.has_kind(TokenKind::Semi) => Ok(expr),
                        Some(token) if token.has_kind(TokenKind::Eq) => {
                            self.skip_token();

                            // Parse the right hand-side of the assignment
                            let rhs = self.parse_expr_with_precedence(0)?;

                            Ok(self.node_with_joined_span(
                                Expr::new(ExprKind::Assign(AssignExpr { lhs: expr, rhs })),
                                start,
                            ))
                        }
                        Some(token) => self.err_with_location(
                            ParseErrorKind::ExpectedOperator,
                            Some(TokenKindVector::from_vec(smallvec![
                                TokenKind::Dot,
                                TokenKind::Eq,
                                TokenKind::Semi,
                            ])),
                            Some(token.kind),
                            self.next_location(),
                        ),
                        // Special case where there is a expression at the end of the stream and
                        // therefore it is signifying that it is returning
                        // the expression value here
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
    pub(crate) fn parse_expr(&mut self) -> ParseResult<AstNode<Expr>> {
        let token = self
            .next_token()
            .ok_or_else(|| {
                self.make_err(ParseErrorKind::ExpectedExpr, None, None, Some(self.next_location()))
            })
            .copied()?;

        // Firstly, we have to get the initial part of the expression,
        // and then we can check if there are any additional parts in the
        // forms of either property accesses, indexing or method calls
        let subject = match token.kind {
            kind if kind.is_unary_op() => return self.parse_unary_expr(),

            // Handle primitive literals
            kind if kind.is_lit() => self.node_with_span(
                Expr::new(ExprKind::LitExpr(LitExpr(self.parse_primitive_lit()?))),
                token.span,
            ),
            TokenKind::Ident(ident) => {
                // Create the variable expr
                self.node_with_span(
                    Expr::new(ExprKind::Variable(VariableExpr {
                        name: self.node_with_span(Name { ident }, token.span),
                    })),
                    token.span,
                )
            }
            TokenKind::Lt => {
                let def = self.parse_ty_fn_def()?;
                self.node_with_joined_span(Expr::new(ExprKind::TyFnDef(def)), token.span)
            }
            TokenKind::Keyword(Keyword::Struct) => {
                let def = self.parse_struct_def()?;
                self.node_with_joined_span(Expr::new(ExprKind::StructDef(def)), token.span)
            }
            TokenKind::Keyword(Keyword::Enum) => {
                let def = self.parse_enum_def()?;
                self.node_with_joined_span(Expr::new(ExprKind::EnumDef(def)), token.span)
            }
            TokenKind::Keyword(Keyword::Trait) => {
                let def = self.parse_trait_def()?;
                self.node_with_joined_span(Expr::new(ExprKind::TraitDef(def)), token.span)
            }
            TokenKind::Keyword(Keyword::Type) => {
                let ty = self.parse_type()?;
                self.node_with_joined_span(Expr::new(ExprKind::Ty(TyExpr(ty))), token.span)
            }
            TokenKind::Keyword(Keyword::Set) => {
                let lit = self.parse_set_lit()?;
                self.node_with_joined_span(Expr::new(ExprKind::LitExpr(LitExpr(lit))), token.span)
            }
            TokenKind::Keyword(Keyword::Map) => {
                let lit = self.parse_map_lit()?;
                self.node_with_joined_span(Expr::new(ExprKind::LitExpr(LitExpr(lit))), token.span)
            }
            TokenKind::Keyword(Keyword::Impl)
                if self.peek().map_or(false, |tok| !tok.is_brace_tree()) =>
            {
                let ty = self.parse_type()?;
                let implementation = self.parse_exprs_from_braces()?;

                self.node_with_joined_span(
                    Expr::new(ExprKind::TraitImpl(TraitImpl { ty, implementation })),
                    token.span,
                )
            }
            // Body block.
            TokenKind::Tree(Delimiter::Brace, _) => {
                // @@Hack: we need to backtrack a single token so that `parse_block` can be
                // used.
                self.offset.set(self.offset.get() - 1);

                let block = self.parse_block()?;

                self.node_with_joined_span(Expr::new(ExprKind::Block(BlockExpr(block))), token.span)
            }
            // Non-body blocks
            kind if kind.begins_block() => {
                let start = self.current_location();

                let block = match kind {
                    TokenKind::Keyword(Keyword::For) => self.parse_for_loop()?,
                    TokenKind::Keyword(Keyword::While) => self.parse_while_loop()?,
                    TokenKind::Keyword(Keyword::Loop) => {
                        let block = self.parse_block()?;
                        self.node_with_joined_span(Block::Loop(LoopBlock(block)), start)
                    }
                    TokenKind::Keyword(Keyword::If) => self.parse_if_block()?,
                    TokenKind::Keyword(Keyword::Match) => self.parse_match_block()?,
                    TokenKind::Keyword(Keyword::Mod) => {
                        let block = self.parse_body_block()?;
                        self.node_with_joined_span(Block::Mod(ModBlock(block)), start)
                    }
                    TokenKind::Keyword(Keyword::Impl) => {
                        let block = self.parse_body_block()?;
                        self.node_with_joined_span(Block::Impl(ImplBlock(block)), start)
                    }
                    _ => unreachable!(),
                };

                self.node_with_joined_span(Expr::new(ExprKind::Block(BlockExpr(block))), start)
            }
            // Import
            TokenKind::Keyword(Keyword::Import) => self.parse_import()?,

            // List literal
            TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                let tree = self.token_trees.get(tree_index as usize).unwrap();
                self.parse_list_lit(tree, token.span)?
            }

            // Either tuple, function, or nested expression
            TokenKind::Tree(Delimiter::Paren, tree_index) => {
                let mut is_func = false;

                // Now here we have to look ahead after the token_tree to see if there is an
                // arrow @@Speed: avoid using parse_token_atom() because we
                // don't care about error messages          We just want to
                // purely look if there are is a combination of symbols following
                //          which make up an '=>'.
                let has_arrow = self
                    .peek_resultant_fn(|g| -> Result<(), ()> {
                        match g.peek() {
                            Some(token)
                                if token.has_kind(TokenKind::Minus)
                                    || token.has_kind(TokenKind::Eq) =>
                            {
                                g.skip_token();
                                g.parse_token_fast(TokenKind::Gt).ok_or(())?;
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

                let tree = self.token_trees.get(tree_index as usize).unwrap();

                match is_func {
                    true => {
                        let gen = self.from_stream(tree, token.span);
                        self.parse_fn_def(gen)?
                    }
                    false => self.parse_expr_or_tuple(tree, self.current_location())?,
                }
            }
            TokenKind::Keyword(Keyword::Continue) => {
                self.node_with_span(Expr::new(ExprKind::Continue(ContinueStatement)), token.span)
            }
            TokenKind::Keyword(Keyword::Break) => {
                self.node_with_span(Expr::new(ExprKind::Break(BreakStatement)), token.span)
            }
            TokenKind::Keyword(Keyword::Return) => {
                // @@Hack: check if the next token is a semi-colon, if so the return statement
                // has no returned expression...
                let return_expr = match self.peek().copied() {
                    Some(token) if token.has_kind(TokenKind::Semi) => {
                        ExprKind::Return(ReturnStatement(None))
                    }
                    Some(_) => {
                        ExprKind::Return(ReturnStatement(Some(self.parse_expr_with_precedence(0)?)))
                    }
                    None => ExprKind::Return(ReturnStatement(None)),
                };

                self.node_with_joined_span(Expr::new(return_expr), token.span)
            }
            kind @ TokenKind::Keyword(_) => {
                return self.err_with_location(
                    ParseErrorKind::Keyword,
                    None,
                    Some(kind),
                    token.span,
                )
            }
            kind => {
                return self.err_with_location(
                    ParseErrorKind::ExpectedExpr,
                    None,
                    Some(kind),
                    token.span,
                )
            }
        };

        self.parse_singular_expr(subject)
    }

    /// Parse a [TyFnCall] wrapped within a [TyExpr]. This function tries to
    /// parse `type_args` by using `parse_type_args`. If this parsing fails,
    /// it could be that this isn't a type function call, but rather a
    /// simple binary expression which uses the `<` operator.
    fn maybe_parse_type_fn_call(&mut self, subject: AstNode<Expr>) -> (AstNode<Expr>, bool) {
        let span = subject.span();

        // @@Speed: so here we want to be efficient about type_args, we'll just try to
        // see if the next token atom is a 'Lt' rather than using parse_token_atom
        // because it throws an error essentially and thus allocates a stupid amount
        // of strings which at the end of the day aren't even used...
        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => {
                match self.peek_resultant_fn_mut(|g| g.parse_ty_args(false)) {
                    Some(args) => (
                        self.node_with_joined_span(
                            Expr::new(ExprKind::Ty(TyExpr(self.node_with_joined_span(
                                Ty::TyFnCall(TyFnCall { subject, args }),
                                span,
                            )))),
                            span,
                        ),
                        true,
                    ),
                    None => (subject, false),
                }
            }
            _ => (subject, false),
        }
    }

    /// Parse an expression whilst taking into account binary precedence
    /// operators. Parse chain of expressions with chain links being binary
    /// operators. Whilst parsing the chain, figure out the applicative
    /// precedence of each operator using Pratt parsing.
    pub(crate) fn parse_expr_with_precedence(
        &mut self,
        mut min_prec: u8,
    ) -> ParseResult<AstNode<Expr>> {
        // first of all, we want to get the lhs...
        let mut lhs = self.parse_expr()?;
        let lhs_span = lhs.span();

        // reset the compound_expr flag, since this is a new expression...
        self.is_compound_expr.set(false);

        loop {
            let op_start = self.next_location();
            // this doesn't consider operators that have an 'eq' variant because that is
            // handled at the statement level, since it isn't really a binary
            // operator...
            let (op, consumed_tokens) = self.parse_binary_operator();

            // We want to break if it's an operator and it is wanting to re-assign
            if op.is_some_and(|op| op.is_re_assignable())
                && matches!(self.peek_nth(consumed_tokens as usize), Some(token) if token.has_kind(TokenKind::Eq))
            {
                break;
            }

            match op {
                // check if the operator here is re-assignable, as in '+=', '/=', if so then we need
                // to stop parsing onwards because this might be an assignable
                // expression... Only perform this check if know prior that the
                // expression is not made of compounded components.
                Some(op) => {
                    // check if we have higher precedence than the lhs expression...
                    let (l_prec, r_prec) = op.infix_binding_power();

                    if l_prec < min_prec {
                        break;
                    }

                    self.offset.update(|x| x + consumed_tokens as usize);
                    let op_span = op_start.join(self.current_location());

                    // if the operator is a non-functional, (e.g. as) we need to perform a different
                    // conversion where we transform the AstNode into a
                    // different
                    if op == BinOp::As {
                        let ty = self.parse_type()?;
                        lhs = self.node_with_joined_span(
                            Expr::new(ExprKind::Cast(CastExpr { expr: lhs, ty })),
                            op_span,
                        );

                        // since we don't descend, we still need to update the precedence to
                        // being `r_prec`.
                        min_prec = r_prec;
                    } else {
                        let rhs = self.parse_expr_with_precedence(r_prec)?;
                        self.is_compound_expr.set(true);

                        //v transform the operator into an `BinaryExpr`
                        lhs = self.node_with_joined_span(
                            Expr::new(ExprKind::BinaryExpr(BinaryExpr {
                                lhs,
                                rhs,
                                operator: self.node_with_span(op, op_span),
                            })),
                            lhs_span,
                        );
                    }
                }
                _ => break,
            }
        }

        Ok(lhs)
    }

    /// Provided an initial subject expression that is parsed by the parent
    /// caller, this function will check if there are any additional
    /// components to the expression; in the form of either property access,
    /// method calls, indexing, etc.
    pub(crate) fn parse_singular_expr(
        &mut self,
        mut subject: AstNode<Expr>,
    ) -> ParseResult<AstNode<Expr>> {
        // so here we need to peek to see if this is either a index_access, field access
        // or a function call...
        while let Some(token) = self.peek() {
            subject = match token.kind {
                // Property access or method call
                TokenKind::Dot => {
                    self.skip_token();
                    self.parse_property_access(subject)?
                }
                TokenKind::Colon if matches!(self.peek_second(), Some(token) if token.has_kind(TokenKind::Colon)) =>
                {
                    self.offset.update(|offset| offset + 2);
                    self.parse_ns_access(subject)?
                }
                TokenKind::Lt => match self.maybe_parse_type_fn_call(subject) {
                    (subject, true) => subject,
                    // Essentially break because the type_args failed
                    (subject, false) => return Ok(subject),
                },
                // Array index access syntax: ident[...]
                TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                    self.skip_token();

                    let tree = self.token_trees.get(tree_index as usize).unwrap();
                    self.parse_array_index(subject, tree, self.current_location())?
                }
                // Function call
                TokenKind::Tree(Delimiter::Paren, tree_index) => {
                    self.skip_token();

                    let tree = self.token_trees.get(tree_index as usize).unwrap();
                    self.parse_constructor_call(subject, tree, self.current_location())?
                }
                _ => break,
            }
        }

        Ok(subject)
    }

    /// Parsing module import statement which are in the form of a function
    /// call that have a single argument in the form of a string literal.
    /// The syntax is as follows:
    ///
    /// import("./relative/path/to/module")
    ///
    /// The path argument to imports automatically assumes that the path you
    /// provide is references '.hash' extension file or a directory with a
    /// 'index.hash' file contained within the directory.
    pub(crate) fn parse_import(&self) -> ParseResult<AstNode<Expr>> {
        let pre = self.current_token().span;
        let start = self.current_location();

        let gen = self.parse_delim_tree(Delimiter::Paren, None)?;

        let (raw, path, span) = match gen.peek() {
            Some(Token { kind: TokenKind::StrLit(str), span }) => (str, *str, span),
            _ => gen.err(ParseErrorKind::ImportPath, None, None)?,
        };

        gen.skip_token(); // eat the string argument

        // @@ErrorRecovery: it would be quite easy to implement error recovery, but is
        // it the right thing to do here, assuming that imports could be changed in the
        // future, we might want to bail early since more tokens may change the queried
        // import.
        if gen.has_token() {
            return gen.expected_eof();
        }

        // Attempt to add the module via the resolver
        let import_path = PathBuf::from_str(path.into()).unwrap();
        let resolved_import_path =
            self.resolver.resolve_import(&import_path, self.source_location(span));

        match resolved_import_path {
            Ok(resolved_import_path) => Ok(self.node_with_joined_span(
                Expr::new(ExprKind::Import(ImportExpr(self.node_with_joined_span(
                    Import { path: *raw, resolved_path: resolved_import_path },
                    start,
                )))),
                start,
            )),
            Err(err) => self.err_with_location(
                ParseErrorKind::ErroneousImport(err),
                None,
                None,
                pre.join(self.current_location()),
            ),
        }
    }

    /// Parse a [ConstructorCallExpr] which accepts the `subject` that the
    /// constructor is being called on.
    pub(crate) fn parse_constructor_call(
        &mut self,
        subject: AstNode<Expr>,
        tree: &'stream [Token],
        span: Span,
    ) -> ParseResult<AstNode<Expr>> {
        let mut gen = self.from_stream(tree, span);
        let mut args = vec![];

        while gen.has_token() {
            let start = gen.next_location();

            // here we trying to check if this argument is in form of just an expression or
            // if there is a name being assigned here...
            let name = match (gen.peek(), gen.peek_second()) {
                (
                    Some(Token { kind: TokenKind::Ident(_), .. }),
                    Some(Token { kind: TokenKind::Eq, .. }),
                ) => {
                    let name = gen.parse_name()?;
                    gen.skip_token(); // '='

                    Some(name)
                }
                _ => None,
            };

            // Now here we expect an expression...
            let value = gen.parse_expr_with_precedence(0)?;

            args.push(gen.node_with_span(ConstructorCallArg { name, value }, start));

            // now we eat the next token, checking that it is a comma
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                Some(token) => gen.err_with_location(
                    ParseErrorKind::Expected,
                    Some(TokenKindVector::singleton(TokenKind::Comma)),
                    Some(token.kind),
                    token.span,
                )?,
                None => break,
            };
        }
        self.consume_gen(gen);

        let subject_span = subject.span();

        Ok(self.node_with_joined_span(
            Expr::new(ExprKind::ConstructorCall(ConstructorCallExpr {
                subject,
                args: AstNodes::new(args, Some(span)),
            })),
            subject_span,
        ))
    }

    /// Parse an array index. Array indexes are constructed with square brackets
    /// wrapping a singular expression.
    pub(crate) fn parse_array_index(
        &mut self,
        subject: AstNode<Expr>,
        tree: &'stream [Token],
        span: Span,
    ) -> ParseResult<AstNode<Expr>> {
        let mut gen = self.from_stream(tree, span);
        let start = gen.current_location();

        // parse the indexing expression between the square brackets...
        let index_expr = gen.parse_expr_with_precedence(0)?;

        // @@ErrorRecovery: Investigate introducing `Err` variant into expressions...
        //
        // since nothing should be after the expression, we can check that no tokens
        // are left and the generator is empty, otherwise report this as an
        // unexpected_token
        self.consume_gen(gen);

        Ok(self.node_with_joined_span(
            Expr::new(ExprKind::Index(IndexExpr { subject, index_expr })),
            start,
        ))
    }

    /// Parses a unary operator or expression modifier followed by a singular
    /// expression. Once the unary operator is picked up, the expression is
    /// parsed given the specific rules of the operator or expression
    /// modifier.
    pub(crate) fn parse_unary_expr(&mut self) -> ParseResult<AstNode<Expr>> {
        let token = *self.current_token();
        let start = self.current_location();

        let expr_kind = match &token.kind {
            TokenKind::Star => ExprKind::Deref(DerefExpr(self.parse_expr()?)),
            TokenKind::Amp => {
                // Check if this reference is raw...
                match self.peek().copied() {
                    Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Raw)) => {
                        self.skip_token();

                        // Parse a mutability modifier if any
                        let mutability =
                            self.parse_token_fast(TokenKind::Keyword(Keyword::Mut)).map(|_| {
                                self.node_with_span(Mutability::Mutable, self.current_location())
                            });

                        ExprKind::Ref(RefExpr {
                            inner_expr: self.parse_expr()?,
                            kind: RefKind::Raw,
                            mutability,
                        })
                    }
                    Some(Token { kind: TokenKind::Keyword(Keyword::Mut), span }) => {
                        self.skip_token();

                        let inner_expr = self.parse_expr()?;

                        ExprKind::Ref(RefExpr {
                            inner_expr,
                            kind: RefKind::Raw,
                            mutability: Some(self.node_with_span(Mutability::Mutable, span)),
                        })
                    }
                    _ => ExprKind::Ref(RefExpr {
                        inner_expr: self.parse_expr()?,
                        kind: RefKind::Normal,
                        mutability: None,
                    }),
                }
            }
            TokenKind::Plus => {
                let inner_expr = self.parse_expr()?;

                // Emit a warning for the unnecessary `+` operator
                self.add_warning(ParseWarning::new(
                    WarningKind::UselessUnaryOperator(inner_expr.kind().into()),
                    inner_expr.span(),
                ));

                return Ok(inner_expr);
            }
            kind @ (TokenKind::Minus | TokenKind::Exclamation | TokenKind::Tilde) => {
                let expr = self.parse_expr()?;

                let operator = self.node_with_span(
                    match kind {
                        TokenKind::Minus => UnOp::Neg,
                        TokenKind::Exclamation => UnOp::Not,
                        TokenKind::Tilde => UnOp::BitNot,
                        _ => unreachable!(),
                    },
                    start,
                );

                ExprKind::UnaryExpr(UnaryExpr { expr, operator })
            }
            TokenKind::Hash => {
                // First get the directive subject, and expect a possible singular expression
                // followed by the directive.
                let name = self.parse_name()?;
                let subject = self.parse_expr()?;

                // create the subject node
                return Ok(self.node_with_joined_span(
                    Expr::new(ExprKind::Directive(DirectiveExpr { name, subject })),
                    start,
                ));
            }
            TokenKind::Keyword(Keyword::Unsafe) => {
                let arg = self.parse_expr()?;
                ExprKind::Unsafe(UnsafeExpr(arg))
            }
            kind => panic!("Expected token to be a unary operator, but got '{}'", kind),
        };

        Ok(self.node_with_joined_span(Expr::new(expr_kind), start))
    }

    /// Parse a declaration.
    ///
    /// A declaration is either a variable declaration, function declaration, or
    /// both. As such a name is returned before parsing a type, function, or
    /// both. A destructuring pattern, potential for-all statement, optional
    /// type definition and a potential definition of the right hand side. For
    /// example:
    ///
    /// ```text
    /// some_var: float = ...;
    /// ^^^^^^^^  ^^^^^   ^^^─────┐
    /// pattern    type    the right hand-side expr
    /// ```
    pub(crate) fn parse_declaration(&mut self, pattern: AstNode<Pat>) -> ParseResult<Declaration> {
        // Attempt to parse an optional type...
        let ty = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Eq) => None,
            _ => Some(self.parse_type()?),
        };

        // Now parse the value after the assignment
        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Eq) => {
                self.skip_token();

                let value = self.parse_expr_with_precedence(0)?;
                Ok(Declaration { pat: pattern, ty, value: Some(value) })
            }
            _ => Ok(Declaration { pat: pattern, ty, value: None }),
        }
    }

    /// Function to pass a [MergeDeclaration] which is a pattern on the
    /// right-hand side followed by the `~=` operator and then an expression
    /// (which should be either a [ImplBlock] or a [TraitImpl]).
    pub(crate) fn parse_merge_declaration(
        &mut self,
        decl: AstNode<Expr>,
    ) -> ParseResult<AstNode<Expr>> {
        self.parse_token(TokenKind::Eq)?;
        let value = self.parse_expr_with_precedence(0)?;
        let decl_span = decl.span();

        Ok(self.node_with_joined_span(
            Expr::new(ExprKind::MergeDeclaration(MergeDeclaration { decl, value })),
            decl_span,
        ))
    }

    /// Given a initial left-hand side expression, attempt to parse a
    /// re-assignment operator and then right hand-side. If a re-assignment
    /// operator is successfully parsed, then a right hand-side is expected
    /// and will hard fail. If no re-assignment operator is found, then it
    /// should just return the left-hand side.
    #[profiling::function]
    pub(crate) fn parse_expr_with_re_assignment(&mut self) -> ParseResult<(AstNode<Expr>, bool)> {
        let lhs = self.parse_expr_with_precedence(0)?;
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
                let operator = self.node_with_joined_span(operator.unwrap(), start);

                let rhs = self.parse_expr_with_precedence(0)?;

                // Now we need to transform the re-assignment operator into a function call
                Ok((
                    self.node_with_span(
                        Expr::new(ExprKind::AssignOp(AssignOpExpr { lhs, rhs, operator })),
                        lhs_span,
                    ),
                    false,
                ))
            }
            _ => Ok((lhs, false)),
        }
    }

    /// Parse a property access expression, in other words an [AccessExpr] with
    /// the [AccessKind::Property] variant.
    pub(crate) fn parse_property_access(
        &self,
        subject: AstNode<Expr>,
    ) -> ParseResult<AstNode<Expr>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Dot));
        let span = subject.span();

        Ok(self.node_with_joined_span(
            Expr::new(ExprKind::Access(AccessExpr {
                subject,
                property: self.parse_name_with_error(ParseErrorKind::ExpectedPropertyAccess)?,
                kind: AccessKind::Property,
            })),
            span,
        ))
    }

    /// Parse a [AccessExpr] with a `namespace` access kind.
    pub(crate) fn parse_ns_access(&self, subject: AstNode<Expr>) -> ParseResult<AstNode<Expr>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Colon));
        let span = subject.span();

        Ok(self.node_with_joined_span(
            Expr::new(ExprKind::Access(AccessExpr {
                subject,
                property: self.parse_name()?,
                kind: AccessKind::Namespace,
            })),
            span,
        ))
    }

    /// Function to either parse an expression that is wrapped in parentheses or
    /// a tuple literal. If this is a tuple literal, the first expression
    /// must be followed by a comma separator, after that the comma
    /// after the expression is optional.
    ///
    ///
    /// Tuples have a familiar syntax with many other languages, but exhibit two
    /// distinct differences between the common syntax. These differences
    /// are:
    ///
    /// - Empty tuples: (,)
    /// - Singleton tuple : (A,)
    /// - Many membered tuple: (A, B, C) or (A, B, C,)
    pub(crate) fn parse_expr_or_tuple(
        &mut self,
        tree: &'stream [Token],
        span: Span,
    ) -> ParseResult<AstNode<Expr>> {
        let mut gen = self.from_stream(tree, span);
        let start = self.current_location();

        // Handle the case if it is an empty stream, this means that if it failed to
        // parse a function in the form of `() => ...` for whatever reason, then it
        // is trying to parse either a tuple or an expression.
        // Handle the empty tuple case
        if gen.stream.len() < 2 {
            let tuple = gen.node_with_joined_span(
                Expr::new(ExprKind::LitExpr(LitExpr(gen.node_with_joined_span(
                    Lit::Tuple(TupleLit { elements: ast_nodes![] }),
                    start,
                )))),
                start,
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

        let entry = gen.parse_tuple_lit_entry()?;

        // In the special case where this is just an expression that is wrapped within
        // parentheses, we can check that the 'name' and 'ty' parameters are
        // set to `None` and that there are no extra tokens that are left within
        // the token tree...
        if entry.ty.is_none() && entry.name.is_none() && !gen.has_token() {
            let expr = entry.into_body().value;

            // We want to emit a redundant parentheses warning if it is not a binary-like
            // expression since it does not affect the precedence...
            if !matches!(expr.kind(), ExprKind::BinaryExpr(_) | ExprKind::Cast(_)) {
                self.add_warning(ParseWarning::new(
                    WarningKind::RedundantParenthesis(expr.kind().into()),
                    expr.span(),
                ));
            }

            return Ok(expr);
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

                    elements.nodes.push(gen.parse_tuple_lit_entry()?)
                }
                Some(token) => gen.err_with_location(
                    ParseErrorKind::ExpectedExpr,
                    None,
                    Some(token.kind),
                    token.span,
                )?,
                None => break,
            }
        }

        Ok(gen.node_with_joined_span(
            Expr::new(ExprKind::LitExpr(LitExpr(
                gen.node_with_joined_span(Lit::Tuple(TupleLit { elements }), start),
            ))),
            start,
        ))
    }

    /// Parse a function definition argument, which is made of an identifier and
    /// a function type.
    pub(crate) fn parse_fn_def_param(&mut self) -> ParseResult<AstNode<Param>> {
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
                Some(self.parse_expr_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(self
            .node_with_joined_span(Param { name, ty, default, origin: ParamOrigin::Fn }, name_span))
    }

    /// Parse a [FnDef]. Function literals are essentially definitions
    /// of lambdas that can be assigned to variables or passed as arguments
    /// into other functions.
    pub(crate) fn parse_fn_def(&mut self, mut gen: Self) -> ParseResult<AstNode<Expr>> {
        let start = self.current_location();

        // parse function definition parameters.
        let params =
            gen.parse_separated_fn(|g| g.parse_fn_def_param(), |g| g.parse_token(TokenKind::Comma));
        self.consume_gen(gen);

        // check if there is a return type
        let return_ty = match self.peek_resultant_fn(|g| g.parse_thin_arrow()) {
            Some(_) => Some(self.parse_type()?),
            _ => None,
        };

        self.parse_arrow()?;

        let fn_body = match self.peek() {
            Some(_) => self.parse_expr_with_precedence(0)?,
            None => self.err(ParseErrorKind::ExpectedFnBody, None, None)?,
        };

        Ok(self.node_with_joined_span(
            Expr::new(ExprKind::FnDef(FnDef { params, return_ty, fn_body })),
            start,
        ))
    }

    /// Function to parse a sequence of top-level [Expr]s from a
    /// brace-block exhausting all of the remaining tokens within the block.
    /// This function expects that the next token is a [TokenKind::Tree] and
    /// it will consume it producing [Expr]s from it.
    pub(crate) fn parse_exprs_from_braces(&mut self) -> ParseResult<AstNodes<Expr>> {
        let mut gen = self.parse_delim_tree(Delimiter::Brace, Some(ParseErrorKind::Block))?;

        let mut exprs = vec![];

        // Continue eating the generator until no more tokens are present
        //
        // @@ErrorRecovery: don't bail immediately...
        while gen.has_token() {
            let (_, expr) = gen.parse_top_level_expr(true)?;
            exprs.push(expr);
        }

        let span = gen.parent_span;
        self.consume_gen(gen);

        Ok(AstNodes::new(exprs, span))
    }
}
