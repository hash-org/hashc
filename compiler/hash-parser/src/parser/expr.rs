//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_reporting::diagnostic::HasDiagnosticsMut;
use hash_source::location::ByteRange;
use hash_token::{delimiter::Delimiter, keyword::Keyword, IntLitKind, Token, TokenKind};
use hash_utils::thin_vec::thin_vec;

use super::AstGen;
use crate::diagnostics::{
    error::{ParseErrorKind, ParseResult},
    expected::ExpectedItem,
    warning::{ParseWarning, WarningKind},
};

impl AstGen<'_> {
    /// Parse a top level [Expr] that are optionally terminated with a
    /// semi-colon.
    #[profiling::function]
    pub fn parse_top_level_expr(&mut self) -> ParseResult<Option<(bool, AstNode<Expr>)>> {
        let start = self.current_pos();

        // This is used to handle a semi-colon that occurs at the end of
        // an expression...
        let maybe_eat_semi = |this: &mut Self| -> bool {
            if let Some(TokenKind::Semi) = this.peek_kind() {
                this.skip_fast(TokenKind::Semi); // `;`
                true
            } else {
                false
            }
        };

        // If we are starting with a macro invocation, then we have
        // to recurse and re-try parsing the top level expression
        if let Some(macros) = self.parse_macro_invocations(MacroKind::Ast)? {
            let top_level_expr = self.parse_top_level_expr()?;

            return if let Some((_, subject)) = top_level_expr {
                let expr = self.node_with_joined_span(
                    Expr::Macro(ExprMacroInvocation { macros, subject }),
                    start,
                );

                let semi = maybe_eat_semi(self);
                Ok(Some((semi, expr)))
            } else {
                self.err_with_location(
                    ParseErrorKind::ExpectedExpr,
                    ExpectedItem::empty(),
                    None,
                    self.expected_pos(),
                )
            };
        }

        // So here we want to check that the next token(s) could make up a singular
        // pattern which is then followed by a `:` to denote that this is a
        // declaration.
        if self.begins_pat() {
            let pat = self.parse_singular_pat()?;
            self.parse_token(TokenKind::Colon)?;
            let decl = self.parse_declaration(pat)?;

            let expr = self.node_with_joined_span(Expr::Declaration(decl), start);
            let semi = maybe_eat_semi(self);
            return Ok(Some((semi, expr)));
        }

        // Handle trailing semi-colons...
        if let Some(TokenKind::Semi) = self.peek_kind() {
            self.eat_trailing_semis();

            return Ok(None);
        }

        let (expr, re_assigned) = self.parse_expr_with_re_assignment()?;

        let expr = match self.peek_kind() {
            // We don't skip here because it is handled after the statement has been
            // generated.
            Some(TokenKind::Eq) if !re_assigned => {
                self.skip_fast(TokenKind::Eq); // `=`

                // Parse the right hand-side of the assignment
                let rhs = self.parse_expr_with_precedence(0)?;
                self.node_with_joined_span(Expr::Assign(AssignExpr { lhs: expr, rhs }), start)
            }

            // Special case where there is a expression at the end of the stream and
            // therefore it is signifying that it is returning
            // the expression value here
            _ => expr,
        };

        let semi = maybe_eat_semi(self);
        Ok(Some((semi, expr)))
    }

    /// Function to eat a collection of trailing semi-colons.
    pub(crate) fn eat_trailing_semis(&mut self) {
        let tok = self.current_token();

        // Collect any additional trailing semis with the one that was encountered
        while let Some(TokenKind::Semi) = self.peek_kind() {
            self.skip_fast(TokenKind::Semi); // `;`
        }

        // Emit trailing semis diagnostic
        let span = self.make_span(tok.span.join(self.previous_pos()));
        self.add_warning(ParseWarning::new(WarningKind::TrailingSemis(span.len()), span));
    }

    /// Parse an expression which can be compound.
    #[profiling::function]
    pub(crate) fn parse_expr(&mut self) -> ParseResult<AstNode<Expr>> {
        let token = self
            .peek()
            .ok_or_else(|| {
                self.make_err(
                    ParseErrorKind::ExpectedExpr,
                    ExpectedItem::empty(),
                    None,
                    Some(self.expected_pos()),
                )
            })
            .copied()?;

        // Firstly, we have to get the initial part of the expression,
        // and then we can check if there are any additional parts in the
        // forms of either property accesses, indexing or method calls
        let (subject, subject_span) = self.track_span(|this| this.parse_expr_component(token))?;

        self.parse_singular_expr(subject, subject_span)
    }

    fn parse_expr_component(&mut self, token: Token) -> ParseResult<AstNode<Expr>> {
        // ##Note: Each child path is responsible for skipping the current `token`.
        Ok(match token.kind {
            kind if kind.is_unary_op() => return self.parse_unary_expr(token),

            // Handle primitive literals
            kind if kind.is_lit() => {
                let data = self.parse_primitive_lit();
                self.node_with_span(Expr::Lit(LitExpr { data }), token.span)
            }
            TokenKind::Ident(ident) => {
                self.skip_fast(token.kind); // `ident`
                let name = self.node_with_span(Name { ident }, token.span);
                self.node_with_span(Expr::Variable(VariableExpr { name }), token.span)
            }
            TokenKind::Lt => {
                let def = self.parse_implicit_fn_def()?;
                self.node_with_joined_span(Expr::ImplicitFnDef(def), token.span)
            }
            TokenKind::Keyword(Keyword::Struct) => {
                let def = self.parse_struct_def()?;
                self.node_with_joined_span(Expr::StructDef(def), token.span)
            }
            TokenKind::Keyword(Keyword::Enum) => {
                let def = self.parse_enum_def()?;
                self.node_with_joined_span(Expr::EnumDef(def), token.span)
            }
            TokenKind::Keyword(Keyword::Type) => {
                self.skip_fast(token.kind); // `type`
                let ty = self.parse_ty()?;
                self.node_with_joined_span(Expr::Ty(TyExpr { ty }), token.span)
            }
            TokenKind::Keyword(Keyword::Mod) => {
                let def = self.parse_mod_def()?;
                self.node_with_joined_span(Expr::ModDef(def), token.span)
            }
            // Body block.
            TokenKind::Tree(Delimiter::Brace, _) => {
                // Don't need to skip, `parse_block()` will eat it!

                let block = self.parse_block()?;
                self.node_with_joined_span(Expr::Block(BlockExpr { data: block }), token.span)
            }
            // Non-body blocks
            kind if kind.begins_block() => {
                let start = self.current_pos();

                let block = match kind {
                    TokenKind::Keyword(Keyword::For) => self.parse_for_loop()?,
                    TokenKind::Keyword(Keyword::While) => self.parse_while_loop()?,
                    kw @ TokenKind::Keyword(Keyword::Loop) => {
                        self.skip_fast(kw); // `loop`
                        let block = self.parse_block()?;
                        self.node_with_joined_span(
                            Block::Loop(LoopBlock { contents: block }),
                            start,
                        )
                    }
                    TokenKind::Keyword(Keyword::If) => self.parse_if_block()?,
                    TokenKind::Keyword(Keyword::Match) => self.parse_match_block()?,
                    _ => unreachable!(),
                };

                self.node_with_joined_span(Expr::Block(BlockExpr { data: block }), start)
            }
            // Import
            TokenKind::Keyword(Keyword::Import) => self.parse_import()?,

            // Array literal
            TokenKind::Tree(Delimiter::Bracket, _) => self.parse_array_lit()?,

            // Either tuple, function, or nested expression
            TokenKind::Tree(Delimiter::Paren, _) => {
                let offset = self.position();
                self.skip_token();

                // Now here we have to look ahead after the token_tree to see if there is an
                // arrow.
                let has_arrow = self.parse_token_fast(TokenKind::FatArrow).is_some()
                    || self.parse_token_fast(TokenKind::ThinArrow).is_some();

                // Backtrack so that we can re-parse the 'gen' and potentially the arrow.
                self.set_pos(offset);

                match has_arrow {
                    true => self.parse_fn_def()?,
                    false => self.parse_expr_or_tuple()?,
                }
            }
            kw @ TokenKind::Keyword(Keyword::Continue) => {
                self.skip_fast(kw); // `continue`
                self.node_with_span(Expr::Continue(ContinueStatement {}), token.span)
            }
            kw @ TokenKind::Keyword(Keyword::Break) => {
                self.skip_fast(kw); // `break`
                self.node_with_span(Expr::Break(BreakStatement {}), token.span)
            }
            kw @ TokenKind::Keyword(Keyword::Return) => {
                self.skip_fast(kw); // `return`
                let return_expr = match self.peek().copied() {
                    Some(tok) if !tok.has_kind(TokenKind::Semi) => Expr::Return(ReturnStatement {
                        expr: Some(self.parse_expr_with_precedence(0)?),
                    }),
                    _ => Expr::Return(ReturnStatement { expr: None }),
                };

                self.node_with_joined_span(return_expr, token.span)
            }
            kind => {
                return self.err_with_location(
                    ParseErrorKind::ExpectedExpr,
                    ExpectedItem::empty(),
                    Some(kind),
                    token.span,
                )
            }
        })
    }

    /// Parse a [Expr::ImplicitCall]. This function tries to parse `<` delimited
    /// [TyArg]s by using [`parse_ty_args()`].
    ///
    /// If this parsing fails, it could be that this isn't a type function call,
    /// but rather a simple binary expression which uses the `<` operator.
    fn maybe_parse_implicit_call(
        &mut self,
        subject: AstNode<Expr>,
        subject_span: ByteRange,
    ) -> (AstNode<Expr>, bool) {
        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => {
                match self.peek_resultant_fn_mut(|g| g.parse_ty_args(false)) {
                    Some(args) => (
                        self.node_with_joined_span(
                            Expr::ImplicitCall(ImplicitFnCall { subject, args }),
                            subject_span,
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
        let (mut lhs, lhs_span) = self.track_span(|this| this.parse_expr())?;

        loop {
            let op_start = self.current_pos();
            let offset = self.position();
            // this doesn't consider operators that have an 'eq' variant because that is
            // handled at the statement level, since it isn't really a binary
            // operator...
            let (Some(op), consumed_tokens) = self.parse_binary_operator() else {
                break;
            };

            // check if we have higher precedence than the lhs expression...
            let (l_prec, r_prec) = op.infix_binding_power();

            if l_prec < min_prec {
                break;
            }

            // Now skip the consumed tokens...
            self.skip(consumed_tokens);

            // check if the operator here is re-assignable, as in '+=', '/=', if so then we
            // need to stop parsing onwards because this might be an assignable
            // expression... Only perform this check if know prior that the
            // expression is not made of compounded components.
            if op.is_re_assignable() {
                // Check if the next token is a '='
                if self.parse_token_fast(TokenKind::Eq).is_some() {
                    self.set_pos(offset);
                    break;
                }
            }

            let op_span = op_start.join(self.current_pos());

            // if the operator is a non-functional, (e.g. as) we need to perform a different
            // conversion where we transform the AstNode into a
            // different
            if op == BinOp::As {
                let ty = self.parse_ty()?;
                lhs = self.node_with_joined_span(Expr::Cast(CastExpr { expr: lhs, ty }), op_span);

                // since we don't descend, we still need to update the precedence to
                // being `r_prec`.
                min_prec = r_prec;
            } else {
                let rhs = self.parse_expr_with_precedence(r_prec)?;

                //v transform the operator into an `BinaryExpr`
                let operator = self.node_with_span(op, op_span);
                lhs = self.node_with_joined_span(
                    Expr::BinaryExpr(BinaryExpr { lhs, rhs, operator }),
                    lhs_span,
                );
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
        mut subject_span: ByteRange,
    ) -> ParseResult<AstNode<Expr>> {
        // so here we need to peek to see if this is either a index_access, field access
        // or a function call...
        while let Some(token) = self.peek() {
            // if there exists a space between the `subject` and the
            // next fragment of the expression, we treat them as explicitly
            // non-singular expressions.
            if !token.span.is_right_before(subject_span) {
                break;
            }

            subject = match token.kind {
                // Property access or method call
                TokenKind::Dot => self.parse_property_access(subject, subject_span)?,
                TokenKind::Access => self.parse_ns_access(subject, subject_span)?,
                TokenKind::Lt => match self.maybe_parse_implicit_call(subject, subject_span) {
                    (subject, true) => subject,
                    // Essentially break because the type_args failed
                    (subject, false) => return Ok(subject),
                },
                // Array index access syntax: ident[...]
                TokenKind::Tree(Delimiter::Bracket, _) => {
                    let span = token.span;
                    let index_expr = self
                        .in_tree(Delimiter::Bracket, None, |g| g.parse_expr_with_precedence(0))?;

                    self.node_with_joined_span(Expr::Index(IndexExpr { subject, index_expr }), span)
                }
                // Function call
                TokenKind::Tree(Delimiter::Paren, _) => self.parse_call(subject, subject_span)?,
                _ => break,
            };

            // We need to adjust the subject_span so we can compute whether
            // we're still "physically" connected to the end of the expression.
            subject_span = subject_span.join(self.previous_pos())
        }

        Ok(subject)
    }

    /// Parsing module import statement which are in the form of a function
    /// call that have a single argument in the form of a string literal.
    /// The syntax is as follows:
    ///
    /// ```ignore
    /// import("./relative/path/to/module")
    /// ```
    ///
    /// The path argument to imports automatically assumes that the path you
    /// provide is references '.hash' extension file or a directory with a
    /// `index.hash` file contained within the directory.
    pub(crate) fn parse_import(&mut self) -> ParseResult<AstNode<Expr>> {
        self.skip_fast(TokenKind::Keyword(Keyword::Import)); // `import`

        let start = self.current_pos();
        let (path, span) = self.in_tree(Delimiter::Paren, None, |gen| {
            match gen.current_token_and_advance().copied() {
                Some(Token { kind: TokenKind::Str(path), span }) => Ok((path, span)),
                tok => {
                    gen.err(ParseErrorKind::ImportPath, ExpectedItem::empty(), tok.map(|t| t.kind))?
                }
            }
        })?;

        // Attempt to add the module via the resolver
        match self.resolver.resolve_import(path) {
            Ok(source) => {
                let data = self.node_with_joined_span(Import { path, source }, start);
                Ok(self.node_with_joined_span(Expr::Import(ImportExpr { data }), start))
            }
            Err(err) => self.err_with_location(
                ParseErrorKind::ErroneousImport(err),
                ExpectedItem::empty(),
                None,
                span,
            ),
        }
    }

    /// Parse an argument with an expression as the value. An [ExprArg]
    /// can appear in two forms:
    ///
    /// - A named argument which appear in the form of `name = value`
    /// - Just a value for the argument.
    fn parse_arg(&mut self) -> ParseResult<AstNode<ExprArg>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;
        let start = self.current_pos();

        // here we trying to check if this argument is in form of just an expression or
        // if there is a name being assigned here...
        let name = match (self.peek(), self.peek_second()) {
            (
                Some(Token { kind: TokenKind::Ident(_), .. }),
                Some(Token { kind: TokenKind::Eq, .. }),
            ) => {
                let name = self.parse_name()?;
                self.skip_fast(TokenKind::Eq); // `=`

                Some(name)
            }
            _ => None,
        };

        // Now here we expect an expression...
        let value = self.parse_expr_with_precedence(0)?;

        Ok(self.node_with_span(ExprArg { name, value, macros }, start))
    }

    /// Parse a [CallExpr] which accepts the `subject` that the
    /// constructor is being called on.
    pub(crate) fn parse_call(
        &mut self,
        subject: AstNode<Expr>,
        subject_span: ByteRange,
    ) -> ParseResult<AstNode<Expr>> {
        let args = self.in_tree(Delimiter::Paren, None, |gen| {
            Ok(gen.parse_nodes(|g| g.parse_arg(), |g| g.parse_token(TokenKind::Comma)))
        })?;

        Ok(self.node_with_joined_span(Expr::Call(CallExpr { subject, args }), subject_span))
    }

    /// Parses a unary operator or expression modifier followed by a singular
    /// expression. Once the unary operator is picked up, the expression is
    /// parsed given the specific rules of the operator or expression
    /// modifier.
    pub(crate) fn parse_unary_expr(&mut self, token: Token) -> ParseResult<AstNode<Expr>> {
        let start = self.current_pos();

        let expr = match token.kind {
            TokenKind::Star => {
                self.skip_fast(TokenKind::Star); // `*`
                Expr::Deref(DerefExpr { data: self.parse_expr()? })
            }
            TokenKind::Amp => {
                self.skip_fast(TokenKind::Amp); // `&`

                // Check if this reference is raw...
                match self.peek().copied() {
                    Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Raw)) => {
                        self.skip_fast(token.kind); // `raw`

                        // Parse a mutability modifier if any
                        let mutability = self
                            .parse_token_fast(TokenKind::Keyword(Keyword::Mut))
                            .map(|_| self.node_with_span(Mutability::Mutable, self.current_pos()));

                        Expr::Ref(RefExpr {
                            inner_expr: self.parse_expr()?,
                            kind: RefKind::Raw,
                            mutability,
                        })
                    }
                    Some(Token { kind: kw @ TokenKind::Keyword(Keyword::Mut), span }) => {
                        self.skip_fast(kw); // `mut`

                        let inner_expr = self.parse_expr()?;

                        Expr::Ref(RefExpr {
                            inner_expr,
                            kind: RefKind::Raw,
                            mutability: Some(self.node_with_span(Mutability::Mutable, span)),
                        })
                    }
                    _ => Expr::Ref(RefExpr {
                        inner_expr: self.parse_expr()?,
                        kind: RefKind::Normal,
                        mutability: None,
                    }),
                }
            }
            TokenKind::Plus => {
                self.skip_fast(TokenKind::Plus); // `+`
                let start = self.current_pos();
                let inner_expr = self.parse_expr()?;

                // Emit a warning for the unnecessary `+` operator
                self.add_warning(ParseWarning::new(
                    WarningKind::UselessUnaryOperator(inner_expr.body().into()),
                    self.make_span(start.join(self.current_pos())),
                ));

                return Ok(inner_expr);
            }
            kind @ (TokenKind::Minus | TokenKind::Exclamation | TokenKind::Tilde) => {
                self.skip_fast(kind); // `-` | `!` | `~`
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

                Expr::UnaryExpr(UnaryExpr { expr, operator })
            }
            TokenKind::Pound => {
                let macros = self.parse_macro_invocations(MacroKind::Ast)?.unwrap();
                let subject = self.parse_expr()?;
                Expr::Macro(ExprMacroInvocation { macros, subject })
            }
            TokenKind::At => {
                let token_macro = self.parse_token_macro_invocation()?;
                Expr::TokenMacro(token_macro)
            }
            kw @ TokenKind::Keyword(Keyword::Unsafe) => {
                self.skip_fast(kw); // `unsafe`
                let arg = self.parse_expr()?;
                Expr::Unsafe(UnsafeExpr { data: arg })
            }

            kind => panic!("Expected token to be a unary operator, but got '{kind}'"),
        };

        Ok(self.node_with_joined_span(expr, start))
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
    /// some_var: f64 = ...;
    /// ^^^^^^^^  ^^^   ^^^─────┐
    /// pattern   type    the right hand-side expr
    /// ```
    pub(crate) fn parse_declaration(&mut self, pat: AstNode<Pat>) -> ParseResult<Declaration> {
        // Attempt to parse an optional type...
        let ty = match self.peek_kind() {
            Some(TokenKind::Eq) => None,
            _ => Some(self.parse_ty()?),
        };

        // Now parse the initialiser...
        self.parse_token(TokenKind::Eq)?;
        let value = self.parse_expr_with_precedence(0)?;
        Ok(Declaration { pat, ty, value })
    }

    /// Given a initial left-hand side expression, attempt to parse a
    /// re-assignment operator and then right hand-side. If a re-assignment
    /// operator is successfully parsed, then a right hand-side is expected
    /// and will hard fail. If no re-assignment operator is found, then it
    /// should just return the left-hand side.
    #[profiling::function]
    pub(crate) fn parse_expr_with_re_assignment(&mut self) -> ParseResult<(AstNode<Expr>, bool)> {
        let (lhs, lhs_span) = self.track_span(|g| g.parse_expr_with_precedence(0))?;

        let start = self.current_pos();
        let (Some(operator), consumed_tokens) = self.parse_binary_operator() else {
            return Ok((lhs, false));
        };

        let offset = self.position();
        self.skip(consumed_tokens);

        match self.peek_kind() {
            Some(TokenKind::Eq) => {
                self.skip_fast(TokenKind::Eq); // `=`

                let operator = self.node_with_joined_span(operator, start);
                let rhs = self.parse_expr_with_precedence(0)?;

                // Now we need to transform the re-assignment operator into a function call
                Ok((
                    self.node_with_span(
                        Expr::AssignOp(AssignOpExpr { lhs, rhs, operator }),
                        lhs_span,
                    ),
                    false,
                ))
            }
            _ => {
                self.set_pos(offset);
                Ok((lhs, false))
            }
        }
    }

    /// Parse a property access expression, in other words an [AccessExpr] with
    /// the [AccessKind::Property] variant.
    pub(crate) fn parse_property_access(
        &mut self,
        subject: AstNode<Expr>,
        subject_span: ByteRange,
    ) -> ParseResult<AstNode<Expr>> {
        self.skip_fast(TokenKind::Dot); // `.`

        if let Some(token) = self.peek()
            && token.kind.is_numeric()
        {
            // If the next token kind is a integer with no sign, then we can assume
            // that this is a numeric field access, otherwise we can say that
            // `-` was an unexpected token here...
            if let TokenKind::Int(_, kind) = token.kind {
                // Now read the value and verify that it has no numeric prefix
                if let IntLitKind::Suffixed(ty) = kind {
                    return self.err_with_location(
                        ParseErrorKind::DisallowedSuffix(ty.into()),
                        ExpectedItem::empty(),
                        None,
                        token.span,
                    )?;
                }

                self.skip_fast(token.kind); // `int` literal
                let value = self.source.hunk(token.span).parse::<u32>().map_err(|_| {
                    self.make_err(
                        ParseErrorKind::InvalidPropertyAccess,
                        ExpectedItem::empty(),
                        None,
                        Some(token.span),
                    )
                })?;

                let property = self.node_with_span(PropertyKind::NumericField(value), token.span);

                return Ok(self.node_with_joined_span(
                    Expr::Access(AccessExpr { subject, property, kind: AccessKind::Property }),
                    subject_span,
                ));
            }
        }

        let property = self.parse_named_field(ParseErrorKind::ExpectedPropertyAccess)?;
        Ok(self.node_with_joined_span(
            Expr::Access(AccessExpr { subject, property, kind: AccessKind::Property }),
            subject_span,
        ))
    }

    /// Parse a [AccessExpr] with a `namespace` access kind.
    pub(crate) fn parse_ns_access(
        &mut self,
        subject: AstNode<Expr>,
        subject_span: ByteRange,
    ) -> ParseResult<AstNode<Expr>> {
        self.skip_fast(TokenKind::Access); // `::`

        let property = self.parse_named_field(ParseErrorKind::ExpectedName)?;
        Ok(self.node_with_joined_span(
            Expr::Access(AccessExpr { subject, property, kind: AccessKind::Namespace }),
            subject_span,
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
    pub(crate) fn parse_expr_or_tuple(&mut self) -> ParseResult<AstNode<Expr>> {
        self.in_tree(Delimiter::Paren, None, |gen| {
            let start = gen.current_pos();

            // Handle the case if it is an empty stream, this means that if it failed to
            // parse a function in the form of `() => ...` for whatever reason, then it
            // is trying to parse either a tuple or an expression.
            // Handle the empty tuple case
            if gen.len() < 2 {
                let elements = gen.nodes_with_span(thin_vec![], start);
                let tuple = gen.node_with_joined_span(Expr::Tuple(TupleExpr { elements }), start);

                match gen.peek_kind() {
                    Some(TokenKind::Comma) => {
                        gen.skip_fast(TokenKind::Comma); // ','

                        return Ok(tuple);
                    }
                    None => {
                        return Ok(tuple);
                    }
                    _ => (),
                };
            }

            let entry = gen.parse_tuple_arg()?;

            // In the special case where this is just an expression that is wrapped within
            // parentheses, we can check that the 'name' and 'ty' parameters are
            // set to `None` and that there are no extra tokens that are left within
            // the token tree...
            if entry.name.is_none() && !gen.has_token() {
                let expr = entry.into_body().value;

                // We want to emit a redundant parentheses warning if it is not a binary-like
                // expression since it does not affect the precedence...
                if !matches!(
                    expr.body(),
                    Expr::BinaryExpr(_) | Expr::Cast(_) | Expr::FnDef(_) | Expr::Deref(_)
                ) {
                    gen.add_warning(ParseWarning::new(
                        WarningKind::RedundantParenthesis(expr.body().into()),
                        gen.make_span(gen.range()),
                    ));
                }

                return Ok(expr);
            }

            let mut elements = thin_vec![entry];

            loop {
                match gen.peek() {
                    Some(token) if token.has_kind(TokenKind::Comma) => {
                        gen.skip_fast(TokenKind::Comma); // ','

                        // Handles the case where this is a trailing comma and no tokens after...
                        if !gen.has_token() {
                            break;
                        }

                        elements.push(gen.parse_tuple_arg()?)
                    }
                    Some(token) => gen.err_with_location(
                        ParseErrorKind::ExpectedExpr,
                        ExpectedItem::Comma,
                        Some(token.kind),
                        token.span,
                    )?,
                    None => break,
                }
            }

            let span = gen.range();
            let elements = gen.nodes_with_span(elements, span);
            Ok(gen.node_with_span(Expr::Tuple(TupleExpr { elements }), span))
        })
    }

    /// Parse a [FnDef]. Function literals are essentially definitions
    /// of lambdas that can be assigned to variables or passed as arguments
    /// into other functions.
    pub(crate) fn parse_fn_def(&mut self) -> ParseResult<AstNode<Expr>> {
        // parse function definition parameters.
        let start = self.current_pos();
        let params = self.parse_params(ParamOrigin::Fn)?;

        // check if there is a return type
        let return_ty = match self.peek_resultant_fn(|g| g.parse_token(TokenKind::ThinArrow)) {
            Some(_) => Some(self.parse_ty()?),
            _ => None,
        };

        self.parse_token(TokenKind::FatArrow)?;

        let fn_body = match self.peek() {
            Some(_) => self.parse_expr_with_precedence(0)?,
            None => self.err(ParseErrorKind::ExpectedFnBody, ExpectedItem::empty(), None)?,
        };

        Ok(self.node_with_joined_span(Expr::FnDef(FnDef { params, return_ty, fn_body }), start))
    }

    /// Function to parse a sequence of top-level [Expr]s from the current
    /// context.
    pub(crate) fn parse_exprs_from_brace_tree(&mut self) -> ParseResult<AstNodes<Expr>> {
        self.in_tree(Delimiter::Brace, Some(ParseErrorKind::ExpectedBlock), |gen| {
            let mut exprs = thin_vec![];

            // Continue eating the generator until no more tokens are present
            //
            // @@ErrorRecovery: don't bail immediately...
            while gen.has_token() {
                if let Some((_, expr)) = gen.parse_top_level_expr()? {
                    exprs.push(expr);
                }
            }

            Ok(gen.nodes_with_span(exprs, gen.range()))
        })
    }
}
