//! Parsing code for various kind of macros.

use hash_ast::ast::{
    AstNode, AstNodes, MacroInvocation, MacroInvocationArg, MacroInvocationArgs, MacroInvocations,
    MacroKind, Name, TokenMacro, TokenMacroInvocation, TokenStream,
};
use hash_token::{delimiter::Delimiter, Token, TokenKind};
use hash_utils::thin_vec::{thin_vec, ThinVec};

use super::AstGen;
use crate::diagnostics::{
    error::{ParseErrorKind, ParseResult},
    expected::ExpectedItem,
};

impl AstGen<'_> {
    /// Parse a macro prefix character, which depending on [MacroKind] is either
    /// a `#` or a `@`.
    ///
    /// **Note**: This function will consume the token if it is a macro prefix,
    /// otherwise it will not consume the token.
    fn parse_macro_prefix(&self, kind: MacroKind) -> Option<()> {
        self.parse_token_fast(match kind {
            MacroKind::Token => TokenKind::At,
            MacroKind::Ast => TokenKind::Pound,
        })
    }

    /// Parse a macro argument, which has the same syntax as a standard
    /// argument. This means that it can either be a name followed by an
    /// equals sign, or just an expression.
    fn parse_macro_arg(&mut self) -> ParseResult<AstNode<MacroInvocationArg>> {
        let start = self.current_pos();

        // here we trying to check if this argument is in form of just an expression or
        // if there is a name being assigned here...
        let name = match (self.peek(), self.peek_second()) {
            (
                Some(Token { kind: TokenKind::Ident(_), .. }),
                Some(Token { kind: TokenKind::Eq, .. }),
            ) => {
                let name = self.parse_name()?;
                self.skip_fast(TokenKind::Eq); // '='

                Some(name)
            }
            _ => None,
        };

        // Now here we expect an expression...
        let value = self.parse_expr_with_precedence(0)?;
        Ok(self.node_with_joined_span(MacroInvocationArg { name, value }, start))
    }

    fn parse_macro_invocation_with_args(&mut self) -> ParseResult<AstNode<MacroInvocation>> {
        let start = self.current_pos();
        let name = self.parse_name()?; // Parse a name for the macro invocation.

        let args = match self.peek() {
            Some(token) if token.is_paren_tree() => {
                let args = self.in_tree(Delimiter::Paren, None, |gen| {
                    Ok(gen
                        .parse_nodes(|g| g.parse_macro_arg(), |g| g.parse_token(TokenKind::Comma)))
                })?;
                let id = args.id();

                Some(AstNode::with_id(MacroInvocationArgs { args }, id))
            }
            _ => None,
        };

        Ok(self.node_with_joined_span(MacroInvocation { name, args }, start))
    }

    /// Parse a list of macro invocations, which can either be a single
    /// macro invocation, or a nested collection of macros. A single
    /// invocation might look like the following:
    /// ```notrust, ignore
    /// #foo main := () => { ... }
    /// ```
    /// And a nest invocation might look like the following:
    /// ```notrust, ignore
    /// #foo #bar #baz main := () => { ... }
    /// ```
    ///
    /// This function will parse single and nested invocations into a single
    /// batch of invocations.
    fn parse_macros(&mut self, kind: MacroKind) -> ParseResult<AstNode<MacroInvocations>> {
        let start = self.current_pos();
        let mut initial_prefix = true;
        let mut invocations = thin_vec![];

        // Check if this is a single macro invocation or a list of macro invocations.
        //
        // If it is followed by an `Ident` token, this means that we try to parse a
        // single macro invocation. These kind of invocations don't support
        // macro arguments, and can either be followed by another invocation. If
        // the next token is a `[...]` this means that we are parsing a list of
        // comma separated invocations.
        loop {
            if initial_prefix {
                initial_prefix = false;
            } else {
                // Otherwise, we expect the beginning of a new directive.
                if self.parse_macro_prefix(kind).is_none() {
                    break;
                }
            }

            match self.peek().copied() {
                Some(Token { kind: kind @ TokenKind::Ident(ident), span }) => {
                    self.skip_fast(kind); // `ident`

                    let directive_span = span.join(start);
                    let name = self.node_with_span(Name { ident }, directive_span);
                    invocations.push(
                        self.node_with_span(MacroInvocation { name, args: None }, directive_span),
                    );
                }
                Some(Token { kind: TokenKind::Tree(Delimiter::Bracket, _), .. }) => {
                    let new_invocations = self.in_tree(Delimiter::Bracket, None, |gen| {
                        Ok(gen.parse_nodes(
                            |g| g.parse_macro_invocation_with_args(),
                            |g| g.parse_token(TokenKind::Comma),
                        ))
                    })?;

                    // Simply append the new invocations to the list of invocations.
                    invocations.extend(new_invocations.nodes);
                }

                // We expected at least one directive here, so more specifically an
                // identifier after the hash.
                token if invocations.is_empty() => {
                    self.err_with_location(
                        ParseErrorKind::ExpectedMacroInvocation,
                        ExpectedItem::Ident | ExpectedItem::LeftBracket,
                        token.map(|t| t.kind),
                        token.map_or_else(|| self.eof_pos(), |t| t.span),
                    )?;
                }
                _ => break,
            }
        }

        // ##Hack: avoid making another id and allocating another span for
        // just a wrapper for the children. Ideally, this problem could be
        // fixed if we had `OptionalChildren!` in tree-def.
        let macros = self.nodes_with_joined_span(invocations, start);
        Ok(self.make_macro_invocations(macros))
    }

    pub(crate) fn make_macro_invocations(
        &self,
        invocations: AstNodes<MacroInvocation>,
    ) -> AstNode<MacroInvocations> {
        let id = invocations.id();
        AstNode::with_id(MacroInvocations { invocations }, id)
    }

    /// Parse a macro invocation, either being a name identifier or a bracketed
    /// list of macro invocations. This function will try to combine as many
    /// specified invocations into a single node in order to avoid
    /// allocating too many nodes.
    #[inline(always)]
    pub(crate) fn parse_macro_invocations(
        &mut self,
        kind: MacroKind,
    ) -> ParseResult<Option<AstNode<MacroInvocations>>> {
        // Hot-path: quickly check if we have a macro invocation.
        if self.parse_macro_prefix(kind).is_none() {
            return Ok(None);
        }

        // Slow-path: parse the macro invocations.
        Ok(Some(self.parse_macros(kind)?))
    }

    /// Parse macro invocations at the top level of a module. These invocations
    /// are always prefixed with a `#!`, and then followed by a `[...]`
    /// token tree. The caller is responsible for parsing the initial prefix
    /// tokens before calling this function.
    pub(crate) fn parse_module_marco_invocations(
        &mut self,
    ) -> ParseResult<ThinVec<AstNode<MacroInvocation>>> {
        self.in_tree(Delimiter::Bracket, None, |gen| {
            let invocations = gen.parse_node_collection(
                |g| g.parse_macro_invocation_with_args(),
                |g| g.parse_token(TokenKind::Comma),
            );

            Ok(invocations)
        })
    }

    /// Parse a token macro invocation, which begins with a `@`, and followed by
    /// the name of the token macro, or a `[...]` which contains the name of
    /// the token macro and its arguments.
    pub(crate) fn parse_token_macro_invocation(&mut self) -> ParseResult<TokenMacroInvocation> {
        self.skip_fast(TokenKind::At); // '@'

        // We want to either parse a name of the macro invocation, or a name
        // with arguments which is surrounded in a `[...]`.
        // let invoke = self.parse_macro_invocation()
        let mac = match self.peek().copied() {
            Some(Token { kind: kind @ TokenKind::Ident(ident), span }) => {
                self.skip_fast(kind);

                let name = self.node_with_span(Name { ident }, span);
                self.node_with_span(TokenMacro { name, args: None, delimited: false }, span)
            }
            Some(Token { kind: TokenKind::Tree(Delimiter::Bracket, _), .. }) => {
                self.in_tree(Delimiter::Bracket, None, |gen| {
                    // @@Ugly: we're converting the `macro_invocation` into a `token_macro` here...
                    let invocation = gen.parse_macro_invocation_with_args()?;
                    let id = invocation.id();
                    let MacroInvocation { name, args } = invocation.into_body();

                    Ok(AstNode::with_id(TokenMacro { name, args, delimited: true }, id))
                })?
            }

            // We expected at least one directive here, so more specifically an
            // identifier after the hash.
            token => self.err_with_location(
                ParseErrorKind::ExpectedMacroInvocation,
                ExpectedItem::Ident | ExpectedItem::LeftBracket,
                token.map(|t| t.kind),
                token.map_or_else(|| self.eof_pos(), |t| t.span),
            )?,
        };

        // Next, we deal with a stream of tokens, which is any token tree.
        let stream = match self.peek().copied() {
            Some(Token { kind: TokenKind::Tree(delimiter, length), .. }) => {
                let start = self.position() + 1;
                self.skip_token(); // We want to update our position, when we return to this generator.

                self.node_with_span(
                    TokenStream {
                        tokens: self.stream()[start..(start + length as usize)].to_vec(),
                        delimiter,
                    },
                    self.previous_pos(),
                )
            }
            tok => self.err_with_location(
                ParseErrorKind::UnExpected,
                ExpectedItem::DelimLeft,
                tok.map(|t| t.kind),
                tok.map_or_else(|| self.expected_pos(), |t| t.span),
            )?,
        };

        Ok(TokenMacroInvocation { mac, stream })
    }
}
