//! Parsing code for various kind of macros.

use hash_ast::ast::{
    AstNode, MacroInvocation, MacroInvocationArg, MacroInvocationArgs, MacroInvocations, MacroKind,
    Name,
};
use hash_token::{delimiter::Delimiter, Token, TokenKind};
use hash_utils::thin_vec::thin_vec;

use super::AstGen;
use crate::diagnostics::error::{ParseErrorKind, ParseResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    fn parse_macro_prefix(&self, kind: MacroKind) -> Option<()> {
        match kind {
            MacroKind::Token if self.parse_token_fast(TokenKind::At).is_some() => {
                self.skip_token();
                Some(())
            }
            MacroKind::Ast if self.parse_token_fast(TokenKind::Pound).is_some() => {
                self.skip_token();
                Some(())
            }
            _ => None,
        }
    }

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
                self.skip_token(); // '='

                Some(name)
            }
            _ => None,
        };

        // Now here we expect an expression...
        let value = self.parse_expr_with_precedence(0)?;
        Ok(self.node_with_span(MacroInvocationArg { name, value }, start))
    }

    fn parse_macro_invocation(&mut self) -> ParseResult<AstNode<MacroInvocation>> {
        let start = self.current_pos();
        let name = self.parse_name()?; // Parse a name for the macro invocation.

        let args = match self.peek() {
            Some(token) if token.is_paren_tree() => {
                let mut gen = self.parse_delim_tree(Delimiter::Paren, None)?;
                let args =
                    gen.parse_nodes(|g| g.parse_macro_arg(), |g| g.parse_token(TokenKind::Comma));
                self.consume_gen(gen);
                let id = args.id();

                Some(AstNode::with_id(MacroInvocationArgs { args }, id))
            }
            _ => None,
        };

        Ok(self.node_with_joined_span(MacroInvocation { name, args }, start))
    }

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
        // comma seperated invocations.
        loop {
            if initial_prefix {
                initial_prefix = false;
            } else {
                // Otherwise, we expect the beginning of a new directive.
                if self.parse_macro_prefix(kind).is_none() {
                    break;
                }
            }

            match *self.current_token() {
                Token { kind: TokenKind::Ident(ident), span } => {
                    let directive_span = span.join(start);
                    let name = self.node_with_span(Name { ident }, directive_span);
                    invocations.push(
                        self.node_with_span(MacroInvocation { name, args: None }, directive_span),
                    );
                }
                Token { kind: TokenKind::Tree(Delimiter::Bracket, tree_index), span } => {
                    let mut gen = self.from_stream(&self.token_trees[tree_index as usize], span);
                    let new_invocations = gen.parse_nodes(
                        |g| g.parse_macro_invocation(),
                        |g| g.parse_token(TokenKind::Comma),
                    );

                    self.consume_gen(gen);

                    // Simply append the new invocations to the list of invocations.
                    invocations.extend(new_invocations.nodes);
                }

                // We expected at least one directive here, so more specifically an
                // identifier after the hash.
                token if invocations.is_empty() => {
                    self.err_with_location(
                        ParseErrorKind::ExpectedMacroInvocation,
                        None,
                        Some(token.kind),
                        token.span,
                    )?;
                }
                _ => break,
            }
        }

        // @@Hack: avoid making another id and allocating another span for
        // just a wrapper for the children. Ideally, this problem could be
        // fixed if we had `OptionalChildren!` in tree-def.
        let invocations = self.nodes_with_joined_span(invocations, start);
        let id = invocations.id();
        Ok(AstNode::with_id(MacroInvocations { invocations }, id))
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
}
