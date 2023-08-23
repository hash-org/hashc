//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::{ast::*, origin::PatOrigin};
use hash_reporting::diagnostic::AccessToDiagnosticsMut;
use hash_source::{identifier::IDENTS, location::ByteRange};
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind};
use hash_utils::thin_vec::thin_vec;

use super::AstGen;
use crate::diagnostics::error::{ParseErrorKind, ParseResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a compound [Pat]. A compound [Pat] means that this could
    /// be a pattern that might be a combination of multiple patterns.
    /// Additionally, compound patterns are allowed to have `if-guard`
    /// syntax which permits for conditional matching of a pattern. There
    /// are only a few contexts where the full range of patterns is allowed
    /// (such as the `match` cases).
    pub fn parse_pat(&mut self) -> ParseResult<AstNode<Pat>> {
        // attempt to get the next token location as we're starting a pattern here, if
        // there is no token we should exit and return an error
        let start = self.next_pos();

        // Parse the first pattern, but throw away the location information since that
        // will be computed at the end anyway...
        let mut variants = self.nodes_with_span(thin_vec![], start);

        while self.has_token() {
            let pat = self.parse_pat_with_if()?;
            variants.nodes.push(pat);

            // Check if this is going to be another pattern following the current one.
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Pipe) => {
                    self.skip_token();
                }
                _ => break,
            }
        }

        // if the length of patterns is greater than one, we return an 'OR' pattern,
        // otherwise just the first pattern.
        if variants.len() == 1 {
            Ok(variants.nodes.pop().unwrap())
        } else {
            let joined = self.make_span(start.join(self.current_pos()));
            variants.set_span(joined);

            Ok(AstNode::new(Pat::Or(OrPat { variants }), joined))
        }
    }

    /// Parse a [Pat] with an optional `if-guard` after the singular
    /// pattern.
    pub fn parse_pat_with_if(&mut self) -> ParseResult<AstNode<Pat>> {
        let start = self.next_pos();
        let pat = self.parse_singular_pat()?;

        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Keyword(Keyword::If)) => {
                self.skip_token();

                let condition = self.parse_expr_with_precedence(0)?;

                Ok(self.node_with_joined_span(Pat::If(IfPat { pat, condition }), start))
            }
            _ => Ok(pat),
        }
    }

    /// Parse a singular [Pat]. Singular [Pat]s cannot have any grouped
    /// pattern operators such as a `|`, if guards or any form of compound
    /// pattern.
    pub(crate) fn parse_singular_pat(&mut self) -> ParseResult<AstNode<Pat>> {
        let (mut subject, can_continue) = self.parse_pat_component()?;
        let span = subject.span().span;

        while let Some(token) = self.peek() && can_continue {
            subject = match token.kind {
                // A constructor pattern which uses the `subject` to apply the constructor on
                TokenKind::Tree(Delimiter::Paren, tree_index) => {
                    self.skip_token();

                    let tree = self.token_trees.get(tree_index as usize).unwrap();
                    let mut gen = self.from_stream(tree, token.span);

                    // If we encounter a spread pattern, we keep it separate
                    // to all of the other fields that are specified for the
                    // constructor pattern.
                    let mut spread = None;

                    let fields = gen.parse_nodes_with_skips(
                        |g, pos| {
                            // If the next token is a dot, then we try to parse a spread pattern
                            // since this is the only case where a dot can appear in a tuple pattern.
                            if matches!(g.peek(), Some(token) if token.has_kind(TokenKind::Dot)) {
                                g.parse_spread_pat(&mut spread, pos, PatOrigin::Constructor)?;
                                Ok(None)
                            } else {
                                Ok(Some(g.parse_pat_arg()?))
                            }
                        },
                        |g| g.parse_token(TokenKind::Comma),
                    );
                    self.consume_gen(gen);

                    self.node_with_joined_span(
                        Pat::Constructor(ConstructorPat { subject, fields, spread }),
                        span,
                    )
                }
                // An access pattern which accesses the `subject` with a particular `property`
                // denotes with a name.
                TokenKind::Colon if matches!(self.peek_second(), Some(token) if token.has_kind(TokenKind::Colon)) =>
                {
                    self.offset.update(|offset| offset + 2);

                    self.node_with_joined_span(
                        Pat::Access(AccessPat { subject, property: self.parse_name()? }),
                        span,
                    )
                }
                _ => break,
            }
        }

        Ok(subject)
    }

    /// Internal function to pattern parsing used for parsing inner components
    /// of a single pattern. This function does not consider [Pat::Access]
    /// which is considered to be a single pattern, but made of components
    /// of other single patterns that have very specific rules about when it
    /// can be done.
    ///
    /// Returns a flag whether further patterns that are applied onto this
    /// [Pat] can be parsed. The `can_continue` flag is set to `false` if this
    /// produces a [Pat::Range].
    fn parse_pat_component(&mut self) -> ParseResult<(AstNode<Pat>, bool)> {
        let start = self.next_pos();
        let mut has_range_pat = false;
        let token = *self
            .peek()
            .ok_or_else(|| self.make_err(ParseErrorKind::UnExpected, None, None, None))?;

        let pat = match token {
            Token { kind: TokenKind::Ident(ident), .. } if ident == IDENTS.underscore => {
                self.skip_token();
                Pat::Wild(WildPat {})
            }
            // A name bind that has visibility/mutability modifiers
            Token {
                kind:
                    TokenKind::Keyword(Keyword::Pub | Keyword::Priv | Keyword::Mut)
                    | TokenKind::Ident(_),
                ..
            } => self.parse_binding_pat()?,

            // Literal patterns
            token
                if token.has_kind(TokenKind::Minus)
                    && matches!(self.peek_second(), Some(token) if token.kind.is_numeric()) =>
            {
                self.offset.update(|x| x + 2); // skip the minus and set current token to the numeric literal
                Pat::Lit(LitPat { data: self.parse_numeric_lit(true)? })
            }

            token if token.kind.is_lit() => {
                self.skip_token();
                Pat::Lit(LitPat { data: self.parse_primitive_lit()? })
            }
            // Potentially a range pattern
            token @ Token { kind: TokenKind::Dot, .. } => match self.maybe_parse_range_pat(None) {
                Some(pat) => {
                    has_range_pat = true;
                    Pat::Range(pat)
                }
                None => self.err_with_location(
                    ParseErrorKind::ExpectedPat,
                    None,
                    Some(token.kind),
                    token.span,
                )?,
            },

            // Tuple patterns
            Token { kind: TokenKind::Tree(Delimiter::Paren, tree_index), span } => {
                self.skip_token();
                let tree = self.token_trees.get(tree_index as usize).unwrap();

                return Ok((self.parse_tuple_pat(tree, span)?, true));
            }
            // Namespace patterns
            Token { kind: TokenKind::Tree(Delimiter::Brace, tree_index), span } => {
                self.skip_token();
                let tree = self.token_trees.get(tree_index as usize).unwrap();
                let pat = self.parse_module_pat(tree, span)?;

                Pat::Module(pat)
            }
            // Array pattern
            Token { kind: TokenKind::Tree(Delimiter::Bracket, tree_index), span } => {
                self.skip_token();
                let tree = self.token_trees.get(tree_index as usize).unwrap();

                return Ok((self.parse_array_pat(tree, span)?, true));
            }
            token => self.err_with_location(
                ParseErrorKind::ExpectedPat,
                None,
                Some(token.kind),
                token.span,
            )?,
        };

        // The only valid `range` pattern prefixes are either a bind, or a numeric
        // literal, bindings are later reported as erroneous anyway, but it's better
        // for error-reporting to defer this until later
        let (pat, can_continue) = if let Pat::Lit(LitPat { data: lit }) = &pat && !has_range_pat {
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Dot) => {
                    match self.maybe_parse_range_pat(Some(lit.clone())) {
                        Some(pat) => (Pat::Range(pat), false),
                        None => (pat, true),
                    }
                }
                _ => (pat, true),
            }
        } else {
            (pat, true)
        };

        Ok((self.node_with_joined_span(pat, start), can_continue))
    }

    /// Attempt to parse a range-pattern, if it fails then the
    /// function returns [None]
    fn maybe_parse_range_pat(&mut self, lo: Option<AstNode<Lit>>) -> Option<RangePat> {
        let offset = self.offset();

        // Parse the two dots...
        for _ in 0..2 {
            match self.parse_token_fast(TokenKind::Dot) {
                Some(_) => {}
                None => {
                    self.offset.set(offset);
                    return None;
                }
            }
        }

        // Now parse the range end specifier...
        let end = match self.parse_token_fast(TokenKind::Lt) {
            Some(_) => RangeEnd::Excluded,
            _ => RangeEnd::Included,
        };

        // Now parse the `hi` part of the range
        if matches!(self.peek(), Some(token) if token.kind.is_lit()) {
            self.skip_token();

            // @@ErrorReporting: just push the error but don't fail...
            match self.peek_resultant_fn(|t| t.parse_primitive_lit()) {
                Some(hi) => Some(RangePat { lo, hi: Some(hi), end }),
                None => {
                    // Reset the token offset to the beginning
                    self.offset.set(offset);
                    None
                }
            }
        } else {
            // This means that the range is open-ended, so we just return
            // the `lo` part of the range.
            Some(RangePat { lo, hi: None, end })
        }
    }

    /// Parse a [ModulePatEntry]. The [ModulePatEntry] refers to
    /// destructuring either a struct or a namespace to extract fields,
    /// exported members. The function takes in a token atom because both
    /// syntaxes use different operators as pattern assigners.
    pub(crate) fn parse_module_pat_entry(&mut self) -> ParseResult<AstNode<ModulePatEntry>> {
        let start = self.current_pos();
        let name = self.parse_name()?;

        // if the next token is the correct assigning operator, attempt to parse a
        // pattern here, if not then we copy the parsed ident and make a binding
        // pattern.
        let pat = match self.parse_token_fast(TokenKind::Keyword(Keyword::As)) {
            Some(_) => self.parse_pat()?,
            None => {
                let span = name.span();
                let copy = self.node(*name.body());

                AstNode::new(
                    Pat::Binding(BindingPat { name: copy, visibility: None, mutability: None }),
                    span,
                )
            }
        };

        Ok(self.node_with_joined_span(ModulePatEntry { name, pat }, start))
    }

    /// Parse a [ModulePat] which is comprised of a collection of
    /// [ModulePatEntry]s that are comma separated within a brace tree.
    fn parse_module_pat(
        &mut self,
        tree: &'stream [Token],
        span: ByteRange,
    ) -> ParseResult<ModulePat> {
        let mut gen = self.from_stream(tree, span);
        let mut fields = thin_vec![];

        while gen.has_token() {
            let start = gen.offset();

            match gen.parse_module_pat_entry().ok() {
                Some(pat) => fields.push(pat),
                None => {
                    gen.offset.set(start);
                    break;
                }
            }

            if gen.has_token() {
                gen.parse_token(TokenKind::Comma)?;
            }
        }
        self.consume_gen(gen);

        Ok(ModulePat { fields: self.nodes_with_span(fields, span) })
    }

    /// Parse a [`Pat::Array`] pattern from the token vector. An array pattern
    /// consists of a list of comma separated within a square brackets .e.g
    /// `[x, 1, ..]`
    pub(crate) fn parse_array_pat(
        &mut self,
        tree: &'stream [Token],
        parent_span: ByteRange,
    ) -> ParseResult<AstNode<Pat>> {
        let mut gen = self.from_stream(tree, parent_span);

        // We keep the spread pattern as a separate part of the array pattern
        // fields, so we must check for it separately.
        let mut spread = None;

        let fields = gen.parse_nodes_with_skips(
            |g, pos| {
                // Check if we encounter a dot, if so then we try to parse a
                // spread pattern, if not then we parse a normal pattern.
                if matches!(g.peek(), Some(token) if token.has_kind(TokenKind::Dot)) {
                    g.parse_spread_pat(&mut spread, pos, PatOrigin::Array)?;
                    Ok(None)
                } else {
                    Ok(Some(g.parse_pat()?))
                }
            },
            |g| g.parse_token(TokenKind::Comma),
        );
        self.consume_gen(gen);

        Ok(self.node_with_span(Pat::Array(ArrayPat { fields, spread }), parent_span))
    }

    /// Parse a [Pat::Tuple] from the token vector. A tuple pattern consists
    /// of nested patterns within parentheses which might also have an
    /// optional named fields.
    ///
    /// If only a singular pattern is parsed and it doesn't have a name, then
    /// the function will assume that this is not a tuple pattern and simply
    /// a pattern wrapped within parentheses.
    pub(crate) fn parse_tuple_pat(
        &mut self,
        tree: &'stream [Token],
        parent_span: ByteRange,
    ) -> ParseResult<AstNode<Pat>> {
        // check here if the tree length is 1, and the first token is the comma to check
        // if it is an empty tuple pattern...
        if let Some(token) = tree.get(0) {
            if token.has_kind(TokenKind::Comma) {
                return Ok(self.node_with_span(
                    Pat::Tuple(TuplePat {
                        fields: self.nodes_with_span(thin_vec![], parent_span),
                        spread: None,
                    }),
                    parent_span,
                ));
            }
        }

        // @@Hack: here it might actually be a nested pattern in parentheses. So we
        // perform a slight transformation if the number of parsed patterns is
        // only one. So essentially we handle the case where a pattern is
        // wrapped in parentheses and so we just unwrap it.
        let mut gen = self.from_stream(tree, parent_span);

        // We track the spread pattern separately because it is not a part of the
        // tuple pattern fields.
        let mut spread = None;

        let mut fields = gen.parse_nodes_with_skips(
            |g, pos| {
                // If the next token is a dot, then we try to parse a spread pattern
                // since this is the only case where a dot can appear in a tuple pattern.
                if matches!(g.peek(), Some(token) if token.has_kind(TokenKind::Dot)) {
                    g.parse_spread_pat(&mut spread, pos, PatOrigin::Tuple)?;
                    Ok(None)
                } else {
                    Ok(Some(g.parse_pat_arg()?))
                }
            },
            |g| g.parse_token(TokenKind::Comma),
        );

        // If there is no associated name with the entry and there is only one entry
        // then we can be sure that it is only a nested entry.
        if spread.is_none()
            && fields.len() == 1
            && fields[0].name.is_none()
            && !matches!(gen.current_token().kind, TokenKind::Comma)
        {
            // @@Future: we want to check if there were any errors and then
            // if not we want to possibly emit a warning about redundant parentheses
            // for this particular pattern
            self.consume_gen(gen);

            let PatArg { pat, macro_args, .. } = fields.nodes.pop().unwrap().into_body();

            if let Some(macro_args) = macro_args {
                Ok(AstNode::with_id(
                    Pat::Macro(PatMacroInvocation { macro_args, subject: pat }),
                    fields.id(),
                ))
            } else {
                Ok(pat)
            }
        } else {
            self.consume_gen(gen);
            Ok(self.node_with_span(Pat::Tuple(TuplePat { fields, spread }), parent_span))
        }
    }

    /// Parse an pattern argument which might consists of an optional
    /// [Name], a value [Pat], and optional macro invocations on the
    /// argument.
    pub(crate) fn parse_pat_arg(&mut self) -> ParseResult<AstNode<PatArg>> {
        let start = self.next_pos();
        let macro_args = self.parse_macro_invocations(MacroKind::Ast)?;

        let (name, pat) = match self.peek() {
            Some(Token { kind: TokenKind::Ident(_), .. }) => {
                // Here if there is a '=', this means that there is a name attached to the entry
                // within the tuple pattern...
                match self.peek_second() {
                    Some(token) if token.has_kind(TokenKind::Eq) => {
                        let name = self.parse_name()?;
                        self.skip_token(); // '='

                        (Some(name), self.parse_pat()?)
                    }
                    _ => (None, self.parse_pat()?),
                }
            }
            _ => (None, self.parse_pat()?),
        };

        Ok(self.node_with_joined_span(PatArg { name, pat, macro_args }, start))
    }

    /// Parse a spread operator from the current token tree. A spread operator
    /// can have an optional name attached to the spread operator on the
    /// right hand-side.
    ///
    /// ## Allowed locations
    /// So the spread operator can only appear within either `list`, `tuple`
    /// patterns at the moment which means that any other location will mark
    /// it as `invalid` in the current implementation.
    pub(crate) fn parse_spread_pat(
        &mut self,
        spread: &mut Option<AstNode<SpreadPat>>,
        position: usize,
        origin: PatOrigin,
    ) -> ParseResult<()> {
        let start = self.next_pos();

        for k in 0..3 {
            self.parse_token_fast(TokenKind::Dot).ok_or_else(|| {
                self.make_err(
                    ParseErrorKind::MalformedSpreadPattern(3 - k),
                    None,
                    None,
                    Some(self.next_pos()),
                )
            })?;
        }

        // Try and see if there is a identifier that is followed by the spread to try
        // and bind the capture to a variable
        let name = self.peek_resultant_fn(|g| g.parse_name());
        let span = start.join(self.current_pos());

        // If the spread pattern is already present, then we need to
        // report this as an error since, a spread pattern can only appear
        // once within a tuple or list pattern.
        if spread.is_some() {
            self.add_error(self.make_err(
                ParseErrorKind::MultipleSpreadPats { origin },
                None,
                None,
                Some(span),
            ));
        } else {
            *spread = Some(self.node_with_span(SpreadPat { name, position }, span));
        }

        Ok(())
    }

    /// Function to parse a [BindingPat] without considering whether it
    /// might be part of a constructor or any other form of pattern. This
    /// function also accounts for visibility or mutability modifiers on the
    /// binding pattern.
    fn parse_binding_pat(&self) -> ParseResult<Pat> {
        let visibility = self.peek_resultant_fn(|g| g.parse_visibility());

        // Parse a mutability modifier if any
        let mutability = self
            .parse_token_fast(TokenKind::Keyword(Keyword::Mut))
            .map(|_| self.node_with_span(Mutability::Mutable, self.current_pos()));

        let name = self.parse_name()?;

        Ok(Pat::Binding(BindingPat { name, visibility, mutability }))
    }

    /// Parse a [Visibility] modifier, either being a `pub` or `priv`.
    fn parse_visibility(&self) -> ParseResult<AstNode<Visibility>> {
        match self.next_token() {
            Some(Token { kind: TokenKind::Keyword(Keyword::Pub), span }) => {
                Ok(self.node_with_span(Visibility::Public, *span))
            }
            Some(Token { kind: TokenKind::Keyword(Keyword::Priv), span }) => {
                Ok(self.node_with_span(Visibility::Private, *span))
            }
            token => self.err_with_location(
                ParseErrorKind::UnExpected,
                None,
                token.map(|t| t.kind),
                token.map_or_else(|| self.next_pos(), |t| t.span),
            ),
        }
    }

    /// Utility function to lookahead and see if it's possible to parse a
    /// singular pattern from the current position in the token stream. This is
    /// essentially a dry-run of [Self::parse_singular_pat] since it doesn't
    /// create any kind of patterns whilst traversing the token tree.
    pub(crate) fn begins_pat(&self) -> bool {
        let check_lit = |offset| match self.peek_nth(offset) {
            Some(token) if token.has_kind(TokenKind::Minus) => match self.peek_nth(offset + 1) {
                Some(token) if token.kind.is_numeric() => 2,
                _ => 0,
            },
            Some(token) if token.kind.is_lit() => 1,
            _ => 0,
        };

        // Firstly, we might need to deal with literals and range patterns
        let count = check_lit(0);

        if count != 0 {
            // If we peek, there is a dot, and we can check that there
            // is also a lit at the end, then we can conclude that this could
            // be a pattern
            let range_tokens = [
                self.peek_nth(count).map_or(false, |t| t.kind == TokenKind::Dot),
                self.peek_nth(count + 1).map_or(false, |t| t.kind == TokenKind::Dot),
                self.peek_nth(count + 2).map_or(false, |t| t.kind == TokenKind::Lt),
            ];

            let count = match range_tokens {
                // No initial dot, so it could just be a literal
                [false, _, _] => {
                    return matches!(self.peek_nth(count), Some(token) if token.has_kind(TokenKind::Colon))
                }
                // `..`
                [true, true, false] => count + 2,
                // `..<`
                [true, true, true] => count + 3,
                _ => return false,
            };

            // Now we need to check that there is a literal after this range token
            let offset = check_lit(count);
            if offset != 0 {
                return matches!(self.peek_nth(offset + count), Some(token) if token.has_kind(TokenKind::Colon));
            } else {
                return false;
            }
        }

        // Perform the initial pattern component lookahead
        let mut n_lookahead = match self.peek() {
            // Namespace, List, Tuple, etc.
            Some(Token { kind: TokenKind::Tree(_, _), .. }) => 1,
            // Identifier or constructor pattern
            Some(Token { kind: TokenKind::Ident(_), .. }) => 1,
            // This is the case for a bind that has a visibility modifier at the beginning. In
            // this scenario, it can be followed by a `mut` modifier and then a identifier or
            // just an identifier.
            Some(Token { kind: TokenKind::Keyword(Keyword::Priv | Keyword::Pub), .. }) => {
                match self.peek_second() {
                    Some(Token { kind: TokenKind::Ident(_), .. }) => 2,
                    Some(Token { kind: TokenKind::Keyword(Keyword::Mut), .. }) => {
                        match self.peek_nth(2) {
                            Some(Token { kind: TokenKind::Ident(_), .. }) => 3,
                            _ => return false,
                        }
                    }
                    _ => return false,
                }
            }
            // This case covers the scenario where there is just a mutability modifier
            // in front of the name binding
            Some(Token { kind: TokenKind::Keyword(Keyword::Mut), .. }) => {
                match self.peek_second() {
                    Some(Token { kind: TokenKind::Ident(_), .. }) => 2,
                    _ => return false,
                }
            }
            _ => return false,
        };

        // Continue looking ahead to see if we're applying an access pr a construction
        // on the pattern
        while let Some(token) = self.peek_nth(n_lookahead) {
            match token.kind {
                // Handle the `constructor` pattern case
                TokenKind::Tree(Delimiter::Paren, _) => n_lookahead += 1,
                // Handle the `access` pattern case. We're looking for the next
                // three tokens to be `::Ident`
                TokenKind::Colon => {
                    if matches!(self.peek_nth(n_lookahead + 1), Some(token) if token.has_kind(TokenKind::Colon))
                        && matches!(
                            self.peek_nth(n_lookahead + 2),
                            Some(Token { kind: TokenKind::Ident(_), .. })
                        )
                    {
                        n_lookahead += 3;
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }

        matches!(self.peek_nth(n_lookahead), Some(token) if token.has_kind(TokenKind::Colon))
    }
}
