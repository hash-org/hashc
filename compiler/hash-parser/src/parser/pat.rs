//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::{ast::*, origin::PatOrigin};
use hash_reporting::diagnostic::HasDiagnosticsMut;
use hash_source::identifier::IDENTS;
use hash_token::{Token, TokenKind, delimiter::Delimiter, keyword::Keyword};
use hash_utils::thin_vec::thin_vec;

use super::AstGen;
use crate::diagnostics::{
    error::{ParseErrorKind, ParseResult},
    expected::ExpectedItem,
};

impl AstGen<'_> {
    /// Parse a compound [Pat]. A compound [Pat] means that this could
    /// be a pattern that might be a combination of multiple patterns.
    /// Additionally, compound patterns are allowed to have `if-guard`
    /// syntax which permits for conditional matching of a pattern. There
    /// are only a few contexts where the full range of patterns is allowed
    /// (such as the `match` cases).
    pub fn parse_pat(&mut self) -> ParseResult<AstNode<Pat>> {
        // attempt to get the next token location as we're starting a pattern here, if
        // there is no token we should exit and return an error
        let start = self.current_pos();

        // Parse the first pattern, but throw away the location information since that
        // will be computed at the end anyway...
        let mut variants = thin_vec![];

        while self.has_token() {
            let pat = self.parse_pat_with_if()?;
            variants.push(pat);

            // Check if this is going to be another pattern following the current one.
            match self.peek_kind() {
                Some(TokenKind::Pipe) => {
                    self.skip_fast(TokenKind::Pipe); // '|'
                }
                _ => break,
            }
        }

        // if the length of patterns is greater than one, we return an 'OR' pattern,
        // otherwise just the first pattern.
        if variants.len() == 1 {
            Ok(variants.pop().unwrap())
        } else {
            let joined = start.join(self.current_pos());
            let variants = self.nodes_with_span(variants, joined);
            Ok(self.node_with_span(Pat::Or(OrPat { variants }), joined))
        }
    }

    /// Parse a [Pat] with an optional `if-guard` after the singular
    /// pattern.
    pub fn parse_pat_with_if(&mut self) -> ParseResult<AstNode<Pat>> {
        let start = self.current_pos();
        let pat = self.parse_singular_pat()?;

        match self.peek_kind() {
            Some(kind @ TokenKind::Keyword(Keyword::If)) => {
                self.skip_fast(kind); // `if`

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
        let span = self.current_pos();
        let (mut subject, can_continue) = self.parse_pat_component()?;

        while let Some(token) = self.peek()
            && can_continue
        {
            subject = match token.kind {
                // A constructor pattern which uses the `subject` to apply the constructor on
                TokenKind::Tree(Delimiter::Paren, _) => {
                    // If we encounter a spread pattern, we keep it separate
                    // to all of the other fields that are specified for the
                    // constructor pattern.
                    let mut spread = None;

                    // `in_tree` eat the paren token.
                    let fields = self.in_tree(Delimiter::Paren, None, |g| {
                        Ok(g.parse_nodes_with_skips(
                            |g, pos| {
                                // If the next token is an ellipsis, then we try to parse a spread
                                // pattern.
                                if g.try_parse_spread_pat(&mut spread, pos, PatOrigin::Constructor)?
                                {
                                    Ok(None)
                                } else {
                                    Ok(Some(g.parse_pat_arg()?))
                                }
                            },
                            |g| g.parse_token(TokenKind::Comma),
                        ))
                    })?;

                    self.node_with_joined_span(
                        Pat::Constructor(ConstructorPat { subject, fields, spread }),
                        span,
                    )
                }
                // An access pattern which accesses the `subject` with a particular `property`
                // denotes with a name.
                TokenKind::Access => {
                    self.skip_fast(TokenKind::Access); // `::`
                    let property = self.parse_name()?;
                    self.node_with_joined_span(Pat::Access(AccessPat { subject, property }), span)
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
        let start = self.current_pos();
        let mut has_range_pat = false;

        let token = *self.peek().ok_or_else(|| {
            self.make_err(ParseErrorKind::UnExpected, ExpectedItem::Pat, None, None)
        })?;

        let pat = match token {
            Token { kind: kind @ TokenKind::Ident(ident), .. } if ident == IDENTS.underscore => {
                self.skip_fast(kind); // `ident`
                Pat::Wild(WildPat {})
            }
            // A name bind that has visibility/mutability modifiers
            Token {
                kind:
                    TokenKind::Keyword(Keyword::Pub | Keyword::Priv | Keyword::Mut)
                    | TokenKind::Ident(_),
                ..
            } => self.parse_binding_pat()?,

            // We emit an error saying that we don't support expressions in patterns
            // since the AST doesn't support it. Negative literals must be written with
            // no spaces between the `-` and the literal itself.
            token
                if token.has_kind(TokenKind::Minus)
                    && matches!(self.peek_second(), Some(token) if token.kind.is_numeric()) =>
            {
                // Just to get the error reporting to highlight the entire literal.
                self.skip_fast(TokenKind::Minus); // `-`

                return self.err_with_location(
                    ParseErrorKind::UnsupportedExprInPat {
                        value: self.source.hunk(self.current_pos()).to_string(),
                    },
                    ExpectedItem::empty(),
                    None,
                    token.span.join(self.current_pos()),
                );
            }

            // Literals
            token if token.kind.is_lit() => Pat::Lit(LitPat { data: self.parse_primitive_lit() }),
            // Potentially a range pattern
            token @ Token { kind: TokenKind::Range | TokenKind::RangeExclusive, .. } => {
                match self.maybe_parse_range_pat(None) {
                    Some(pat) => {
                        has_range_pat = true;
                        Pat::Range(pat)
                    }
                    None => self.err_with_location(
                        ParseErrorKind::ExpectedPat,
                        ExpectedItem::Pat,
                        Some(token.kind),
                        token.span,
                    )?,
                }
            }

            // Parse a token macro invocation
            Token { kind: TokenKind::At, .. } => {
                let token_macro = self.parse_token_macro_invocation()?;
                return Ok((
                    self.node_with_joined_span(Pat::TokenMacro(token_macro), token.span),
                    false,
                ));
            }

            // Tuple patterns
            Token { kind: TokenKind::Tree(Delimiter::Paren, _), .. } => {
                return self.in_tree(Delimiter::Paren, None, |g| Ok((g.parse_tuple_pat()?, true)));
            }
            // Module patterns
            Token { kind: TokenKind::Tree(Delimiter::Brace, _), .. } => {
                self.in_tree(Delimiter::Brace, None, |g| Ok(Pat::Module(g.parse_module_pat()?)))?
            }
            // Array pattern
            Token { kind: TokenKind::Tree(Delimiter::Bracket, _), .. } => {
                return self
                    .in_tree(Delimiter::Bracket, None, |g| Ok((g.parse_array_pat()?, true)));
            }
            token => self.err_with_location(
                ParseErrorKind::ExpectedPat,
                ExpectedItem::Pat,
                Some(token.kind),
                token.span,
            )?,
        };

        // The only valid `range` pattern prefixes are either a bind, or a numeric
        // literal, bindings are later reported as erroneous anyway, but it's better
        // for error-reporting to defer this until later
        let (pat, can_continue) = if let Pat::Lit(LitPat { data: lit }) = &pat
            && !has_range_pat
        {
            match self.peek_kind() {
                Some(TokenKind::Range | TokenKind::RangeExclusive) => {
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

    /// Attempt to parse a [RangePat] whilst providing the `lo` component of the
    /// range pattern. The `lo` component is the left hand-side of the range. If
    /// it is not provided, then the [RangePat] does not include a `lo`
    /// component.
    fn maybe_parse_range_pat(&mut self, lo: Option<AstNode<Lit>>) -> Option<RangePat> {
        let end = match self.peek_kind() {
            Some(TokenKind::Range) => {
                self.skip_fast(TokenKind::Range);
                RangeEnd::Included
            }
            Some(TokenKind::RangeExclusive) => {
                self.skip_fast(TokenKind::RangeExclusive);
                RangeEnd::Excluded
            }
            _ => return None,
        };

        // Now parse the `hi` part of the range
        if matches!(self.peek_kind(), Some(kind) if kind.is_range_lit()) {
            Some(RangePat { lo, hi: Some(self.parse_primitive_lit()), end })
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

        // ##ErrorReporting: handle the case where the user tries to specify
        // an ellipsis in a module pattern entry, this is not allowed.
        if self.peek_kind() == Some(TokenKind::Ellipsis) {
            return self.err_with_location(
                ParseErrorKind::DisallowedSpreadPat { origin: PatOrigin::Mod },
                ExpectedItem::Ident,
                None,
                start,
            );
        }

        let (name, name_span) = self.track_span(|this| this.parse_name())?;

        // if the next token is the correct assigning operator, attempt to parse a
        // pattern here, if not then we copy the parsed ident and make a binding
        // pattern.
        let pat = match self.parse_token_fast(TokenKind::Keyword(Keyword::As)) {
            Some(_) => self.parse_pat()?,
            None => {
                let copy = self.node(*name.body());

                self.node_with_span(
                    Pat::Binding(BindingPat { name: copy, visibility: None, mutability: None }),
                    name_span,
                )
            }
        };

        Ok(self.node_with_joined_span(ModulePatEntry { name, pat }, start))
    }

    /// Parse a [ModulePat] which is comprised of a collection of
    /// [ModulePatEntry]s that are comma separated within a brace tree.
    ///
    /// ##Note: we should be in a generator already!
    fn parse_module_pat(&mut self) -> ParseResult<ModulePat> {
        let fields =
            self.parse_nodes(|g| g.parse_module_pat_entry(), |g| g.parse_token(TokenKind::Comma));

        Ok(ModulePat { fields })
    }

    /// Parse a [`Pat::Array`] pattern from the token vector. An array pattern
    /// consists of a list of comma separated within a square brackets .e.g
    /// `[x, 1, ..]`
    pub(crate) fn parse_array_pat(&mut self) -> ParseResult<AstNode<Pat>> {
        // We keep the spread pattern as a separate part of the array pattern
        // fields, so we must check for it separately.
        let mut spread = None;

        let fields = self.parse_nodes_with_skips(
            |g, pos| {
                // If the next token is an ellipsis, then we try to parse a spread pattern.
                if g.try_parse_spread_pat(&mut spread, pos, PatOrigin::Array)? {
                    Ok(None)
                } else {
                    Ok(Some(g.parse_pat()?))
                }
            },
            |g| g.parse_token(TokenKind::Comma),
        );

        Ok(self.node_with_span(Pat::Array(ArrayPat { fields, spread }), self.range()))
    }

    /// Parse a [Pat::Tuple] from the token vector. A tuple pattern consists
    /// of nested patterns within parentheses which might also have an
    /// optional named fields.
    ///
    /// If only a singular pattern is parsed and it doesn't have a name, then
    /// the function will assume that this is not a tuple pattern and simply
    /// a pattern wrapped within parentheses.
    pub(crate) fn parse_tuple_pat(&mut self) -> ParseResult<AstNode<Pat>> {
        // check here if the tree length is 1, and the first token is the comma to check
        // if it is an empty tuple pattern...
        if let Some(TokenKind::Comma) = self.peek_kind() {
            self.skip_fast(TokenKind::Comma);

            let span = self.range();
            let fields = self.nodes_with_span(thin_vec![], span);

            return Ok(self.node_with_span(Pat::Tuple(TuplePat { fields, spread: None }), span));
        }

        // We track the spread pattern separately because it is not a part of the
        // tuple pattern fields.
        let mut spread = None;

        let mut fields = self.parse_nodes_with_skips(
            |g, pos| {
                // If the next token is an ellipsis, then we try to parse a spread pattern.
                if g.try_parse_spread_pat(&mut spread, pos, PatOrigin::Tuple)? {
                    Ok(None)
                } else {
                    Ok(Some(g.parse_pat_arg()?))
                }
            },
            |g| g.parse_token(TokenKind::Comma),
        );

        // ##Hack: here it might actually be a nested pattern in parentheses. So we
        // perform a slight transformation if the number of parsed patterns is
        // only one. So essentially we handle the case where a pattern is
        // wrapped in parentheses and so we just unwrap it.
        //
        // If there is no associated name with the entry and there is only one entry
        // then we can be sure that it is only a nested entry.
        if spread.is_none()
            && fields.len() == 1
            && fields[0].name.is_none()
            && !matches!(self.previous_token().kind, TokenKind::Comma)
        {
            // @@Future: we want to check if there were any errors and then
            // if not we want to possibly emit a warning about redundant parentheses
            // for this particular pattern
            let PatArg { pat, macros, .. } = fields.nodes.pop().unwrap().into_body();

            if let Some(macros) = macros {
                Ok(AstNode::with_id(
                    Pat::Macro(PatMacroInvocation { macros, subject: pat }),
                    fields.id(),
                ))
            } else {
                Ok(pat)
            }
        } else {
            Ok(self.node_with_span(Pat::Tuple(TuplePat { fields, spread }), self.range()))
        }
    }

    /// Parse an pattern argument which might consists of an optional
    /// [Name], a value [Pat], and optional macro invocations on the
    /// argument.
    pub(crate) fn parse_pat_arg(&mut self) -> ParseResult<AstNode<PatArg>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;
        let start = self.current_pos();

        let (name, pat) = match self.peek_kind() {
            Some(TokenKind::Ident(_)) => {
                // Here if there is a '=', this means that there is a name attached to the entry
                // within the tuple pattern...
                match self.peek_second() {
                    Some(token) if token.has_kind(TokenKind::Eq) => {
                        let name = self.parse_name()?;
                        self.skip_fast(TokenKind::Eq); // '='

                        (Some(name), self.parse_pat()?)
                    }
                    _ => (None, self.parse_pat()?),
                }
            }
            _ => (None, self.parse_pat()?),
        };

        Ok(self.node_with_joined_span(PatArg { name, pat, macros }, start))
    }

    /// Parse a spread operator from the current token tree. A spread operator
    /// can have an optional name attached to the spread operator on the
    /// right hand-side.
    ///
    /// ## Allowed locations
    /// So the spread operator can only appear within either `list`, `tuple`
    /// patterns at the moment which means that any other location will mark
    /// it as `invalid` in the current implementation.
    pub(crate) fn try_parse_spread_pat(
        &mut self,
        spread: &mut Option<AstNode<SpreadPat>>,
        position: usize,
        origin: PatOrigin,
    ) -> ParseResult<bool> {
        let start = self.current_pos();

        // Give some nice feedback to user about how many `.`s we expected
        match self.peek_kind() {
            Some(TokenKind::Ellipsis) => {
                self.skip_fast(TokenKind::Ellipsis); // `...`
            }
            Some(TokenKind::Range) => {
                self.skip_fast(TokenKind::Range); // `..`
                return self.err_with_location(
                    ParseErrorKind::MalformedSpreadPat(1),
                    ExpectedItem::Dot,
                    None,
                    self.current_pos(),
                );
            }
            Some(TokenKind::Dot) => {
                self.skip_fast(TokenKind::Dot); // `.`
                return self.err_with_location(
                    ParseErrorKind::MalformedSpreadPat(2),
                    ExpectedItem::Range,
                    None,
                    self.current_pos(),
                );
            }
            _ => {
                return Ok(false);
            }
        };

        // Try and see if there is a identifier that is followed by the spread to try
        // and bind the capture to a variable
        let name = self.peek_resultant_fn(|g| g.parse_name());
        let span = start.join(self.previous_pos());

        // If the spread pattern is already present, then we need to
        // report this as an error since, a spread pattern can only appear
        // once within a tuple or list pattern.
        if spread.is_some() {
            self.add_error(self.make_err(
                ParseErrorKind::MultipleSpreadPats { origin },
                ExpectedItem::empty(),
                None,
                Some(span),
            ));
        } else {
            *spread = Some(self.node_with_span(SpreadPat { name, position }, span));
        }

        Ok(true)
    }

    /// Function to parse a [BindingPat] without considering whether it
    /// might be part of a constructor or any other form of pattern. This
    /// function also accounts for visibility or mutability modifiers on the
    /// binding pattern.
    fn parse_binding_pat(&mut self) -> ParseResult<Pat> {
        let visibility = self.peek_resultant_fn(|g| g.parse_visibility());

        // Parse a mutability modifier if any
        let mutability = self
            .parse_token_fast(TokenKind::Keyword(Keyword::Mut))
            .map(|_| self.node_with_span(Mutability::Mutable, self.current_pos()));

        let name = self.parse_name()?;

        Ok(Pat::Binding(BindingPat { name, visibility, mutability }))
    }

    /// Parse a [Visibility] modifier, either being a `pub` or `priv`.
    fn parse_visibility(&mut self) -> ParseResult<AstNode<Visibility>> {
        match self.current_token_and_advance() {
            Some(Token { kind: TokenKind::Keyword(Keyword::Pub), span }) => {
                Ok(self.node_with_span(Visibility::Public, *span))
            }
            Some(Token { kind: TokenKind::Keyword(Keyword::Priv), span }) => {
                Ok(self.node_with_span(Visibility::Private, *span))
            }
            token => self.err_with_location(
                ParseErrorKind::UnExpected,
                ExpectedItem::Visibility,
                token.map(|t| t.kind),
                token.map_or_else(|| self.eof_pos(), |t| t.span),
            ),
        }
    }

    /// Utility function to lookahead and see if it's possible to parse a
    /// singular pattern from the current position in the token stream. This is
    /// essentially a dry-run of [Self::parse_singular_pat] since it doesn't
    /// create any kind of patterns whilst traversing the token tree.
    ///
    /// @@Ugly: simplify or remove this!
    pub(crate) fn begins_pat(&self) -> bool {
        let start = self.position();
        let result = self.peek_pat();
        self.set_pos(start);

        result
    }

    fn peek_pat(&self) -> bool {
        macro_rules! peek_colon(
            () => {
                matches!(self.peek_kind(), Some(TokenKind::Colon))
            }
        );

        // Perform the initial pattern component lookahead
        match self.peek_kind() {
            // Literals in ranges
            Some(kind) if kind.is_range_lit() => {
                self.skip_fast(kind);

                match self.peek_kind() {
                    Some(kind @ (TokenKind::Range | TokenKind::RangeExclusive)) => {
                        self.skip_fast(kind); // '..' | '..<'

                        // Now we need to check that there is a literal after this range token
                        if let Some(kind) = self.peek_kind()
                            && kind.is_range_lit()
                        {
                            self.skip_fast(kind);
                            peek_colon!()
                        } else {
                            false
                        }
                    }
                    Some(TokenKind::Colon) => true,
                    _ => false,
                }
            }
            // Other general literal patterns.
            Some(kind) if kind.is_lit() => {
                self.skip_fast(kind);
                peek_colon!()
            }
            // Module, Array, Tuple patterns.
            Some(TokenKind::Tree(_, _)) => {
                self.skip_token();
                peek_colon!()
            }
            // Identifier or constructor pattern.
            Some(ident @ TokenKind::Ident(_)) => {
                self.skip_fast(ident);

                // Continue looking ahead to see if we're applying an access pr a construction
                // on the pattern
                while let Some(token) = self.peek() {
                    match token.kind {
                        // Handle the `constructor` pattern case
                        TokenKind::Tree(Delimiter::Paren, _) => self.skip_token(),
                        // Handle the `access` pattern case. We're looking for the next
                        // three tokens to be `::Ident`
                        TokenKind::Access => {
                            self.skip_fast(TokenKind::Access);

                            match self.peek_kind() {
                                Some(ident @ TokenKind::Ident(_)) => {
                                    self.skip_fast(ident);
                                }
                                _ => return false,
                            }
                        }
                        _ => break,
                    }
                }

                peek_colon!()
            }
            // This is the case for a bind that has a visibility modifier at the beginning. In
            // this scenario, it can be followed by a `mut` modifier and then a identifier or
            // just an identifier.
            Some(TokenKind::Keyword(Keyword::Priv | Keyword::Pub | Keyword::Mut)) => true,
            _ => false,
        }
    }
}
