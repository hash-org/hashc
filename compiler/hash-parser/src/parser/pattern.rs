//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_ast::{ast::*, ast_nodes, ident::CORE_IDENTIFIERS};
use hash_source::location::Span;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use crate::{disable_flag, enable_flag};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a compound [Pattern]. A compound [Pattern] means that this could be a
    /// pattern that might be a combination of multiple patterns. Additionally, compound
    /// patterns are allowed to have `if-guard` syntax which permits for conditional matching
    /// of a pattern. There are only a few contexts where the full range of patterns is allowed
    /// (such as the `match` cases).
    pub fn parse_pattern(&self) -> AstGenResult<AstNode<Pattern>> {
        // attempt to get the next token location as we're starting a pattern here, if there is no token
        // we should exit and return an error
        let start = self.next_location();

        // Parse the first pattern, but throw away the location information since that will be
        // computed at the end anyway...
        let mut patterns = ast_nodes![];

        while self.has_token() {
            let pattern = self.parse_pattern_with_if()?;
            patterns.nodes.push(pattern);

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
        if patterns.len() == 1 {
            Ok(patterns.nodes.pop().unwrap())
        } else {
            Ok(self.node_with_joined_span(Pattern::Or(OrPattern { variants: patterns }), &start))
        }
    }

    /// Parse a [Pattern] with an optional `if-guard` after the singular pattern.
    pub fn parse_pattern_with_if(&self) -> AstGenResult<AstNode<Pattern>> {
        let start = self.next_location();
        let pattern = self.parse_singular_pattern()?;

        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Keyword(Keyword::If)) => {
                self.skip_token();

                let condition = self.parse_expression_with_precedence(0)?;

                Ok(self
                    .node_with_joined_span(Pattern::If(IfPattern { pattern, condition }), &start))
            }
            _ => Ok(pattern),
        }
    }

    /// Parse a singular [Pattern]. Singular [Pattern]s cannot have any grouped pattern
    /// operators such as a `|`, if guards or any form of compound pattern.
    pub(crate) fn parse_singular_pattern(&self) -> AstGenResult<AstNode<Pattern>> {
        let spread_patterns_allowed = self.spread_patterns_allowed.get();

        let start = self.next_location();
        let token = self
            .peek()
            .ok_or_else(|| self.make_error(AstGenErrorKind::EOF, None, None, None))?;

        let pattern = match token {
            // A name bind that has visibility/mutability modifiers
            Token {
                kind: TokenKind::Keyword(Keyword::Pub | Keyword::Priv | Keyword::Mut),
                ..
            } => self.parse_binding_pattern()?,
            // this could be either just a binding pattern, enum, or a struct pattern
            Token {
                kind: TokenKind::Ident(ident),
                span,
            } => {
                self.skip_token();

                // So here we try to parse an access name, if it is only made of a single binding
                // name, we'll just return this as a binding pattern, otherwise it must follow that
                // it is either a enum or struct pattern, if not we report it as an error since
                // access names cannot be used as binding patterns on their own...
                let name = self.parse_access_name(self.node_with_span(*ident, *span))?;

                match self.peek() {
                    // a `constructor` pattern
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                        span,
                    }) => {
                        self.skip_token();
                        let tree = self.token_trees.get(*tree_index).unwrap();
                        let gen = self.from_stream(tree, *span);

                        disable_flag!(gen; spread_patterns_allowed;
                            let fields = gen.parse_separated_fn(
                                || gen.parse_tuple_pattern_entry(),
                                || gen.parse_token(TokenKind::Comma),
                            )?
                        );

                        Pattern::Constructor(ConstructorPattern { name, fields })
                    }
                    Some(token) if name.path.len() > 1 => self.error_with_location(
                        AstGenErrorKind::Expected,
                        None,
                        Some(token.kind),
                        token.span,
                    )?,
                    _ => {
                        if *ident == CORE_IDENTIFIERS.underscore {
                            Pattern::Ignore(IgnorePattern)
                        } else {
                            Pattern::Binding(BindingPattern {
                                name: self.node_with_span(Name { ident: *ident }, *span),
                                visibility: None,
                                mutability: None,
                            })
                        }
                    }
                }
            }
            // Spread pattern
            token if spread_patterns_allowed && token.has_kind(TokenKind::Dot) => {
                Pattern::Spread(self.parse_spread_pattern()?)
            }

            // Literal patterns
            token if token.kind.is_literal() => {
                self.skip_token();
                Pattern::Literal(self.convert_literal_kind_into_pattern(&token.kind))
            }
            // Tuple patterns
            Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            } => {
                self.skip_token();
                return self.parse_tuple_pattern(*tree_index, *span);
            }
            // Namespace patterns
            Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            } => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();

                disable_flag!(self; spread_patterns_allowed;
                    let pat = self.parse_namespace_pattern(tree, *span)?
                );

                Pattern::Namespace(pat)
            }
            // List pattern
            Token {
                kind: TokenKind::Tree(Delimiter::Bracket, tree_index),
                span,
            } => {
                self.skip_token();
                return self.parse_list_pattern(*tree_index, *span);
            }
            token => self.error_with_location(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::begin_pattern()),
                Some(token.kind),
                token.span,
            )?,
        };

        Ok(self.node_with_joined_span(pattern, &start))
    }

    /// Parse an arbitrary number of [Pattern]s which are comma separated.
    pub fn parse_pattern_collection(&self) -> AstGenResult<AstNodes<Pattern>> {
        self.parse_separated_fn(
            || self.parse_pattern(),
            || self.parse_token(TokenKind::Comma),
        )
    }

    /// Parse a [DestructuringPattern]. The [DestructuringPattern] refers to destructuring
    /// either a struct or a namespace to extract fields, exported members. The function
    /// takes in a token atom because both syntaxes use different operators as pattern
    /// assigners.
    pub(crate) fn parse_destructuring_pattern(
        &self,
    ) -> AstGenResult<AstNode<DestructuringPattern>> {
        let start = self.current_location();
        let name = self.parse_name()?;

        // if the next token is the correct assigning operator, attempt to parse a
        // pattern here, if not then we copy the parsed ident and make a binding
        // pattern.
        let pattern = match self.parse_token_fast(TokenKind::Keyword(Keyword::As)) {
            Some(_) => self.parse_pattern()?,
            None => {
                let span = name.span();
                let copy = self.node(Name { ..*name.body() });

                self.node_with_span(
                    Pattern::Binding(BindingPattern {
                        name: copy,
                        visibility: None,
                        mutability: None,
                    }),
                    span,
                )
            }
        };

        Ok(self.node_with_joined_span(DestructuringPattern { name, pattern }, &start))
    }

    /// Parse a collection of [DestructuringPattern]s that are comma separated within a brace
    /// tree.
    fn parse_namespace_pattern(
        &self,
        tree: &'stream Vec<Token>,
        span: Span,
    ) -> AstGenResult<NamespacePattern> {
        let gen = self.from_stream(tree, span);
        let mut fields = vec![];

        while gen.has_token() {
            match gen.peek_resultant_fn(|| gen.parse_destructuring_pattern()) {
                Some(pat) => fields.push(pat),
                None => break,
            }

            if gen.has_token() {
                gen.parse_token(TokenKind::Comma)?;
            }
        }

        // @@ErrorReporting: So here, there is a problem because we do actually want to report
        //                   that this should have been the end of the pattern but because in some
        //                   contexts the function is being peeked and the error is being ignored,
        //                   maybe there should be some mechanism to cause the function to hard error?
        gen.verify_is_empty()?;

        Ok(NamespacePattern {
            fields: AstNodes::new(fields, Some(span)),
        })
    }

    /// Parse a [Pattern::List] pattern from the token vector. A list [Pattern] consists
    /// of a list of comma separated within a square brackets .e.g `[x, 1, ..]`
    pub(crate) fn parse_list_pattern(
        &self,
        tree_index: usize,
        parent_span: Span,
    ) -> AstGenResult<AstNode<Pattern>> {
        let tree = self.token_trees.get(tree_index).unwrap();
        let gen = self.from_stream(tree, parent_span);

        enable_flag!(gen; spread_patterns_allowed;
            let fields = gen.parse_pattern_collection()?
        );

        Ok(self.node_with_span(Pattern::List(ListPattern { fields }), parent_span))
    }

    /// Parse a [Pattern::Tuple] from the token vector. A tuple pattern consists of
    /// nested patterns within parenthesees which might also have an optional
    /// named fields.
    ///
    /// If only a singular pattern is parsed and it doesn't have a name, then the
    /// function will assume that this is not a tuple pattern and simply a pattern
    /// wrapped within parenthesees.
    pub(crate) fn parse_tuple_pattern(
        &self,
        tree_index: usize,
        parent_span: Span,
    ) -> AstGenResult<AstNode<Pattern>> {
        let tree = self.token_trees.get(tree_index).unwrap();

        // check here if the tree length is 1, and the first token is the comma to check if it is an
        // empty tuple pattern...
        if let Some(token) = tree.get(0) {
            if token.has_kind(TokenKind::Comma) {
                return Ok(self.node_with_span(
                    Pattern::Tuple(TuplePattern {
                        fields: AstNodes::empty(),
                    }),
                    parent_span,
                ));
            }
        }

        // @@Hack: here it might actually be a nested pattern in parenthesees. So we perform a slight
        // transformation if the number of parsed patterns is only one. So essentially we handle the case
        // where a pattern is wrapped in parentheses and so we just unwrap it.
        let gen = self.from_stream(tree, parent_span);

        enable_flag!(gen; spread_patterns_allowed;
            // @@Cleanup: In the case that there is a single pattern and the user writes a `,` does this
            //            mean that this is still a singular pattern or if it is now treated as a tuple pattern?
            let mut elements = gen.parse_separated_fn(
                || gen.parse_tuple_pattern_entry(),
                || gen.parse_token(TokenKind::Comma),
            )?
        );

        // If there is no associated name with the entry and there is only one entry
        // then we can be sure that it is only a nested entry.
        if elements.len() == 1 && elements[0].name.is_none() {
            let element = elements.nodes.pop().unwrap().into_body();

            Ok(element.pattern)
        } else {
            Ok(self.node_with_span(
                Pattern::Tuple(TuplePattern { fields: elements }),
                parent_span,
            ))
        }
    }

    /// Parse an entry within a tuple pattern which might contain an optional [Name] node.
    pub(crate) fn parse_tuple_pattern_entry(&self) -> AstGenResult<AstNode<TuplePatternEntry>> {
        let start = self.current_location();

        let (name, pattern) = match self.peek() {
            Some(Token {
                kind: TokenKind::Ident(_),
                ..
            }) => {
                // Here if there is a '=', this means that there is a name attached to the entry within the
                // tuple pattern...
                match self.peek_second() {
                    Some(token) if token.has_kind(TokenKind::Eq) => {
                        let name = self.parse_name()?;
                        self.skip_token(); // '='

                        (Some(name), self.parse_pattern()?)
                    }
                    _ => (None, self.parse_pattern()?),
                }
            }
            _ => (None, self.parse_pattern()?),
        };

        Ok(self.node_with_joined_span(TuplePatternEntry { name, pattern }, &start))
    }

    /// Convert a [Literal] into a [LiteralPattern].
    pub(crate) fn convert_literal_kind_into_pattern(&self, kind: &TokenKind) -> LiteralPattern {
        match kind {
            TokenKind::StrLiteral(s) => LiteralPattern::Str(StrLiteralPattern(*s)),
            TokenKind::CharLiteral(s) => LiteralPattern::Char(CharLiteralPattern(*s)),
            TokenKind::IntLiteral(s) => LiteralPattern::Int(IntLiteralPattern(*s)),
            TokenKind::FloatLiteral(s) => LiteralPattern::Float(FloatLiteralPattern(*s)),
            TokenKind::Keyword(Keyword::False) => LiteralPattern::Bool(BoolLiteralPattern(false)),
            TokenKind::Keyword(Keyword::True) => LiteralPattern::Bool(BoolLiteralPattern(true)),
            _ => unreachable!(),
        }
    }

    /// Parse a spread operator from the current token tree. A spread operator can have an
    /// optional name attached to the spread operator on the right hand-side.
    ///
    /// ## Allowed locations
    /// So the spread operator can only appear within either `list`, `tuple` patterns at the moment
    /// which means that any other location will mark it as `invalid` in the current implementation.
    ///
    pub(crate) fn parse_spread_pattern(&self) -> AstGenResult<SpreadPattern> {
        for k in 0..3 {
            self.parse_token_fast(TokenKind::Dot).ok_or_else(|| {
                self.make_error(
                    AstGenErrorKind::MalformedSpreadPattern(3 - k),
                    None,
                    None,
                    Some(self.next_location()),
                )
            })?;
        }

        // Try and see if there is a identifier that is followed by the spread to try and
        // bind the capture to a variable
        let name = self.peek_resultant_fn(|| self.parse_name());

        Ok(SpreadPattern { name })
    }

    /// Function to parse a [BindingPattern] without considering whether it might be part of a
    /// constructor or any other form of pattern. This function also accounts for visibility or
    /// mutability modifiers on the binding pattern.
    fn parse_binding_pattern(&self) -> AstGenResult<Pattern> {
        let visibility = self.peek_resultant_fn(|| self.parse_visibility());

        // Parse a mutability modifier if any
        let mutability = self
            .parse_token_fast(TokenKind::Keyword(Keyword::Mut))
            .map(|_| self.node_with_span(Mutability::Mutable, self.current_location()));

        let name = self.parse_name()?; // @@Correctness: Should this be an access name?

        Ok(Pattern::Binding(BindingPattern {
            name,
            visibility,
            mutability,
        }))
    }

    /// Parse a [Visibility] modifier, either being a `pub` or `priv`.
    fn parse_visibility(&self) -> AstGenResult<AstNode<Visibility>> {
        match self.next_token() {
            Some(Token {
                kind: TokenKind::Keyword(Keyword::Pub),
                span,
            }) => Ok(self.node_with_span(Visibility::Public, *span)),
            Some(Token {
                kind: TokenKind::Keyword(Keyword::Priv),
                span,
            }) => Ok(self.node_with_span(Visibility::Private, *span)),
            token => self.error_with_location(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::begin_visibility()),
                token.map(|t| t.kind),
                token.map_or_else(|| self.next_location(), |t| t.span),
            ),
        }
    }

    /// Utility function to lookahead and see if it's possible to parse a singular pattern
    /// from the current position in the token stream.
    pub(crate) fn begins_pattern(&self) -> bool {
        let n_lookahead = match self.peek() {
            // Namespace, List, Tuple, etc.
            Some(Token {
                kind: TokenKind::Tree(_, _),
                ..
            }) => 1,
            // Identifier or constructor pattern
            Some(Token {
                kind: TokenKind::Ident(_),
                ..
            }) => match self.peek_second() {
                Some(Token {
                    kind: TokenKind::Tree(Delimiter::Paren, _),
                    ..
                }) => 2,
                _ => 1,
            },
            // This is the case for a bind that has a visibility modifier at the beginning. In
            // this scenario, it can be followed by a `mut` modifier and then a identifier or
            // just an identifier.
            Some(Token {
                kind: TokenKind::Keyword(Keyword::Priv | Keyword::Pub),
                ..
            }) => match self.peek_second() {
                Some(Token {
                    kind: TokenKind::Ident(_),
                    ..
                }) => 2,
                Some(Token {
                    kind: TokenKind::Keyword(Keyword::Mut),
                    ..
                }) => match self.peek_nth(3) {
                    Some(Token {
                        kind: TokenKind::Ident(_),
                        ..
                    }) => 3,
                    _ => return false,
                },
                _ => return false,
            },
            // This case covers the scenario where there is just a mutability modifier
            // in front of the name binding
            Some(Token {
                kind: TokenKind::Keyword(Keyword::Mut),
                ..
            }) => match self.peek_second() {
                Some(Token {
                    kind: TokenKind::Ident(_),
                    ..
                }) => 2,
                _ => return false,
            },
            _ => return false,
        };

        matches!(self.peek_nth(n_lookahead), Some(token) if token.has_kind(TokenKind::Colon))
    }
}
