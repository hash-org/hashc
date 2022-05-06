//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_alloc::{collections::row::Row, row};
use hash_ast::{ast::*, ast_nodes, ident::CORE_IDENTIFIERS};
use hash_source::location::Location;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Parse a compound pattern.
    pub fn parse_pattern(&self) -> AstGenResult<'c, AstNode<'c, Pattern<'c>>> {
        // attempt to get the next token location as we're starting a pattern here, if there is no token
        // we should exit and return an error
        let start = self.next_location();

        // Parse the first pattern, but throw away the location information since that will be
        // computed at the end anyway...
        let mut patterns = ast_nodes![&self.wall;];

        while self.has_token() {
            let pattern = self.parse_pattern_with_if()?;
            patterns.nodes.push(pattern, &self.wall);

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
            let pat = patterns.nodes.pop().unwrap();
            Ok(pat)
        } else {
            Ok(self
                .node_with_joined_location(Pattern::Or(OrPattern { variants: patterns }), &start))
        }
    }

    /// Parse a function definition argument, which is made of an identifier and a function type.
    pub fn parse_function_def_arg(&self) -> AstGenResult<'c, AstNode<'c, FunctionDefArg<'c>>> {
        let name = self.parse_name()?;
        let start = name.location();

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

        Ok(self.node_with_joined_location(FunctionDefArg { name, ty, default }, &start))
    }

    /// Parse a function literal. Function literals are essentially definitions of lambdas
    /// that can be assigned to variables or passed as arguments into other functions.
    pub fn parse_function_literal(
        &self,
        gen: &Self,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let start = self.current_location();

        // parse function definition arguments.
        let args = gen.parse_separated_fn(
            || gen.parse_function_def_arg(),
            || gen.parse_token_atom(TokenKind::Comma),
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

        Ok(self.node_with_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                gen.node_with_joined_location(
                    Literal::Function(FunctionDef {
                        args,
                        return_ty,
                        fn_body,
                    }),
                    &start,
                ),
            ))),
            &start,
        ))
    }

    /// Parse a pattern with an optional if guard after the singular pattern.
    pub fn parse_pattern_with_if(&self) -> AstGenResult<'c, AstNode<'c, Pattern<'c>>> {
        let start = self.next_location();
        let pattern = self.parse_singular_pattern()?;

        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Keyword(Keyword::If)) => {
                self.skip_token();

                let condition = self.parse_expression_with_precedence(0)?;

                Ok(self.node_with_joined_location(
                    Pattern::If(IfPattern { pattern, condition }),
                    &start,
                ))
            }
            _ => Ok(pattern),
        }
    }

    /// Parse a pattern that can appear in declarations or for-loop destructuring locations
    pub fn parse_declaration_pattern(&self) -> AstGenResult<'c, AstNode<'c, Pattern<'c>>> {
        let start = self.next_location();
        let token = self
            .peek()
            .ok_or_else(|| self.make_error(AstGenErrorKind::EOF, None, None, None))?;

        let pattern = match token {
            Token {
                kind: TokenKind::Ident(ident),
                span,
            } => {
                // this could be either just a binding pattern, enum, or a struct pattern
                self.skip_token();

                // So here we try to parse an access name, if it is only made of a single binding
                // name, we'll just return this as a binding pattern, otherwise it must follow that
                // it is either a enum or struct pattern, if not we report it as an error since
                // access names cannot be used as binding patterns on their own...
                let name = self.parse_access_name(self.node_with_location(*ident, *span))?;

                match self.peek() {
                    // If this is just a identifier declaration
                    Some(token) if token.has_kind(TokenKind::Colon) => Pattern::Binding(
                        BindingPattern(self.node_with_location(Name { ident: *ident }, *span)),
                    ),
                    // Destructuring pattern for either struct or namespace
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                        span,
                    }) => {
                        self.skip_token();
                        let tree = self.token_trees.get(*tree_index).unwrap();

                        Pattern::Struct(StructPattern {
                            name,
                            fields: self.parse_destructuring_patterns(tree, *span)?,
                        })
                    }
                    // enum pattern
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                        span,
                    }) => {
                        self.skip_token();
                        let tree = self.token_trees.get(*tree_index).unwrap();

                        Pattern::Enum(EnumPattern {
                            name,
                            fields: self.parse_pattern_collection(tree, *span)?,
                        })
                    }
                    Some(token) if name.path.len() > 1 => self.error(
                        AstGenErrorKind::Expected,
                        Some(TokenKindVector::begin_pattern_collection(&self.wall)),
                        Some(token.kind),
                    )?,
                    _ => {
                        if *ident == CORE_IDENTIFIERS.underscore {
                            Pattern::Ignore(IgnorePattern)
                        } else {
                            Pattern::Binding(BindingPattern(
                                self.node_with_location(Name { ident: *ident }, *span),
                            ))
                        }
                    }
                }
            }
            // Tuple patterns
            Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            } => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();

                // check here if the tree length is 1, and the first token is the comma to check if it is an
                // empty tuple pattern...
                if let Some(token) = tree.get(0) {
                    if token.has_kind(TokenKind::Comma) {
                        return Ok(self.node_with_location(
                            Pattern::Tuple(TuplePattern {
                                fields: AstNodes::empty(),
                            }),
                            *span,
                        ));
                    }
                }

                // @@Hack: here it might actually be a nested pattern in parenthesees. So we perform a slight
                // transformation if the number of parsed patterns is only one. So essentially we handle the case
                // where a pattern is wrapped in parentheses and so we just unwrap it.
                let gen = self.from_stream(tree, *span);

                let mut elements = gen.parse_separated_fn(
                    || gen.parse_tuple_pattern_entry(),
                    || gen.parse_token_atom(TokenKind::Comma),
                )?;

                // If there is no associated name with the entry and there is only one entry
                // then we can be sure that it is only a nested entry.
                if elements.len() == 1 && elements[0].name.is_none() {
                    let element = elements.nodes.pop().unwrap();
                    return Ok(element.into_body().move_out().pattern);
                } else {
                    Pattern::Tuple(TuplePattern { fields: elements })
                }
            }
            // Namespace patterns
            Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            } => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();

                Pattern::Namespace(NamespacePattern {
                    fields: self.parse_destructuring_patterns(tree, *span)?,
                })
            }
            // @@Future: List patterns aren't supported yet.
            // Token {kind: TokenKind::Tree(Delimiter::Bracket, tree), span} => {
            //                 self.skip_token();
            //     // this is a list pattern
            //
            // }
            token => self.error_with_location(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::begin_pattern(&self.wall)),
                Some(token.kind),
                token.span,
            )?,
        };

        Ok(self.node_with_joined_location(pattern, &start))
    }

    /// Parse a pattern collect which can involve an arbitrary number of patterns which
    /// are comma separated.
    pub fn parse_pattern_collection(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: Location,
    ) -> AstGenResult<'c, AstNodes<'c, Pattern<'c>>> {
        let gen = self.from_stream(tree, span);

        gen.parse_separated_fn(
            || gen.parse_pattern(),
            || gen.parse_token_atom(TokenKind::Comma),
        )
    }

    /// Parse a destructuring pattern. The destructuring pattern refers to destructuring
    /// either a struct or a namespace to extract fields, exported members. The function
    /// takes in a token atom because both syntaxes use different operators as pattern
    /// assigners.
    pub fn parse_destructuring_pattern(
        &self,
    ) -> AstGenResult<'c, AstNode<'c, DestructuringPattern<'c>>> {
        let start = self.current_location();
        let name = self.parse_name()?;

        // if the next token is the correct assigning operator, attempt to parse a
        // pattern here, if not then we copy the parsed ident and make a binding
        // pattern.
        let pattern = match self.peek_resultant_fn(|| self.parse_token_atom(TokenKind::Eq)) {
            Some(_) => self.parse_pattern()?,
            None => {
                let copy = self.node(Name { ..*name.body() });
                let loc = copy.location();
                self.node_with_location(Pattern::Binding(BindingPattern(copy)), loc)
            }
        };

        Ok(self.node_with_joined_location(DestructuringPattern { name, pattern }, &start))
    }

    /// Parse a collection of destructuring patterns that are comma separated.
    pub fn parse_destructuring_patterns(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: Location,
    ) -> AstGenResult<'c, AstNodes<'c, DestructuringPattern<'c>>> {
        let gen = self.from_stream(tree, span);

        let mut patterns = AstNodes::new(row![&self.wall;], Some(span));

        while gen.has_token() {
            match gen.peek_resultant_fn(|| gen.parse_destructuring_pattern()) {
                Some(pat) => patterns.nodes.push(pat, &self.wall),
                None => break,
            }

            if gen.has_token() {
                gen.parse_token_atom(TokenKind::Comma)?;
            }
        }

        Ok(patterns)
    }

    /// Parse an entry within a tuple pattern which might contain an optional [Name] node.
    pub fn parse_tuple_pattern_entry(
        &self,
    ) -> AstGenResult<'c, AstNode<'c, TuplePatternEntry<'c>>> {
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

        Ok(self.node_with_joined_location(TuplePatternEntry { name, pattern }, &start))
    }

    /// Parse a singular pattern. Singular patterns cannot have any grouped pattern
    /// operators such as a '|', if guards or any form of compound pattern.
    pub fn parse_singular_pattern(&self) -> AstGenResult<'c, AstNode<'c, Pattern<'c>>> {
        let token = self
            .peek()
            .ok_or_else(|| self.make_error(AstGenErrorKind::EOF, None, None, None))?;

        let pattern = match token {
            Token {
                kind: TokenKind::Ident(ident),
                span,
            } => {
                // this could be either just a binding pattern, enum, or a struct pattern
                self.skip_token();

                // So here we try to parse an access name, if it is only made of a single binding
                // name, we'll just return this as a binding pattern, otherwise it must follow that
                // it is either a enum or struct pattern, if not we report it as an error since
                // access names cannot be used as binding patterns on their own...
                let name = self.parse_access_name(self.node_with_location(*ident, *span))?;

                match self.peek() {
                    // Destructuring pattern for either struct or namespace
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                        span,
                    }) => {
                        self.skip_token();
                        let tree = self.token_trees.get(*tree_index).unwrap();

                        Pattern::Struct(StructPattern {
                            name,
                            fields: self.parse_destructuring_patterns(tree, *span)?,
                        })
                    }
                    // enum_pattern
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                        span,
                    }) => {
                        self.skip_token();
                        let tree = self.token_trees.get(*tree_index).unwrap();

                        Pattern::Enum(EnumPattern {
                            name,
                            fields: self.parse_pattern_collection(tree, *span)?,
                        })
                    }
                    Some(token) if name.path.len() > 1 => self.error(
                        AstGenErrorKind::Expected,
                        Some(TokenKindVector::begin_pattern_collection(&self.wall)),
                        Some(token.kind),
                    )?,
                    _ => {
                        if *ident == CORE_IDENTIFIERS.underscore {
                            Pattern::Ignore(IgnorePattern)
                        } else {
                            Pattern::Binding(BindingPattern(
                                self.node_with_location(Name { ident: *ident }, *span),
                            ))
                        }
                    }
                }
            }
            token if token.kind.is_literal() => {
                self.skip_token();
                Pattern::Literal(self.convert_literal_kind_into_pattern(&token.kind))
            }
            Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            } => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();

                // check here if the tree length is 1, and the first token is the comma to check if it is an
                // empty tuple pattern...
                if let Some(token) = tree.get(0) {
                    if token.has_kind(TokenKind::Comma) {
                        return Ok(self.node_with_location(
                            Pattern::Tuple(TuplePattern {
                                fields: AstNodes::empty(),
                            }),
                            *span,
                        ));
                    }
                }

                // @@Hack: here it might actually be a nested pattern in parenthesees. So we perform a slight
                // transformation if the number of parsed patterns is only one. So essentially we handle the case
                // where a pattern is wrapped in parentheses and so we just unwrap it.
                let gen = self.from_stream(tree, *span);

                let mut elements = gen.parse_separated_fn(
                    || gen.parse_tuple_pattern_entry(),
                    || gen.parse_token_atom(TokenKind::Comma),
                )?;

                // If there is no associated name with the entry and there is only one entry
                // then we can be sure that it is only a nested entry.
                if elements.len() == 1 && elements[0].name.is_none() {
                    let element = elements.nodes.pop().unwrap();
                    return Ok(element.into_body().move_out().pattern);
                } else {
                    Pattern::Tuple(TuplePattern { fields: elements })
                }
            }
            Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            } => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();

                Pattern::Namespace(NamespacePattern {
                    fields: self.parse_destructuring_patterns(tree, *span)?,
                })
            }
            // @@Future: List patterns aren't supported yet.
            // Token {kind: TokenKind::Tree(Delimiter::Bracket, tree), span} => {
            //                 self.skip_token();
            //     // this is a list pattern
            //
            // }
            token => self.error_with_location(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::begin_pattern(&self.wall)),
                Some(token.kind),
                token.span,
            )?,
        };

        Ok(self.node_with_joined_location(pattern, &token.span))
    }

    /// Convert a literal kind into a pattern literal kind.
    pub fn convert_literal_kind_into_pattern(&self, kind: &TokenKind) -> LiteralPattern {
        match kind {
            TokenKind::StrLiteral(s) => LiteralPattern::Str(StrLiteralPattern(*s)),
            TokenKind::CharLiteral(s) => LiteralPattern::Char(CharLiteralPattern(*s)),
            TokenKind::IntLiteral(s) => LiteralPattern::Int(IntLiteralPattern(*s)),
            TokenKind::FloatLiteral(s) => LiteralPattern::Float(FloatLiteralPattern(*s)),
            _ => unreachable!(),
        }
    }
}
