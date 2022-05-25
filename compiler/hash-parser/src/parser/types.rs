//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_alloc::row;
use hash_ast::{ast::*, ast_nodes, ident::Identifier};
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Parse a [Type]. This includes all forms of a [Type]. This function
    /// does not deal with any kind of [Type] annotation or [TypeFunctionDef] syntax.
    pub fn parse_type(&self) -> AstGenResult<'c, AstNode<'c, Type<'c>>> {
        let start = self.current_location();
        let initial_ty = self.parse_singular_type()?;

        if self.parse_token_atom_fast(TokenKind::Tilde).is_some() {
            let mut inner_tys = ast_nodes!(&self.wall; initial_ty);

            loop {
                inner_tys
                    .nodes
                    .push(self.parse_singular_type()?, &self.wall);

                match self.parse_token_atom_fast(TokenKind::Tilde) {
                    Some(_) => continue,
                    None => break,
                }
            }

            return Ok(self.node_with_joined_span(Type::Merged(MergedType(inner_tys)), &start));
        }

        Ok(initial_ty)
    }

    /// Parse a [Type]. This includes only singular forms of a type. This means that [Type::Merged]
    /// variant is not handled because it makes the `parse_type` function carry context from one call to
    /// the other.
    fn parse_singular_type(&self) -> AstGenResult<'c, AstNode<'c, Type<'c>>> {
        let token = self.peek().ok_or_else(|| {
            self.make_error(
                AstGenErrorKind::ExpectedType,
                None,
                None,
                Some(self.next_location()),
            )
        })?;

        let start = token.span;
        let variant = match &token.kind {
            TokenKind::Amp => {
                self.skip_token();

                // Check if this is a raw ref by checking if the keyword is present...
                let is_ref = match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Raw)) => {
                        self.skip_token();
                        true
                    }
                    _ => false,
                };

                match self.parse_type() {
                    Ok(ty) if is_ref => Type::RawRef(RawRefType(ty)),
                    Ok(ty) => Type::Ref(RefType(ty)),
                    err => return err,
                }
            }
            TokenKind::Ident(id) => {
                self.skip_token();

                let (name, _args) =
                    self.parse_name_with_type_args(self.node_with_span(*id, start))?;

                // @@TODO: return a type function call here... if it has arguments

                Type::Named(NamedType { name })
            }

            // Map or set type
            TokenKind::Tree(Delimiter::Brace, tree_index) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, token.span);

                let key_ty = gen.parse_type()?;

                match gen.peek() {
                    // This must be a map
                    Some(token) if token.has_kind(TokenKind::Colon) => {
                        gen.skip_token();

                        let value_ty = gen.parse_type()?;
                        gen.verify_is_empty()?;

                        Type::Map(MapType {
                            key: key_ty,
                            value: value_ty,
                        })
                    }
                    None => Type::Set(SetType(key_ty)),
                    Some(_) => gen.expected_eof()?,
                }
            }

            // List type
            TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, token.span);

                let inner_type = gen.parse_type()?;
                gen.verify_is_empty()?;

                Type::List(ListType { inner: inner_type })
            }

            // Tuple or function type
            TokenKind::Tree(Delimiter::Paren, _) => {
                self.parse_function_or_tuple_type()?.into_body().move_out()
            }
            kind => {
                self.error_with_location(AstGenErrorKind::ExpectedType, None, Some(*kind), start)?
            }
        };

        Ok(self.node_with_joined_span(variant, &start))
    }

    /// This parses some type arguments after an [AccessName], however due to the nature of the
    /// language grammar, since the [TokenKind] could be a [`TokenKind::Lt`] or `<`, it could
    /// also be a comparison rather than the beginning of a type argument. Therefore, we have to
    /// lookahead to see if there is another type followed by either a comma (which locks the
    /// `type_args`) or a closing [`TokenKind::Gt`].
    pub fn parse_type_args(&self, lt_eaten: bool) -> AstGenResult<'c, AstNodes<'c, Type<'c>>> {
        // Only parse is if the caller specifies that they haven't eaten an `lt`
        if !lt_eaten {
            self.parse_token_atom(TokenKind::Lt)?;
        }

        let start = self.current_location();
        let mut type_args = AstNodes::empty();

        loop {
            // Check if the type argument is parsed, if we have already encountered a comma, we
            // return a hard error because it has already started on a comma.
            match self.parse_type() {
                Ok(ty) => type_args.nodes.push(ty, &self.wall),
                Err(err) => return Err(err),
            };

            // Now consider if the bound is closing or continuing with a comma...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.skip_token();
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.skip_token();
                    break;
                }
                Some(token) => self.error(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::from_row(
                        row![&self.wall; TokenKind::Comma, TokenKind::Gt],
                    )),
                    Some(token.kind),
                )?,
                None => self.unexpected_eof()?,
            }
        }

        // Update the location of the type bound to reflect the '<' and '>' tokens...
        type_args.set_span(start.join(self.current_location()));
        Ok(type_args)
    }

    /// Parses a [Type::Fn] which involves a parenthesis token tree with some arbitrary
    /// number of comma separated types followed by a return [Type] that is preceded by an
    /// `thin-arrow` (->) after the parentheses. e.g. `(i32) -> str`
    pub fn parse_function_or_tuple_type(&self) -> AstGenResult<'c, AstNode<'c, Type<'c>>> {
        let start = self.current_location();

        let mut args = AstNodes::empty();
        let mut gen_has_comma = false;

        // handle the function arguments first by checking for parentheses
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            }) => {
                self.skip_token();

                // update the type argument span...
                args.span = Some(*span);

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                match gen.peek() {
                    // Handle special case where there is only one comma and no following items...
                    // Special edge case for '(,)' or an empty tuple type...
                    Some(token) if token.has_kind(TokenKind::Comma) && gen.stream.len() == 1 => {
                        gen.skip_token();
                    }
                    _ => {
                        args = gen.parse_separated_fn(
                            || {
                                let start = gen.current_location();

                                // Here we have to essentially try and parse a identifier. If this is the case and
                                // then there is a colon present then we have a named field.
                                let (name, ty) = match gen.peek_second() {
                                    Some(token) if token.has_kind(TokenKind::Colon) => {
                                        let ident = gen.parse_name()?;
                                        gen.skip_token(); // :

                                        (Some(ident), gen.parse_type()?)
                                    }
                                    _ => (None, gen.parse_type()?),
                                };

                                Ok(gen.node_with_joined_span(
                                    NamedFieldTypeEntry { name, ty },
                                    &start,
                                ))
                            },
                            || gen.parse_token_atom(TokenKind::Comma),
                        )?;
                    }
                };

                // Here we check that the token tree has a comma at the end to later determine if
                // this is a `GroupedType` or a `TupleType`...
                gen_has_comma = gen.current_token().has_kind(TokenKind::Comma);
            }
            Some(token) => self.error(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::from_row(
                    row![&self.wall; TokenKind::Delimiter(Delimiter::Paren, false)],
                )),
                Some(token.kind),
            )?,
            None => self.unexpected_eof()?,
        };

        // If there is an arrow '=>', then this must be a function type
        match self.peek_resultant_fn(|| self.parse_thin_arrow()) {
            Some(_) => {
                // Parse the return type here, and then give the function name
                Ok(self.node_with_joined_span(
                    Type::Fn(FnType {
                        args,
                        return_ty: self.parse_type()?,
                    }),
                    &start,
                ))
            }
            None => {
                // If there is only one entry in the args, and the last token in the entry is not a comma
                // then we can be sure that this a `GroupedType`.
                if gen_has_comma && args.len() == 1 && args[0].name.is_none() {
                    return Ok(self.node_with_joined_span(
                        Type::Grouped(GroupedType(
                            args.nodes.pop().unwrap().into_body().move_out().ty,
                        )),
                        &start,
                    ));
                }

                Ok(self.node_with_joined_span(Type::Tuple(TupleType { entries: args }), &start))
            }
        }
    }

    /// Parse an [AccessName] followed by optional [Type] arguments.
    pub fn parse_name_with_type_args(
        &self,
        ident: AstNode<'c, Identifier>,
    ) -> AstGenResult<'c, (AstNode<'c, AccessName<'c>>, Option<AstNodes<'c, Type<'c>>>)> {
        let name = self.parse_access_name(ident)?;

        // @@Speed: so here we want to be efficient about type_args, we'll just try to
        // see if the next token atom is a 'Lt' rather than using parse_token_atom
        // because it throws an error essentially and thus allocates a stupid amount
        // of strings which at the end of the day aren't even used...
        let args = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => {
                self.peek_resultant_fn(|| self.parse_type_args(false))
            }
            _ => None,
        };

        Ok((name, args))
    }
}
