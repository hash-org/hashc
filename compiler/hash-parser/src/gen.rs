//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use hash_ast::{
    ast::*,
    error::{ParseError, ParseResult},
    ident::IDENTIFIER_MAP,
    location::{Location, SourceLocation},
    module::ModuleIdx,
    resolve::ModuleResolver,
};

use crate::{
    operator::Operator,
    token::{Delimiter, Token, TokenKind},
};

pub struct AstGen<'resolver, R> {
    offset: usize,
    stream: Vec<Token>,
    resolver: &'resolver mut R,
}

impl<'resolver, R> AstGen<'resolver, R>
where
    R: ModuleResolver,
{
    pub fn new(stream: Vec<Token>, resolver: &'resolver mut R) -> Self {
        Self {
            stream,
            offset: 0,
            resolver,
        }
    }

    /// Function to peek at the nth token ahead of the current offset.
    pub(crate) fn peek_nth(&self, at: usize) -> Option<&Token> {
        self.stream.get(self.offset + at)
    }

    pub(crate) fn peek(&self) -> Option<&Token> {
        self.peek_nth(0)
    }

    pub(crate) fn peek_second(&self) -> Option<&Token> {
        self.peek_nth(1)
    }

    /// Function that increases the offset of the next token
    pub(crate) fn next_token(&mut self) -> Option<&Token> {
        let value = self.stream.get(self.offset);

        if value.is_some() {
            self.offset += 1;
        }

        value
    }

    pub(crate) fn current_token(&self) -> &Token {
        self.stream.get(self.offset - 1).unwrap()
    }

    /// Get the current location from the current token, if there is no token at the current
    /// offset, then the location of the last token is used,
    pub(crate) fn current_location(&self) -> Location {
        match self.stream.get(self.offset) {
            Some(token) => token.span,
            None => (*self.stream.last().unwrap()).span,
        }
    }

    pub(crate) fn make_ident(&self, name: AstString, location: &Location) -> AstNode<Expression> {
        AstNode::new(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.from_joined_location(
                    AccessName {
                        path: IDENTIFIER_MAP.create_path_ident(name),
                    },
                    location,
                ),
                type_args: vec![],
            })),
            *location,
        )
    }

    pub(crate) fn make_ident_from_op(
        &self,
        op: Operator,
        location: &Location,
    ) -> AstNode<Expression> {
        self.make_ident(AstString::Owned(op.as_str().to_owned()), location)
    }

    pub(crate) fn from_location<T>(&self, body: T, location: &Location) -> AstNode<T> {
        AstNode::new(body, *location)
    }

    pub(crate) fn from_joined_location<T>(&self, body: T, start: &Location) -> AstNode<T> {
        AstNode::new(body, start.join(self.current_location()))
    }

    pub fn parse_module(&mut self) -> ParseResult<Module> {
        // Let's begin by looping through
        Ok(Module { contents: vec![] })
    }

    pub fn parse_statement(&mut self) -> ParseResult<AstNode<Statement>> {
        todo!()
    }

    pub fn parse_block(&mut self) {}

    pub fn parse_expression_from_interactive(&mut self) -> ParseResult<AstNode<BodyBlock>> {
        // get the starting position
        let start = self.current_location();

        // let mut statements = vec![];
        // let mut expr = None;
        Ok(AstNode::new(
            BodyBlock {
                statements: vec![],
                expr: Some(self.parse_expression_bp(0)?),
            },
            start.join(self.current_location()),
        ))
    }

    pub fn parse_expression(&mut self) -> ParseResult<AstNode<Expression>> {
        let token = self.next_token();

        if token.is_none() {
            return Err(ParseError::Parsing {
                message: "Expected a binary operator after an expression.".to_string(),
                src: SourceLocation {
                    location: self.current_location(),
                    module_index: ModuleIdx(0),
                },
            });
        }

        let token = token.unwrap();

        match &token.kind {
            kind if kind.is_unary_op() => self.parse_unary_expression(),
            TokenKind::Keyword(_) => todo!(),
            TokenKind::Ident(_) => todo!(),

            // Handle tree literals
            TokenKind::Tree(Delimiter::Brace, _) => self.parse_block_or_braced_literal(),
            TokenKind::Tree(Delimiter::Bracket, _) => self.parse_array_literal(), // Could be an array index?
            TokenKind::Tree(Delimiter::Paren, _) => self.parse_expression_or_tuple(),


            // Handle primitive literals
            TokenKind::IntLiteral(_)
            | TokenKind::FloatLiteral(_)
            | TokenKind::CharLiteral(_)
            | TokenKind::StrLiteral(_) => Ok(self.parse_literal()),

            // Handle a special error if... @@Incomplete
            kind @ TokenKind::Semi => Err(ParseError::Parsing {
                message: format!("Expected expression instead of empty item. Consider removing the additional '{}'", kind),
                src: SourceLocation {
                    location: (*token).span,
                    module_index: ModuleIdx(0), // @@ModuleIdx: sort out locations with sources and paths
                },
            }),
            kind => Err(ParseError::Parsing {
                message: format!("Unexpected token '{}' in the place of expression.", kind),
                src: SourceLocation {
                    location: (*token).span,
                    module_index: ModuleIdx(0), // @@ModuleIdx: sort out locations with sources and paths
                },
            }),
        }
    }

    pub fn parse_unary_expression(&mut self) -> ParseResult<AstNode<Expression>> {
        let token = self.current_token();
        let start = self.current_location();

        let expr_kind = match &token.kind {
            TokenKind::Star => ExpressionKind::Deref(self.parse_expression()?),
            TokenKind::Amp => ExpressionKind::Ref(self.parse_expression()?),
            TokenKind::Plus | TokenKind::Minus => todo!(),
            TokenKind::Tilde => {
                let arg = self.parse_expression()?;
                let loc = arg.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident(AstString::Borrowed("notb"), &start),
                    args: self.from_location(FunctionCallArgs { entries: vec![arg] }, &loc),
                })
            }
            TokenKind::Exclamation => {
                let arg = self.parse_expression()?;
                let loc = arg.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident(AstString::Borrowed("not"), &start),
                    args: self.from_location(FunctionCallArgs { entries: vec![arg] }, &loc),
                })
            }
            kind => panic!("Expected token to be a unary operator, but got '{}'", kind),
        };

        Ok(self.from_joined_location(Expression::new(expr_kind), &start))
    }

    /// Special variant of expression to handle interactive statements that have relaxed rules about
    /// semi-colons for some statements.
    pub fn parse_expression_bp(&mut self, min_prec: u8) -> ParseResult<AstNode<Expression>> {
        // first of all, we want to get the lhs...
        let mut lhs = self.parse_expression()?;

        loop {
            let op_start = self.current_location();
            // this doesn't consider operators that have an 'eq' variant because that is handled at the statement level,
            // since it isn't really a binary operator...
            let (op, consumed_tokens) = Operator::from_token_stream(self);

            match op {
                None => break,
                Some(op) => {
                    // consume the number of tokens eaten whilst getting the operator...
                    (0..consumed_tokens).for_each(|_| {
                        self.next_token();
                    });

                    let op_span = op_start.join(self.current_location());

                    // check if we have higher precedence than the lhs expression...
                    let (l_prec, r_prec) = op.infix_binding_power();

                    if l_prec < min_prec {
                        break;
                    }

                    let rhs = self.parse_expression_bp(r_prec)?;

                    // now convert the Operator into a function call...
                    lhs = AstNode::new(
                        Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                            subject: self.make_ident_from_op(op, &op_span),
                            args: self.from_joined_location(
                                FunctionCallArgs {
                                    entries: vec![lhs, rhs],
                                },
                                &op_span,
                            ),
                        })),
                        op_span,
                    )
                }
            }
        }

        Ok(lhs)
    }

    pub fn parse_block_or_braced_literal(&mut self) -> ParseResult<AstNode<Expression>> {
        todo!()
    }

    pub fn parse_pattern(&mut self) -> ParseResult<AstNode<Pattern>> {
        todo!()
    }

    pub fn parse_expression_or_tuple(&mut self) -> ParseResult<AstNode<Expression>> {
        todo!()
    }

    /// Convert the current token (provided it is a primitive literal) into a [ExpressionKind::LiteralExpr]
    /// by simply matching on the type of the expr.
    pub fn parse_literal(&mut self) -> AstNode<Expression> {
        let token = self.current_token();
        let literal = AstNode::new(
            match token.kind {
                TokenKind::IntLiteral(num) => Literal::Int(num),
                TokenKind::FloatLiteral(num) => Literal::Float(num),
                TokenKind::CharLiteral(ch) => Literal::Char(ch),
                TokenKind::StrLiteral(_str) => {
                    panic!("StringLiteral ids haven't been implemented yet!")
                } //Literal::Str(str),
                _ => unreachable!(),
            },
            token.span,
        );

        AstNode::new(
            Expression::new(ExpressionKind::LiteralExpr(literal)),
            token.span,
        )
    }

    pub fn parse_array_literal(&mut self) -> ParseResult<AstNode<Expression>> {
        todo!()
    }
}
