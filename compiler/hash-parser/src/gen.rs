//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use std::cell::Cell;

use hash_ast::{
    ast::*,
    error::{ParseError, ParseResult},
    ident::{Identifier, IDENTIFIER_MAP},
    location::{Location, SourceLocation},
    module::ModuleIdx,
    resolve::ModuleResolver,
};
use smallvec::smallvec;

use crate::{
    operator::Operator,
    token::{Delimiter, Token, TokenKind, TokenKindVector},
};

pub struct AstGen<'resolver, R> {
    offset: Cell<usize>,
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
            offset: Cell::new(0),
            resolver,
        }
    }

    #[inline(always)]
    pub(crate) fn offset(&self) -> usize {
        self.offset.get()
    }

    /// Function to peek at the nth token ahead of the current offset.
    pub(crate) fn peek_nth(&self, at: usize) -> Option<&Token> {
        self.stream.get(self.offset.get() + at)
    }

    pub(crate) fn peek(&self) -> Option<&Token> {
        self.peek_nth(0)
    }

    pub(crate) fn peek_second(&self) -> Option<&Token> {
        self.peek_nth(1)
    }

    /// Function that increases the offset of the next token
    pub(crate) fn next_token(&self) -> Option<&Token> {
        let value = self.stream.get(self.offset.get());

        if value.is_some() {
            // @@Dumbness: because Cell::update is unsafe
            self.offset.set(self.offset.get() + 1);
        }

        value
    }

    pub(crate) fn current_token(&self) -> &Token {
        self.stream.get(self.offset.get() - 1).unwrap()
    }

    /// Get the current location from the current token, if there is no token at the current
    /// offset, then the location of the last token is used,
    pub(crate) fn current_location(&self) -> Location {
        match self.stream.get(self.offset()) {
            Some(token) => token.span,
            None => (*self.stream.last().unwrap()).span,
        }
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    pub fn node<T>(&self, inner: T) -> AstNode<T> {
        AstNode::new(inner, self.current_location())
    }

    fn copy_name_node(&self, name: &AstNode<Name>) -> AstNode<Name> {
        self.node(Name { ..*name.body() })
    }

    pub(crate) fn unexpected_token_error(
        &self,
        kind: &TokenKind,
        expected: &TokenKindVector,
        location: &Location,
    ) -> ParseError {
        ParseError::Parsing {
            message: format!("Unexpected token '{}', expecting {}", kind, expected),
            src: SourceLocation {
                location: *location,
                module_index: ModuleIdx(0),
            },
        }
    }

    pub(crate) fn make_ident(&self, name: AstString, location: &Location) -> AstNode<Expression> {
        AstNode::new(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.from_joined_location(
                    AccessName {
                        path: smallvec![IDENTIFIER_MAP.create_ident(name)],
                    },
                    location,
                ),
                type_args: vec![],
            })),
            *location,
        )
    }

    pub(crate) fn make_ident_from_id(
        &self,
        id: &Identifier,
        location: Location,
    ) -> AstNode<Expression> {
        AstNode::new(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.from_joined_location(
                    AccessName {
                        path: smallvec![*id],
                    },
                    &location,
                ),
                type_args: vec![],
            })),
            location,
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
                message: "Expected the beginning of an expression here.".to_string(),
                src: SourceLocation {
                    location: self.current_location(),
                    module_index: ModuleIdx(0),
                },
            });
        }

        let token = token.unwrap();

        match &token.kind {
            kind if kind.is_unary_op() => self.parse_unary_expression(),

            // Handle primitive literals
            kind if kind.is_literal() => Ok(self.parse_literal()),
            TokenKind::Keyword(_) => todo!(),
            TokenKind::Ident(_) => self.parse_singular_expression(),

            // Handle tree literals
            TokenKind::Tree(Delimiter::Brace, _) => self.parse_block_or_braced_literal(),
            TokenKind::Tree(Delimiter::Bracket, _) => self.parse_array_literal(), // Could be an array index?
            TokenKind::Tree(Delimiter::Paren, _) => self.parse_expression_or_tuple(),

            kind => Err(ParseError::Parsing {
                message: format!("Unexpected token '{}' in the place of expression.", kind),
                src: SourceLocation {
                    location: token.span,
                    module_index: ModuleIdx(0), // @@ModuleIdx: sort out locations with sources and paths
                },
            }),
        }
    }

    pub fn parse_singular_expression(&self) -> ParseResult<AstNode<Expression>> {
        debug_assert!(matches!(self.current_token().kind, TokenKind::Ident(_)));

        // extract the identifier value and span from the current token
        let (ident, span) = match self.current_token() {
            Token {
                kind: TokenKind::Ident(id),
                span,
            } => (id, span),
            _ => unreachable!(),
        };

        let mut lhs_expr = self.make_ident_from_id(ident, *span);
        let mut last_is_type_args = false;

        // so here we need to peek to see if this is either a access_name, index_access, field access or a
        // function call...
        loop {
            if last_is_type_args {
                break;
            }

            match self.peek() {
                Some(next_token) => {
                    match &next_token.kind {
                        // Type arguments...
                        TokenKind::Lt => {
                            last_is_type_args = true;

                            let type_args = self.parse_type_args()?;

                            // we need to update the type args of the expression...
                            lhs_expr = match lhs_expr.kind() {
                                ExpressionKind::Variable(VariableExpr { name, type_args: _ }) => {
                                    AstNode::new(
                                        Expression::new(ExpressionKind::Variable(VariableExpr {
                                            name: name.clone(), // @@RedundantCopy: we should just update the type_args of the node rather than re-making it!
                                            type_args,
                                        })),
                                        lhs_expr.location().join(self.current_location()),
                                    )
                                }
                                _ => unreachable!(),
                            }
                        }
                        // Property access or infix function call
                        TokenKind::Dot => todo!(),
                        // Access name
                        TokenKind::Colon => todo!(),
                        // Array index access syntax: ident[...]
                        TokenKind::Tree(Delimiter::Bracket, _) => todo!(),
                        // Function call
                        TokenKind::Tree(Delimiter::Paren, _) => todo!(),
                        // Struct literal
                        TokenKind::Tree(Delimiter::Brace, _) => todo!(),
                        _ => break,
                    }
                }
                None => break,
            }
        }

        Ok(lhs_expr)
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

    pub fn parse_type_args(&self) -> ParseResult<AstNodes<Type>> {
        todo!()
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
