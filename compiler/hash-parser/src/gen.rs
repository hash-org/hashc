//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use std::{cell::Cell, vec};

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

pub struct AstGen<'a, R> {
    offset: Cell<usize>,
    stream: Vec<Token>,
    resolver: &'a R,
}

impl<'a, R> AstGen<'a, R>
where
    R: ModuleResolver,
{
    pub fn new(stream: Vec<Token>, resolver: &'a R) -> Self {
        Self {
            stream,
            offset: Cell::new(0),
            resolver,
        }
    }

    pub fn from_stream(&self, stream: Vec<Token>) -> Self {
        Self {
            stream,
            offset: Cell::new(0),
            resolver: self.resolver,
        }
    }

    /// Function to create a [SourceLocation] from a [Location] by using the provided resolver
    fn source_location(&self, location: &Location) -> SourceLocation {
        match self.resolver.module_index() {
            Some(module_index) => SourceLocation {
                location: *location,
                module_index,
            },
            None => SourceLocation {
                location: *location,
                module_index: ModuleIdx(0),
            },
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

    /// Function to check if the token stream has been exhausted based on the current
    /// offset in the generator.
    pub(crate) fn has_token(&self) -> bool {
        let length = self.stream.len();

        match length {
            0 => false,
            _ => self.offset.get() < self.stream.len(),
        }
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

    /// Create a new [AstNode] from the information provided by the [AstGen]
    pub fn node_with_location<T>(&self, inner: T, location: Location) -> AstNode<T> {
        AstNode::new(inner, location)
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
            src: self.source_location(location),
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

    /// Function to peek ahead and match some parsing function that returns a [Option<T>] wrapped
    /// in a [ParseResult]. If The result is an error, or the option is [None], the function will
    /// reset the current offset of the token stream to where it was the function was peeked.
    pub fn peek_fn<T>(
        &self,
        parse_fn: impl Fn() -> ParseResult<Option<T>>,
    ) -> ParseResult<Option<T>> {
        let start = self.offset.get();

        match parse_fn() {
            result @ Ok(Some(_)) => result,
            err => {
                self.offset.set(start);
                err
            }
        }
    }

    pub fn parse_module(&self) -> ParseResult<Module> {
        // Let's begin by looping through
        Ok(Module { contents: vec![] })
    }

    pub fn parse_statement(&self) -> ParseResult<AstNode<Statement>> {
        todo!()
    }

    pub fn parse_expression_from_interactive(&self) -> ParseResult<AstNode<BodyBlock>> {
        // get the starting position
        let start = self.current_location();

        Ok(AstNode::new(
            BodyBlock {
                statements: vec![],
                expr: Some(self.parse_expression_bp(0)?),
            },
            start.join(self.current_location()),
        ))
    }

    pub fn parse_block(&self) {}

    pub fn parse_expression(&self) -> ParseResult<AstNode<Expression>> {
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
                src: self.source_location(&token.span),
            }),
        }
    }

    pub fn parse_singular_expression(&self) -> ParseResult<AstNode<Expression>> {
        debug_assert!(matches!(self.current_token().kind, TokenKind::Ident(_)));

        // extract the identifier value and span from the current token
        let ident = match self.current_token() {
            Token {
                kind: TokenKind::Ident(id),
                span: _,
            } => id,
            _ => unreachable!(),
        };

        // record the starting span
        let start = self.current_location();

        let (name, type_args) = self.parse_name_with_type_args(ident)?;
        let type_args = type_args.unwrap_or_default();

        let mut lhs_expr = self.node_with_location(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: name.clone(),
                type_args: type_args.clone(),
            })),
            start.join(self.current_location()),
        );

        // so here we need to peek to see if this is either a index_access, field access or a function call...
        while let Some(next_token) = self.peek() {
            match &next_token.kind {
                // Property access or infix function call
                TokenKind::Dot => {
                    self.next_token(); // eat the token since there isn't any alternative to being an ident or fn call.

                    let name_or_fn_call = self.parse_name_or_infix_call()?;
                    let kind = name_or_fn_call.into_body().into_kind();

                    match kind {
                        ExpressionKind::FunctionCall(FunctionCallExpr { subject, mut args }) => {
                            // @@Future: @@FunctionArguments:
                            // In the future when we consider function named arguments and optional arguments and variadic arguments,
                            // is it correct to apply the same behaviour of placing the argument first if it is an infix call ?
                            // The current behaviour is that the lhs is inserted as the first argument, but that might change:
                            //
                            // >>> foo.bar()
                            // vvv Is transpiled to..
                            // >>> bar(foo)
                            //
                            // Additionally, if the RHS has arguments, they are shifted for the LHS to be inserted as the first argument...
                            //
                            // >>> foo.bar(baz)
                            // vvv Is transpiled to..
                            // >>> bar(foo, baz)

                            // insert lhs_expr first...
                            args.entries.insert(0, lhs_expr);

                            lhs_expr = AstNode::new(
                                Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                                    subject,
                                    args,
                                })),
                                start.join(self.current_location()),
                            );
                        }
                        ExpressionKind::Variable(VariableExpr { name, type_args: _ }) => {
                            // @@Cleanup: This produces an AstNode<AccessName> whereas we just want the single name...
                            let location = name.location();
                            let ident = name.body().path.get(0).unwrap();

                            let node = self.node_with_location(Name { ident: *ident }, location);

                            lhs_expr = AstNode::new(
                                Expression::new(ExpressionKind::PropertyAccess(
                                    PropertyAccessExpr {
                                        subject: lhs_expr,
                                        property: node,
                                    },
                                )),
                                start.join(self.current_location()),
                            );
                        }
                        _ => {
                            return Err(ParseError::Parsing {
                                message: "Expected field name or an infix function call"
                                    .to_string(),
                                src: self.source_location(&self.current_location()),
                            })
                        }
                    }
                }
                // Array index access syntax: ident[...]
                TokenKind::Tree(Delimiter::Bracket, tree) => {
                    self.next_token();
                    lhs_expr = self.parse_array_index(&lhs_expr, tree)?;
                }
                // Function call
                TokenKind::Tree(Delimiter::Paren, tree) => {
                    self.next_token();
                    lhs_expr = self.parse_function_call(lhs_expr, tree, &next_token.span)?;
                }
                // Struct literal
                TokenKind::Tree(Delimiter::Brace, tree) => {
                    self.next_token();
                    lhs_expr = self.parse_struct_literal(&name, &type_args, tree)?;
                }
                _ => break,
            }
        }

        Ok(lhs_expr)
    }

    pub fn parse_function_call(
        &self,
        ident: AstNode<Expression>,
        tree: &[Token],
        span: &Location,
    ) -> ParseResult<AstNode<Expression>> {
        let gen = self.from_stream(tree.to_owned());
        let mut args = AstNode::new(FunctionCallArgs { entries: vec![] }, *span);

        while gen.has_token() {
            let arg = gen.parse_expression_bp(0);
            args.entries.push(arg?);

            // now we eat the next token, checking that it is a comma
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                _ => break,
            };
        }

        // form the span from the beginning variable expression to the end of the arguments...
        let span = &ident.location().join(self.current_location());

        Ok(self.node_with_location(
            Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                subject: ident,
                args,
            })),
            *span,
        ))
    }

    pub fn parse_struct_literal(
        &self,
        _ident: &AstNode<AccessName>,
        _type_args: &[AstNode<Type>],
        _tree: &[Token],
    ) -> ParseResult<AstNode<Expression>> {
        todo!()
    }

    pub fn parse_array_index(
        &self,
        _ident: &AstNode<Expression>,
        _tree: &[Token],
    ) -> ParseResult<AstNode<Expression>> {
        todo!()
    }

    pub fn parse_unary_expression(&self) -> ParseResult<AstNode<Expression>> {
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

    pub fn parse_name_with_type_args(
        &self,
        ident: &Identifier,
    ) -> ParseResult<(AstNode<AccessName>, Option<AstNodes<Type>>)> {
        let name = self.parse_access_name(ident)?;
        let args = self.peek_fn(|| self.parse_type_args())?;

        Ok((name, args))
    }

    /// Parse an [AccessName] from the current token stream. An [AccessName] is defined as
    /// a number of identifiers that are separated by the namespace operator '::'. The function
    /// presumes that the current token is an identifier an that the next token is a colon.
    pub fn parse_access_name(&self, start_id: &Identifier) -> ParseResult<AstNode<AccessName>> {
        let start = self.current_location();
        let mut path = smallvec![*start_id];

        loop {
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Colon) => {
                    self.next_token();

                    let second_colon = self.peek();

                    // Ensure the second colon is present...
                    if second_colon.is_none() || !second_colon.unwrap().has_kind(TokenKind::Colon) {
                        return Err(ParseError::Parsing {
                            message: "Expected ':' after the beginning of an namespace".to_string(),
                            src: self.source_location(&self.current_location()),
                        });
                    }

                    self.next_token();

                    match self.peek() {
                        Some(Token {
                            kind: TokenKind::Ident(id),
                            span: _,
                        }) => {
                            self.next_token();
                            path.push(*id);
                        }
                        _ => {
                            return Err(ParseError::Parsing {
                                message: "Expected identifier after a name access".to_string(),
                                src: self.source_location(&self.current_location()),
                            })
                        }
                    }
                }
                _ => break,
            }
        }

        Ok(AstNode::new(
            AccessName { path },
            start.join(self.current_location()),
        ))
    }

    /// Special variant of expression to handle interactive statements that have relaxed rules about
    /// semi-colons for some statements.
    pub fn parse_expression_bp(&self, min_prec: u8) -> ParseResult<AstNode<Expression>> {
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

    /// This parses some type args after an [AccessName], however due to the nature of the
    /// language grammar, since the [TokenKind] could be a `TokenKind::Lt` or `<`, it could
    /// also be a comparison rather than the beginning of a type argument. Therefore, we have to
    /// lookahead to see if there is another type followed by either a comma (which locks the
    /// type_args) or a closing `TokenKind::Gt`. Otherwise, we back track and let the expression
    /// be parsed as an order comparison.
    pub fn parse_type_args(&self) -> ParseResult<Option<AstNodes<Type>>> {
        // Ensure this is the beginning of a type_bound
        if self.peek().is_none() || !self.peek().unwrap().has_kind(TokenKind::Lt) {
            return Ok(None);
        }

        self.next_token();

        let mut type_args = vec![];
        let mut has_comma = false;

        loop {
            // Check if the type argument is parsed, if we have already encountered a comma, we
            // return a hard error because it has already started on a comma.
            match self.parse_type()? {
                Some(ty) => type_args.push(ty),
                _ if has_comma => {
                    return Err(ParseError::Parsing {
                        message: "Expected type argument in a type bound.".to_string(),
                        src: self.source_location(&self.current_location()),
                    })
                }
                _ => return Ok(None),
            };

            // Now consider if the bound is closing or continuing with a comma...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.next_token();
                    has_comma = true;
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.next_token();
                    break;
                }
                _ => return Ok(None),
            }
        }

        Ok(Some(type_args))
    }

    /// Function to parse a type
    pub fn parse_type(&self) -> ParseResult<Option<AstNode<Type>>> {
        let start = self.current_location();
        let token = self.peek();

        if token.is_none() {
            return Ok(None);
        }

        let variant = match token.unwrap().kind {
            TokenKind::Amp => {
                self.next_token();

                // @@TODO: raw_refs...
                match self.parse_type()? {
                    Some(ty) => Type::Ref(ty),
                    None => return Ok(None),
                }
            }
            TokenKind::Question => {
                self.next_token();
                Type::Existential
            }
            TokenKind::Ident(id) => {
                self.next_token();

                let (name, args) = self.parse_name_with_type_args(&id)?;
                // if the type_args are None, this means that the name could be either a
                // infer_type, or a type_var...
                match args {
                    Some(type_args) => Type::Named(NamedType { name, type_args }),
                    None => {
                        // @@Cleanup: This produces an AstNode<AccessName> whereas we just want the single name...
                        let location = name.location();
                        let ident = name.body().path.get(0).unwrap();

                        match IDENTIFIER_MAP.ident_name(*ident).as_str() {
                            "_" => Type::Infer,
                            // @@TypeArgsNaming: Here the rules are built-in for what the name of a type-arg is,
                            //                   a capital character of length 1...
                            ident_name => {
                                if ident_name.len() == 1
                                    && ident_name.chars().all(|x| x.is_ascii_uppercase())
                                {
                                    let name =
                                        self.node_with_location(Name { ident: *ident }, location);

                                    Type::TypeVar(TypeVar { name })
                                } else {
                                    Type::Named(NamedType {
                                        name,
                                        type_args: vec![],
                                    })
                                }
                            }
                        }
                    }
                }
            }
            _ => return Ok(None),
        };

        Ok(Some(AstNode::new(
            variant,
            start.join(self.current_location()),
        )))
    }

    pub fn parse_name_or_infix_call(&self) -> ParseResult<AstNode<Expression>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Dot));

        let start = self.current_location();

        match self.next_token() {
            Some(Token {
                kind: TokenKind::Ident(id),
                span: id_span,
            }) => match self.peek() {
                Some(Token {
                    kind: TokenKind::Tree(Delimiter::Paren, stream),
                    span,
                }) => {
                    // Eat the generator now...
                    self.next_token();

                    // @@Parallelisable: Since this is a vector of tokens, we should be able to give the resolver, create a new
                    //                   generator and form function call arguments from the stream...
                    let mut args = AstNode::new(FunctionCallArgs { entries: vec![] }, *span);

                    // so we know that this is the beginning of the function call, so we have to essentially parse an arbitrary number
                    // of expressions separated by commas as arguments to the call.
                    let gen = self.from_stream(stream.to_owned());

                    while gen.has_token() {
                        let arg = gen.parse_expression_bp(0);
                        args.entries.push(arg?);

                        // now we eat the next token, checking that it is a comma
                        match gen.peek() {
                            Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                            _ => break,
                        };
                    }

                    Ok(self.node_with_location(
                        Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                            subject: self.make_ident_from_id(id, *id_span),
                            args,
                        })),
                        start.join(self.current_location()),
                    ))
                }
                _ => Ok(self.make_ident_from_id(id, *id_span)),
            },
            _ => Err(ParseError::Parsing {
                message: "Expecting field name after property access.".to_string(),
                src: self.source_location(&self.current_location()),
            }),
        }
    }

    pub fn parse_block_or_braced_literal(&self) -> ParseResult<AstNode<Expression>> {
        todo!()
    }

    pub fn parse_pattern(&self) -> ParseResult<AstNode<Pattern>> {
        todo!()
    }

    pub fn parse_expression_or_tuple(&self) -> ParseResult<AstNode<Expression>> {
        todo!()
    }

    /// Convert the current token (provided it is a primitive literal) into a [ExpressionKind::LiteralExpr]
    /// by simply matching on the type of the expr.
    pub fn parse_literal(&self) -> AstNode<Expression> {
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

    pub fn parse_array_literal(&self) -> ParseResult<AstNode<Expression>> {
        todo!()
    }
}
