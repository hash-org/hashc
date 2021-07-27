//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use hash_ast::{ast::*, error::ParseResult, location::Location, resolve::ModuleResolver};

use crate::token::Token;

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

    pub fn generate_module(&mut self) -> ParseResult<Module> {
        Ok(Module { contents: vec![] })
    }

    pub fn generate_statement(&mut self) -> ParseResult<AstNode<Statement>> {
        todo!()
    }

    /// Special variant of expression to handle interactive statements that have relaxed rules about
    /// semi-colons for some statements.
    pub fn generate_expression_from_interactive(&mut self) -> ParseResult<AstNode<BodyBlock>> {
        Ok(AstNode::new(
            BodyBlock {
                statements: vec![],
                expr: None,
            },
            Location::span(0, 0),
        ))
    }

    pub fn generate_pattern(&mut self) -> ParseResult<AstNode<Pattern>> {
        todo!()
    }

    pub fn generate_expression(&mut self) -> ParseResult<AstNode<Expression>> {
        todo!()
    }

    pub fn generate_literal(&mut self) -> ParseResult<AstNode<Literal>> {
        todo!()
    }
}
