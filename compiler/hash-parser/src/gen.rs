//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use hash_alloc::{collections::row::Row, row, Castle};
use hash_ast::{ast::*, error::ParseResult, location::Location, resolve::ModuleResolver};

use crate::token::Token;

pub struct AstGen<'c, 'resolver, R> {
    offset: usize,
    stream: Row<'c, Token<'c>>,
    resolver: &'resolver mut R,
    castle: &'c Castle,
}

impl<'c, 'resolver, R> AstGen<'c, 'resolver, R>
where
    R: ModuleResolver,
{
    pub fn new(stream: Row<'c, Token<'c>>, resolver: &'resolver mut R, castle: &'c Castle) -> Self {
        Self {
            stream,
            offset: 0,
            resolver,
            castle,
        }
    }

    pub fn generate_module(&mut self) -> ParseResult<Module<'c>> {
        let wall = self.castle.wall();
        Ok(Module {
            contents: row![&wall],
        })
    }

    pub fn generate_statement(&mut self) -> ParseResult<AstNode<Statement>> {
        todo!()
    }

    /// Special variant of expression to handle interactive statements that have relaxed rules about
    /// semi-colons for some statements.
    pub fn generate_expression_from_interactive(
        &mut self,
    ) -> ParseResult<AstNode<'c, BodyBlock<'c>>> {
        let wall = self.castle.wall();
        Ok(AstNode::new(
            BodyBlock {
                statements: row![&wall],
                expr: None,
            },
            Location::span(0, 0),
            &wall,
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
