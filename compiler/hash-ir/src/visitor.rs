//! Hash Compiler Intermediate Representation (IR) crate.

use std::process::Output;

use crate::{
    ir::{BasicBlock, Body, RValue, Statement, Terminator},
    IrStorage,
};

pub trait IrVisitor<'ir> {
    type Output;

    fn storage(&self) -> &'ir IrStorage;

    fn visit_body(&mut self, body: &'ir Body) -> Output;

    fn visit_block(&mut self, block: BasicBlock) -> Output;

    fn visit_statement(&mut self, statement: &'ir Statement) -> Output;

    fn visit_rvalue(&mut self, value: &'ir RValue) -> Output;

    fn visit_terminator(&mut self, terminator: &'ir Terminator) -> Output;
}
