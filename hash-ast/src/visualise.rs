//! Hash Compiler Frontend library file
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt;

use crate::ast::*;


impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl fmt::Display for AstNode<Statement> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {

        // we first need to compute the children, including the height of the 
        // node so that we can compute the length of vertical lines to draw.
        // Everything else should be handeled by the implementation of the child 
        
        match *self.body {
            Statement::Expr(_) => {}
            Statement::Return(_) => {}
            Statement::Block(_) => {}
            Statement::Break => {}
            Statement::Continue => {}
            Statement::Let(_) => {}
            Statement::Assign(_) => {}
            Statement::StructDef(_) => {}
            Statement::EnumDef(_) => {}
            Statement::TraitDef(_) => {}
        }
        todo!()
    }
}

impl fmt::Display for AstNode<Expression> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl fmt::Display for AstNode<Block> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
