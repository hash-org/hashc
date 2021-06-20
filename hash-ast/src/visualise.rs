//! Hash Compiler Frontend library file
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt;

use crate::ast::*;


impl<'ast> fmt::Display for Module<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl<'ast> fmt::Display for AstNode<'ast, Statement<'ast>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {

        // we first need to compute the children, including the height of the 
        // node so that we can compute the length of vertical lines to draw.
        // Everything else should be handeled by the implementation of the child 

        todo!()
        // let node_count = 0;

        // Ok(match *self.body {
        //     Statement::Expr(_) => {}
        //     Statement::Return(_) => {}
        //     Statement::Block(_) => {}
        //     Statement::Break => write!(f, "break"),
        //     Statement::Continue => write!(f, "continue"),
        //     Statement::Let(_) => {}
        //     Statement::Assign(_) => {}
        //     Statement::StructDef(_) => {}
        //     Statement::EnumDef(_) => {}
        //     Statement::TraitDef(_) => {}
        // })
    }
}

impl<'ast> fmt::Display for AstNode<'ast, Expression<'ast>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl<'ast> fmt::Display for AstNode<'ast, Block<'ast>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
