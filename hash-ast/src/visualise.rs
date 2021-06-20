//! Hash Compiler Frontend library file
//!
//! All rights reserved 2021 (c) The Hash Language authors

// use std::fmt;
// use std::fmt::format;

use crate::ast::*;

const CROSS_PIPE: char = '├';
const CORNER_PIPE: char = '└';
const HORIZ_PIPE: char = '─';
const VERT_PIPE: char = '│';

const END_PIPE: &str = "└─";

pub trait NodeDisplay {
    fn node_display(&self) -> Vec<String>;
}

impl<T> std::fmt::Display for AstNode<'_, T>
where
    Self: NodeDisplay,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.node_display()
                .into_iter()
                .map(|mut line| {
                    line.push('\n');
                    line
                })
                .collect::<String>()
        )
    }
}

impl<'ast> NodeDisplay for Module<'ast> {
    fn node_display(&self) -> Vec<String> {
        todo!()
    }
}

impl<'ast> NodeDisplay for AstNode<'ast, Statement<'ast>> {
    fn node_display(&self) -> Vec<String> {
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

impl<'ast> NodeDisplay for AstNode<'ast, Import<'ast>> {
    fn node_display(&self) -> Vec<String> {
        vec![
            format!("import\n{}", END_PIPE),
            format!(" \"{}\"", self.path),
        ]
    }
}

impl<'ast> NodeDisplay for AstNode<'ast, Expression<'ast>> {
    fn node_display(&self) -> Vec<String> {
        todo!()
    }
}

impl<'ast> NodeDisplay for AstNode<'ast, Block<'ast>> {
    fn node_display(&self) -> Vec<String> {
        match &self.body {
            Block::Match(_match_body) => todo!(),
            Block::Loop(_loop_body) => {
                // first of all, we need to call format on all of the children statements
                // of the block and then compute the height of the formatted string by
                // just checking the number of lines that are in the resultant string.
                // let statements = ;
                todo!()
            }
            Block::Body(_body) => todo!(),
        }
    }
}
