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

impl<T> std::fmt::Display for AstNode<T>
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

impl NodeDisplay for Module {
    fn node_display(&self) -> Vec<String> {
        todo!()
    }
}

impl NodeDisplay for AstNode<Statement> {
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

impl NodeDisplay for AstNode<Import> {
    fn node_display(&self) -> Vec<String> {
        vec![
            format!("import\n{}", END_PIPE),
            format!(" \"{}\"", self.path),
        ]
    }
}

impl NodeDisplay for AstNode<Expression> {
    fn node_display(&self) -> Vec<String> {
        todo!()
    }
}

impl NodeDisplay for AstNode<Block> {
    fn node_display(&self) -> Vec<String> {
        match self.body.as_ref() {
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
