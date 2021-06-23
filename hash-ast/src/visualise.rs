//! Hash Compiler Frontend library file
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt::Alignment;

use crate::ast::*;

// const CROSS_PIPE: char = '├';
// const CORNER_PIPE: char = '└';
// const HORIZ_PIPE: char = '─';
const VERT_PIPE: &str = "│";

const END_PIPE: &str = "└─";
const MID_PIPE: &str = "├─";

pub trait NodeDisplay {
    fn node_display(&self, indent: usize) -> Vec<String>;
}

/// Utility function to pad a string based on [Alignment]
fn pad_str(line: &str, pad_char: char, padding: usize, alignment: Alignment) -> String {
    // compute side padding based on the alignment
    let (left_pad, right_pad) = match alignment {
        Alignment::Left => (padding, 0),
        Alignment::Right => (0, padding),
        Alignment::Center => (padding / 2, padding / 2),
    };

    // pad the string as specified
    let mut s = String::new();

    for _ in 0..left_pad {
        s.push(pad_char)
    }
    s.push_str(line);
    for _ in 0..right_pad {
        s.push(pad_char)
    }

    s
}

impl<T> std::fmt::Display for AstNode<'_, T>
where
    Self: NodeDisplay,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.node_display(0)
                .into_iter()
                .map(|mut line| {
                    line.push('\n');
                    line
                })
                .collect::<String>()
        )
    }
}

///
/// We need a seperate implementation for [Module] since it won't be wrapped within
/// an [AstNode] unlike all the other variants
///
impl<'ast> std::fmt::Display for Module<'ast> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nodes: Vec<Vec<String>> = self.contents.iter().map(|s| s.node_display(0)).collect();

        writeln!(f, "module")?;

        for (count, node) in nodes.iter().enumerate() {
            // determine the connector that should be use to join the nodes
            let (connector, ending) = if count == nodes.len() - 1 {
                (END_PIPE, "")
            } else {
                (MID_PIPE, VERT_PIPE)
            };

            // println!("{:?}", node);
            writeln!(f, "{}{}\n{}", connector, node.join("\n"), ending)?;
        }

        write!(f, "\n")
    }
}

impl<'ast> NodeDisplay for AstNode<'ast, Literal<'ast>> {
    fn node_display(&self, indent: usize) -> Vec<String> {
        let mut lines = vec![];
        let mut next_lines = vec![];

        match &self.body {
            Literal::Str(s) => lines.push(format!("string \"{}\"", s)),
            Literal::Char(c) => lines.push(format!("char \'{}\'", c)),
            Literal::Int(i) => lines.push(format!("number {}", i)),
            Literal::Float(f) => lines.push(format!("float {}", f)),

            // all these variants have the possibility of containing multiple elements, so
            // we have to evaluate the children first and then construct the branches...
            Literal::Set(set_lit) => {
                lines.push(format!("set"));

                // convert all the children and add them to the new lines
                for (index, element) in set_lit.elements.iter().enumerate() {
                    let connector = if index == set_lit.elements.len() - 1 {
                        END_PIPE
                    } else {
                        MID_PIPE
                    };

                    // reset the indent here since we'll be doing indentation here...
                    let child_lines = element.node_display(0);

                    for (child_index, line) in child_lines.iter().enumerate() {
                        // @@Speed: is this really the best way to deal with string concatination.
                        if child_index == 0 {
                            next_lines.push(format!("{}{}", connector, line));
                        } else {
                            next_lines.push(format!("|{}", line));
                        }
                    }
                }
            }
            Literal::Map(_map_lit) => {}
            Literal::List(_list_lit) => {}
            Literal::Tuple(_tup_lit) => {}
            Literal::Struct(_struct_lit) => {}
            Literal::Function(_fn_lit) => {}
        };

        // @@Cleanup: can we make this transformation generic, so we don't have to call it at the end of each implementation??
        // we need to pad each line by the number of spaces specified by 'ident'
        let next_lines: Vec<String> = next_lines
            .into_iter()
            .map(|line| pad_str(line.as_str(), ' ', indent, Alignment::Left))
            .collect();

        lines.extend(next_lines);
        lines
    }
}

impl<'ast> NodeDisplay for AstNode<'ast, Statement<'ast>> {
    fn node_display(&self, indent: usize) -> Vec<String> {
        let mut lines = vec![];
        let mut next_lines = vec![];
        let next_indent = indent + 2;

        match &self.body {
            Statement::Expr(expr) => lines.extend(expr.node_display(next_indent)),
            Statement::Return(expr) => {
                lines.push(format!("ret"));

                // if a return statement has a lin
                if let Some(ret_expr) = expr {
                    next_lines.push(format!(
                        "{}{}",
                        END_PIPE,
                        ret_expr.node_display(next_indent).join("\n")
                    ));
                }
            }
            Statement::Block(_block) => {
                todo!()
            }
            Statement::Break => lines.push(format!("break")),
            Statement::Continue => lines.push(format!("continue")),
            Statement::Let(_decl) => todo!(),
            Statement::Assign(_decl) => todo!(),
            Statement::StructDef(_def) => todo!(),
            Statement::EnumDef(_def) => todo!(),
            Statement::TraitDef(_def) => todo!(),
        };

        // we need to pad each line by the number of spaces specified by 'ident'
        let mut lines: Vec<String> = lines
            .into_iter()
            .map(|line| pad_str(line.as_str(), ' ', indent, Alignment::Left))
            .collect();

        let next_lines: Vec<String> = next_lines
            .into_iter()
            .map(|line| pad_str(line.as_str(), ' ', next_indent, Alignment::Left))
            .collect();

        lines.extend(next_lines);
        lines
    }
}

impl<'ast> NodeDisplay for AstNode<'ast, Import<'ast>> {
    fn node_display(&self, _indent: usize) -> Vec<String> {
        vec![format!("import"), format!("{} \"{}\"", END_PIPE, self.path)]
    }
}

impl<'ast> NodeDisplay for AstNode<'ast, Expression<'ast>> {
    fn node_display(&self, indent: usize) -> Vec<String> {
        match &self.body {
            Expression::FunctionCall(_) => todo!(),
            Expression::Intrinsic(_) => todo!(),
            Expression::LogicalOp(_) => todo!(),
            Expression::Variable(_) => todo!(),
            Expression::PropertyAccess(_) => todo!(),
            Expression::Index(_) => todo!(),
            Expression::Ref(_) => todo!(),
            Expression::Deref(_) => todo!(),
            Expression::LiteralExpr(literal) => literal.node_display(indent),
            Expression::Typed(_) => todo!(),
            Expression::Block(_) => todo!(),
            Expression::Import(import) => import.node_display(indent),
        }
    }
}

impl<'ast> NodeDisplay for AstNode<'ast, Block<'ast>> {
    fn node_display(&self, _indent: usize) -> Vec<String> {
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
