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

/// Compile time function to determine which PIPE connector should
/// be used when converting an array of [AstNode]s.
const fn which_connector(index: usize, max_index: usize) -> &'static str {
    if index == max_index - 1 {
        END_PIPE
    } else {
        MID_PIPE
    }
}

pub trait NodeDisplay {
    fn node_display(&self, indent: usize) -> Vec<String>;
}

impl<T: NodeDisplay> NodeDisplay for AstNode<T> {
    fn node_display(&self, indent: usize) -> Vec<String> {
        self.body().node_display(indent)
    }
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

impl<T> std::fmt::Display for AstNode<T>
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
impl std::fmt::Display for Module {
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
            write!(f, "{}{}\n{}", connector, node.join("\n"), ending)?
        }

        Ok(())
    }
}

impl NodeDisplay for Literal {
    fn node_display(&self, indent: usize) -> Vec<String> {
        let mut lines = vec![];
        let mut next_lines = vec![];

        match &self {
            Literal::Str(s) => lines.push(format!("string \"{}\"", s)),
            Literal::Char(c) => lines.push(format!("char \'{}\'", c)),
            Literal::Int(i) => lines.push(format!("number {}", i)),
            Literal::Float(f) => lines.push(format!("float {}", f)),

            // all these variants have the possibility of containing multiple elements, so
            // we have to evaluate the children first and then construct the branches...
            Literal::Set(SetLiteral { elements })
            | Literal::List(ListLiteral { elements })
            | Literal::Tuple(TupleLiteral { elements }) => {
                // @@Dumbness: rust doesn't allow to bind patterns if there are pattern binds
                // after '@', this can be enabled on Rust nightly, but we aren't that crazy!
                // so we're matching a second time just to get the right literal name
                match &self {
                    Literal::Set(_) => lines.push("set".to_string()),
                    Literal::List(_) => lines.push("list".to_string()),
                    Literal::Tuple(_) => lines.push("tuple".to_string()),
                    _ => unreachable!(),
                };

                // convert all the children and add them to the new lines
                for (index, element) in elements.iter().enumerate() {
                    let connector = which_connector(index, elements.len());

                    // @@Cleanup: make this a function!
                    let branch = if index == elements.len() - 1 {
                        " "
                    } else {
                        "│"
                    };

                    // reset the indent here since we'll be doing indentation here...
                    let child_lines = element.node_display(0);

                    for (child_index, line) in child_lines.iter().enumerate() {
                        // @@Speed: is this really the best way to deal with string concatination.
                        if child_index == 0 {
                            next_lines.push(format!("  {}{}", connector, line));
                        } else {
                            // it's only one space here since the 'branch' char already takes one up
                            next_lines.push(format!("  {}{}", branch, line));
                        }
                    }
                }
            }
            Literal::Map(_map_lit) => {}
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

impl NodeDisplay for Statement {
    fn node_display(&self, indent: usize) -> Vec<String> {
        let mut lines = vec![];
        let mut next_lines = vec![];
        let next_indent = indent + 2;

        match &self {
            Statement::Expr(expr) => lines.extend(expr.node_display(next_indent)),
            Statement::Return(expr) => {
                lines.push("ret".to_string());

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
            Statement::Break => lines.push("break".to_string()),
            Statement::Continue => lines.push("continue".to_string()),
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

impl NodeDisplay for Import {
    fn node_display(&self, _indent: usize) -> Vec<String> {
        vec![
            "import".to_string(),
            format!("{} \"{}\"", END_PIPE, self.path),
        ]
    }
}

impl NodeDisplay for Expression {
    fn node_display(&self, indent: usize) -> Vec<String> {
        match self.kind() {
            ExpressionKind::FunctionCall(_) => todo!(),
            ExpressionKind::Intrinsic(_) => todo!(),
            ExpressionKind::LogicalOp(_) => todo!(),
            ExpressionKind::Variable(_) => todo!(),
            ExpressionKind::PropertyAccess(_) => todo!(),
            ExpressionKind::Index(_) => todo!(),
            ExpressionKind::Ref(_) => todo!(),
            ExpressionKind::Deref(_) => todo!(),
            ExpressionKind::LiteralExpr(literal) => literal.node_display(indent),
            ExpressionKind::Typed(_) => todo!(),
            ExpressionKind::Block(_) => todo!(),
            ExpressionKind::Import(import) => import.node_display(indent),
        }
    }
}

impl NodeDisplay for Block {
    fn node_display(&self, _indent: usize) -> Vec<String> {
        match &self {
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
