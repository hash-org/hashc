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
    if max_index == 0 || index == max_index - 1 {
        END_PIPE
    } else {
        MID_PIPE
    }
}

const fn which_pipe(index: usize, max_index: usize) -> &'static str {
    if max_index == 0 || index == max_index - 1 {
        "  "
    } else {
        "│ "
    }
}

fn pad_lines(lines: &[String], padding: usize) -> Vec<String> {
    lines
        .iter()
        .map(|line| pad_str(line, ' ', padding, Alignment::Left))
        .collect()
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

/// utility function to draw parental branch when display the children of the [AstNode]
fn draw_branches_for_lines(lines: &[String], connector: &str, branch: &str) -> Vec<String> {
    let mut next_lines = vec![];

    for (child_index, line) in lines.iter().enumerate() {
        // @@Speed: is this really the best way to deal with string concatination.
        if child_index == 0 {
            next_lines.push(format!("{}{}", connector, line));
        } else {
            // it's only one space here since the 'branch' char already takes one up
            next_lines.push(format!("{}{}", branch, line));
        }
    }

    next_lines
}

/// Function to draw branches for a Vector of lines, connecting each line with the appropriate
/// connector and vertical connector
fn draw_lines_for_children(line_collections: &Vec<Vec<String>>) -> Vec<String> {
    let mut lines = vec![];

    for (index, collection) in line_collections.iter().enumerate() {
        // figure out which connector to use here...
        let connector = which_connector(index, line_collections.len());
        let branch = which_pipe(index, line_collections.len());

        for (line_index, line) in collection.iter().enumerate() {
            let branch_char = if line_index == 0 { connector } else { branch };

            lines.push(format!("{}{}", branch_char, line));
        }
    }

    lines
}

/// Utility function to draw a single line for a given vector of lines, essentially padding
/// them with a vertical branch at the start of each line. This is a useful function for
/// drawing children nodes of [AstNode]s that have potential children nodes with a specific
/// context.
fn draw_vertical_branch(lines: &[String]) -> Vec<String> {
    lines
        .iter()
        .map(|line| format!("{} {}", VERT_PIPE, line))
        .collect()
}

pub trait NodeDisplay {
    fn node_display(&self, indent: usize) -> Vec<String>;
}

impl<T: NodeDisplay> NodeDisplay for AstNode<T> {
    fn node_display(&self, indent: usize) -> Vec<String> {
        self.body.node_display(indent)
    }
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

            write!(f, "{}{}\n{}", connector, node.join("\n"), ending)?
        }

        Ok(())
    }
}

impl NodeDisplay for Type {
    fn node_display(&self, _indent: usize) -> Vec<String> {
        match &self {
            Type::Named(_) => todo!(),
            Type::Ref(_) => todo!(),
            Type::TypeVar(_) => todo!(),
            Type::Existential => todo!(),
            Type::Infer => todo!(),
        }
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
                    let branch = which_pipe(index, elements.len());

                    // reset the indent here since we'll be doing indentation here...
                    let child_lines = element.node_display(1);
                    next_lines.extend(draw_branches_for_lines(&child_lines, connector, branch));
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

impl NodeDisplay for AccessName {
    fn node_display(&self, _indent: usize) -> Vec<String> {
        let names: Vec<&str> = self.names.iter().map(|n| n.body.string.as_ref()).collect();
        vec![names.join("::")]
    }
}

impl NodeDisplay for Statement {
    fn node_display(&self, indent: usize) -> Vec<String> {
        let mut lines = vec![];

        let child_lines: Vec<Vec<String>> = match &self {
            Statement::Expr(expr) => vec![expr.node_display(indent + 1)],
            Statement::Return(expr) => {
                lines.push("ret".to_string());

                match expr {
                    Some(ret) => vec![ret.node_display(indent + 1)],
                    None => vec![],
                }
            }
            Statement::Block(block) => vec![block.node_display(indent)],
            Statement::Break => {
                lines.push("break".to_string());
                vec![]
            }
            Statement::Continue => {
                lines.push("continue".to_string());
                vec![]
            }
            Statement::Let(_decl) => {
                lines.push("let".to_string());
                vec![]
            }
            Statement::Assign(decl) => {
                lines.push("assign".to_string());

                // add a mid connector for the lhs section, and then add vertical pipe
                // to the lhs so that it can be joined with the rhs of the assign expr
                let mut lhs_lines = vec!["lhs".to_string()];
                lhs_lines.extend(draw_branches_for_lines(
                    &decl.lhs.node_display(0),
                    END_PIPE,
                    "",
                ));

                // now deal with the rhs
                let mut rhs_lines = vec!["rhs".to_string()];
                rhs_lines.extend(draw_branches_for_lines(
                    &decl.rhs.node_display(0),
                    END_PIPE,
                    "",
                ));

                vec![lhs_lines, rhs_lines]
            }
            Statement::StructDef(_def) => {
                lines.push("struct_def".to_string());
                vec![]
            }
            Statement::EnumDef(_def) => {
                lines.push("enum_def".to_string());
                vec![]
            }
            Statement::TraitDef(_def) => {
                lines.push("trait_def".to_string());
                vec![]
            }
        };

        lines.extend(draw_lines_for_children(&child_lines));
        lines
        // // we need to pad each line by the number of spaces specified by 'ident'
        // let mut lines: Vec<String> = lines
        //     .into_iter()
        //     .map(|line| pad_str(line.as_str(), ' ', indent, Alignment::Left))
        //     .collect();

        // let next_lines: Vec<String> = next_lines
        //     .into_iter()
        //     .map(|line| pad_str(line.as_str(), ' ', next_indent, Alignment::Left))
        //     .collect();

        // lines.extend(next_lines);
        // lines
    }
}

impl NodeDisplay for Import {
    fn node_display(&self, _indent: usize) -> Vec<String> {
        vec![format!("import \"{}\"", self.path)]
    }
}

impl NodeDisplay for Expression {
    fn node_display(&self, indent: usize) -> Vec<String> {
        let mut lines = vec![];

        match &self {
            Expression::FunctionCall(func) => {
                let arguments = &func.args.body.entries;

                lines.push("function".to_string());

                // deal with the subject of the function call, this is for sure going to
                // be a VariableExpr, so the child branch will be labelled as 'ident'...
                let connector = if arguments.is_empty() {
                    END_PIPE
                } else {
                    MID_PIPE
                };

                lines.push(format!(" {}subject", connector));

                // deal with the 'subject' as a child and then append it to the next lines
                let subject_lines =
                    draw_branches_for_lines(&func.subject.node_display(2), END_PIPE, " ");
                // now deal with the function args if there are any
                if !arguments.is_empty() {
                    // we need to add a vertical line to the subject in order to connect the 'args'
                    // and subject component of the function AST node...
                    let subject_lines = draw_vertical_branch(&subject_lines);
                    lines.extend(pad_lines(&subject_lines, 1));

                    lines.push(format!(" {}args", END_PIPE));

                    let mut arg_lines = vec![];

                    // draw the children on onto the arguments
                    for (index, element) in arguments.iter().enumerate() {
                        let connector = which_connector(index, arguments.len());
                        let branch = which_pipe(index, arguments.len());

                        // reset the indent here since we'll be doing indentation here...
                        let child_lines = element.node_display(1);
                        arg_lines.extend(draw_branches_for_lines(&child_lines, connector, branch));
                    }

                    // add the lines to parent...
                    lines.extend(pad_lines(&arg_lines, 3))
                } else {
                    // no arguments, hence we should pad the lines by 3 characters instead of one,
                    // counting for a phantom verticla line...
                    lines.extend(pad_lines(&subject_lines, 3));
                }

                lines
            }
            Expression::Intrinsic(intrinsic) => {
                lines.push(format!("intrinsic \"{}\"", intrinsic.name.as_ref()));
                lines
            }
            Expression::Variable(var) => {
                // check if the length of type_args to this ident, if not
                // we don't produce any children nodes for it
                if !var.type_args.is_empty() {
                    todo!()
                } else {
                    let name = var.name.node_display(0).join("");
                    lines.push(format!("ident \"{}\"", name));
                    lines
                }
            }
            Expression::PropertyAccess(_) => todo!(),
            Expression::Ref(expr) | Expression::Deref(expr) => {
                // Match again to determine whether it is a deref or a ref!
                match &self {
                    Expression::Ref(_) => lines.push("ref".to_string()),
                    Expression::Deref(_) => lines.push("deref".to_string()),
                    _ => unreachable!(),
                };

                let next_lines = draw_branches_for_lines(&expr.node_display(indent), END_PIPE, "");
                lines.extend(pad_lines(&next_lines, 1));

                lines
            }
            Expression::LiteralExpr(literal) => literal.node_display(indent),
            Expression::Typed(_) => todo!(),
            Expression::Block(block) => block.node_display(indent),
            Expression::Import(import) => import.node_display(indent),
        }
    }
}

impl NodeDisplay for Block {
    fn node_display(&self, indent: usize) -> Vec<String> {
        match &self {
            Block::Match(match_block) => {
                let mut lines = vec!["match".to_string()];

                let MatchBlock { cases, subject } = &match_block;

                // apply the subject, this is esentially @@Copied from the FunctionCall
                let connector = if cases.is_empty() { END_PIPE } else { MID_PIPE };

                lines.push(format!(" {}subject", connector));

                // deal with the 'subject' as a child and then append it to the next lines
                let subject_lines =
                    draw_branches_for_lines(&subject.node_display(2), END_PIPE, " ");

                // now consider the cases
                if !cases.is_empty() {
                    // we need to add a vertical line to the subject in order to connect the 'args'
                    // and subject component of the function AST node...
                    let subject_lines = draw_vertical_branch(&subject_lines);
                    lines.extend(pad_lines(&subject_lines, 1));

                    lines.push(format!(" {}cases", END_PIPE));

                    let mut arg_lines = vec![];

                    // draw the children on onto the arguments
                    for (index, element) in cases.iter().enumerate() {
                        let connector = which_connector(index, cases.len());
                        let branch = which_pipe(index, cases.len());

                        // reset the indent here since we'll be doing indentation here...
                        let child_lines = element.node_display(1);
                        arg_lines.extend(draw_branches_for_lines(&child_lines, connector, branch));
                    }

                    // add the lines to parent...
                    lines.extend(pad_lines(&arg_lines, 3))
                } else {
                    // no arguments, hence we should pad the lines by 3 characters instead of one,
                    // counting for a phantom verticla line...
                    lines.extend(pad_lines(&subject_lines, 3));
                }

                lines
            }
            Block::Loop(loop_body) => {
                let mut lines = vec!["loop".to_string()];

                let block_lines =
                    draw_branches_for_lines(&loop_body.node_display(indent + 2), END_PIPE, "");

                lines.extend(block_lines);
                lines
            }
            Block::Body(body) => body.node_display(indent),
        }
    }
}

impl NodeDisplay for MatchCase {
    fn node_display(&self, indent: usize) -> Vec<String> {
        let mut lines = vec!["case".to_string()];

        // deal with the pattern for this case
        let pattern_lines = self.pattern.node_display(indent);

        // deal with the block for this case
        let mut branch_lines = vec!["branch".to_string()];

        let child_lines = draw_branches_for_lines(&self.expr.node_display(indent), END_PIPE, "");
        branch_lines.extend(pad_lines(&child_lines, 2));

        // append child_lines with padding and vertical lines being drawn
        lines.extend(draw_lines_for_children(&vec![pattern_lines, branch_lines]));
        lines
    }
}

impl NodeDisplay for Pattern {
    fn node_display(&self, _indent: usize) -> Vec<String> {
        vec!["pattern".to_string()]
    }
}

impl NodeDisplay for BodyBlock {
    fn node_display(&self, indent: usize) -> Vec<String> {
        let mut lines = vec!["block".to_string()];

        let mut statements: Vec<Vec<String>> = self
            .statements
            .iter()
            .map(|statement| statement.node_display(0))
            .collect();

        // check if body block has an expression at the end
        if let Some(expr) = &self.expr {
            statements.push(expr.node_display(0));
        }

        let next_lines = draw_lines_for_children(&statements);
        lines.extend(pad_lines(&next_lines, indent));
        lines
    }
}
