//! Hash Compiler Frontend library file
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt::Alignment;

use crate::ast::*;

// @@FIXME: REMOVE IDENT!

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

fn pad_lines(lines: Vec<String>, padding: usize) -> Vec<String> {
    if padding == 0 {
        lines
    } else {
        lines
            .iter()
            .map(|line| pad_str(line, ' ', padding, Alignment::Left))
            .collect()
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

fn child_branch(lines: &[String]) -> Vec<String> {
    draw_branches_for_lines(lines, END_PIPE, "  ")
}

/// Function to draw branches for a Vector of lines, connecting each line with the appropriate
/// connector and vertical connector
fn draw_lines_for_children(line_collections: &[Vec<String>]) -> Vec<String> {
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
        // special case for reference type, the name of the parent node has the prefix 'ref_'
        let lines = if let Type::Ref(_) = &self {
            vec!["ref_type".to_string()]
        } else {
            vec!["type".to_string()]
        };

        let child_lines = match &self {
            Type::Named(named_ty) => {
                let mut components = vec![];

                // add a mid connector for the lhs section, and then add vertical pipe
                // to the lhs so that it can be joined with the rhs of the assign expr
                let NamedType { name, type_args } = &named_ty;

                // add the name_lines into components
                // @@Fixme: maybe have a different fmt::Display for Access
                components.push(vec![format!("name \"{}\"", name.node_display(0)[0])]);

                if !type_args.is_empty() {
                    let mut type_lines = vec!["args".to_string()];

                    let arg_lines: Vec<Vec<String>> =
                        type_args.iter().map(|arg| arg.node_display(0)).collect();
                    type_lines.extend(draw_lines_for_children(&arg_lines));

                    components.push(type_lines)
                }

                // components
                draw_lines_for_children(&components)
            }
            Type::Ref(ref_ty) => draw_branches_for_lines(&ref_ty.node_display(2), END_PIPE, "  "), // @@Hack: two spaces here to add padding to the child lines
            Type::TypeVar(var) => draw_branches_for_lines(
                &[format!("var \"{}\"", var.name.body.string)],
                END_PIPE,
                "",
            ),
            Type::Existential => draw_branches_for_lines(&["infer".to_string()], END_PIPE, ""),
            Type::Infer => draw_branches_for_lines(&["infer".to_string()], END_PIPE, ""),
        };

        lines.into_iter().chain(child_lines).collect()
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
            Literal::Map(map) => {
                lines.push("map".to_string());

                // loop over the entries in the map and build a list of
                // 'entry' branches which contain a 'key' and 'value' sub branch
                let entries: Vec<Vec<String>> = map
                    .elements
                    .iter()
                    .map(|(key, value)| {
                        let mut entry = vec!["entry".to_string()];

                        // deal with they key, and then value
                        let key_lines = vec!["key".to_string()]
                            .into_iter()
                            .chain(child_branch(&key.node_display(0)))
                            .collect();
                        let value_lines = vec!["value".to_string()]
                            .into_iter()
                            .chain(child_branch(&value.node_display(0)))
                            .collect();

                        entry.extend(draw_lines_for_children(&[key_lines, value_lines]));
                        entry
                    })
                    .collect();

                next_lines.extend(draw_lines_for_children(&entries));
            }
            Literal::Struct(_struct_lit) => {
                lines.push("struct".to_string());
            }
            Literal::Function(fn_defn) => {
                lines.push("function".to_string());

                let mut components = vec![];

                // deal with the args
                if !fn_defn.args.is_empty() {
                    let arg_lines: Vec<Vec<String>> = fn_defn
                        .args
                        .iter()
                        .map(|arg| {
                            let lines = vec!["arg".to_string()];

                            // deal with the name and type as seperate branches
                            let mut arg_components =
                                vec![vec![format!("name \"{}\"", arg.name.body.string)]];

                            if let Some(ty) = &arg.ty {
                                arg_components.push(ty.node_display(0))
                            }

                            let component_lines = draw_lines_for_children(&arg_components);
                            lines.into_iter().chain(component_lines).collect()
                        })
                        .collect();

                    let args = draw_lines_for_children(&arg_lines);
                    components.push(vec!["args".to_string()].into_iter().chain(args).collect());
                }

                // if there is a return type on the function, then add it to the tree
                if let Some(return_ty) = &fn_defn.return_ty {
                    let return_ty_lines = vec!["return_type".to_string()]
                        .into_iter()
                        .chain(child_branch(&return_ty.node_display(1)))
                        .collect();

                    components.push(return_ty_lines);
                }

                // deal with the function body
                let body = vec!["body".to_string()]
                    .into_iter()
                    // we don't need to deal with branches here since the block will already add a parental
                    // branch
                    .chain(fn_defn.fn_body.node_display(0))
                    .collect();

                components.push(body);

                next_lines.extend(pad_lines(draw_lines_for_children(&components), 2));
            }
        };

        lines.extend(pad_lines(next_lines, indent));
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
        let node_name = match &self {
            Statement::Expr(_) => None,
            Statement::Return(_) => Some("ret".to_string()),
            Statement::Block(_) => Some("block".to_string()),
            Statement::Break => Some("break".to_string()),
            Statement::Continue => Some("continue".to_string()),
            Statement::Let(_) => Some("let".to_string()),
            Statement::Assign(_) => Some("assign".to_string()),
            Statement::StructDef(_) => Some("struct_defn".to_string()),
            Statement::EnumDef(_) => Some("enum_defn".to_string()),
            Statement::TraitDef(_) => Some("trait_defn".to_string()),
        };

        let child_lines: Vec<String> = match &self {
            Statement::Expr(expr) => expr.node_display(indent + 1),
            Statement::Return(expr) => match expr {
                Some(ret) => draw_branches_for_lines(&ret.node_display(indent + 1), END_PIPE, ""),
                None => vec![],
            },
            Statement::Block(block) => block.node_display(indent),
            Statement::Break => vec![],
            Statement::Continue => vec![],
            Statement::Let(decl) => {
                let mut components = vec![
                    decl.pattern.node_display(0)
                ];

                // optionally add the type of the argument, as specified by the user
                if let Some(ty) = &decl.ty {
                    components.push(ty.node_display(0));
                }

                // optionally deal with the bound of the let statement
                if let Some(_bound) = &decl.bound {
                    todo!()
                }

                // optionally deal with the value of the let statement
                if let Some(value) = &decl.value {
                    let mut value_lines = vec!["value".to_string()];
                    value_lines.extend(draw_branches_for_lines(
                        &value.node_display(0),
                        END_PIPE,
                        "",
                    ));

                    components.push(value_lines);
                }

                draw_lines_for_children(&components)
            }
            Statement::Assign(decl) => {
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

                draw_lines_for_children(&[lhs_lines, rhs_lines])
            }
            Statement::StructDef(_def) => {
                vec![]
            }
            Statement::EnumDef(_def) => {
                vec![]
            }
            Statement::TraitDef(_def) => {
                vec![]
            }
        };

        node_name.into_iter().chain(child_lines).collect()
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
                    lines.extend(pad_lines(subject_lines, 1));

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
                    lines.extend(pad_lines(arg_lines, 3))
                } else {
                    // no arguments, hence we should pad the lines by 3 characters instead of one,
                    // counting for a phantom verticla line...
                    lines.extend(pad_lines(subject_lines, 3));
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
                let name = var.name.node_display(0).join("");
                let ident_lines = vec![format!("ident \"{}\"", name)];

                if !var.type_args.is_empty() {
                    lines.push("variable".to_string());

                    let mut components = vec![ident_lines];

                    // now deal with type_argumnets here
                    let args: Vec<Vec<String>> = var
                        .type_args
                        .iter()
                        .map(|arg| arg.node_display(0))
                        .collect();

                    let type_args_lines = vec!["type_args".to_string()]
                        .into_iter()
                        .chain(draw_lines_for_children(&args))
                        .collect();

                    components.push(type_args_lines);
                    lines.extend(draw_lines_for_children(&components));
                } else {
                    // we don't construct a complex tree structure here since we want to avoid
                    // verbosity as much, since most of the time variales aren't going to have
                    // type arguments.
                    lines.extend(ident_lines);
                }

                lines
            }
            Expression::PropertyAccess(expr) => {
                lines.push("property_access".to_string());

                // deal with the subject
                let subject_lines = vec!["subject".to_string()]
                    .into_iter()
                    .chain(draw_branches_for_lines(
                        &expr.subject.node_display(2),
                        END_PIPE,
                        "  ",
                    ))
                    .collect();

                // now deal with the field
                let field_lines = vec![format!("field \"{}\"", expr.property.body.string)];

                lines.extend(draw_lines_for_children(&[subject_lines, field_lines]));
                lines
            }
            Expression::Ref(expr) | Expression::Deref(expr) => {
                // Match again to determine whether it is a deref or a ref!
                match &self {
                    Expression::Ref(_) => lines.push("ref".to_string()),
                    Expression::Deref(_) => lines.push("deref".to_string()),
                    _ => unreachable!(),
                };

                let next_lines = draw_branches_for_lines(&expr.node_display(indent), END_PIPE, "");
                lines.extend(pad_lines(next_lines, 1));

                lines
            }
            Expression::LiteralExpr(literal) => literal.node_display(indent),
            Expression::Typed(expr) => {
                lines.push("typed_expr".to_string());

                let TypedExpr { expr, ty } = expr;

                // the type line is handeled by the implementation
                let type_lines = ty.node_display(0);

                // now deal with the expression
                let mut expr_lines = vec!["subject".to_string()];
                expr_lines.extend(draw_branches_for_lines(&expr.node_display(0), END_PIPE, ""));

                let next_lines = draw_lines_for_children(&[expr_lines, type_lines]);

                lines.extend(pad_lines(next_lines, 1));
                lines
            }
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
                    lines.extend(pad_lines(subject_lines, 1));

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
                    lines.extend(pad_lines(arg_lines, 3))
                } else {
                    // no arguments, hence we should pad the lines by 3 characters instead of one,
                    // counting for a phantom verticla line...
                    lines.extend(pad_lines(subject_lines, 3));
                }

                draw_branches_for_lines(&lines, END_PIPE, " ")
            }
            Block::Loop(loop_body) => {
                let mut lines = vec!["loop".to_string()];
                lines.extend(pad_lines(loop_body.node_display(indent), 2));
                draw_branches_for_lines(&lines, END_PIPE, "")
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
        let branch_lines = vec!["branch".to_string()]
            .into_iter()
            .chain(self.expr.node_display(0))
            .collect();

        // append child_lines with padding and vertical lines being drawn
        lines.extend(draw_lines_for_children(&[pattern_lines, branch_lines]));
        lines
    }
}

impl NodeDisplay for Pattern {
    fn node_display(&self, _indent: usize) -> Vec<String> {
        let lines = vec!["pattern".to_string()];

        match &self {
            Pattern::Enum(_) => {}
            Pattern::Struct(_) => {}
            Pattern::Namespace(_) => {}
            Pattern::Tuple(_) => {}
            Pattern::Literal(_) => {}
            Pattern::Or(_) => {}
            Pattern::If(_) => {}
            Pattern::Binding(_) => {}
            Pattern::Ignore => {}
        }

        lines
    }
}

impl NodeDisplay for BodyBlock {
    fn node_display(&self, indent: usize) -> Vec<String> {
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
        pad_lines(next_lines, indent)
    }
}
