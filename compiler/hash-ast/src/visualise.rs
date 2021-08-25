//! Hash Compiler Frontend library file
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::{fmt::Alignment, iter};

use crate::ast::*;
use crate::ident::IDENTIFIER_MAP;
use crate::literal::STRING_LITERAL_MAP;

const VERT_PIPE: &str = "│ ";
const PADDING: &str = "  ";
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
        PADDING
    } else {
        VERT_PIPE
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
    draw_branches_for_lines(lines, END_PIPE, PADDING)
}

/// Function to draw branches for a Vector of lines, connecting each line with the appropriate
/// connector and vertical connector
fn draw_branches_for_children(line_collections: &[Vec<String>]) -> Vec<String> {
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

pub trait NodeDisplay {
    fn node_display(&self) -> Vec<String>;
}

impl<T: NodeDisplay> NodeDisplay for AstNode<'_, T> {
    fn node_display(&self) -> Vec<String> {
        self.body().node_display()
    }
}

impl<T> std::fmt::Display for AstNode<'_, T>
where
    Self: NodeDisplay,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.node_display().join("\n"))
    }
}

///
/// We need a seperate implementation for [Module] since it won't be wrapped within
/// an [AstNode] unlike all the other variants
///
impl std::fmt::Display for Module<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nodes: Vec<Vec<String>> = self.contents.iter().map(|s| s.node_display()).collect();

        writeln!(f, "module")?;
        write!(f, "{}", draw_branches_for_children(&nodes).join("\n"))
    }
}

/// Implementation for Type_Args specifically!
impl NodeDisplay for AstNodes<'_, Type<'_>> {
    fn node_display(&self) -> Vec<String> {
        let args: Vec<Vec<String>> = self.iter().map(|arg| arg.node_display()).collect();

        iter::once("type_args".to_string())
            .into_iter()
            .chain(draw_branches_for_children(&args))
            .collect()
    }
}

impl NodeDisplay for Type<'_> {
    fn node_display(&self) -> Vec<String> {
        let lines = match &self {
            Type::Ref(_) => vec!["ref_type".to_string()],
            Type::RawRef(_) => vec!["raw_ref_type".to_string()],
            _ => vec!["type".to_string()],
        };

        let child_lines = match &self {
            Type::Named(named_ty) => {
                let mut components = vec![];

                // add a mid connector for the lhs section, and then add vertical pipe
                // to the lhs so that it can be joined with the rhs of the assign expr
                let NamedType { name, type_args } = &named_ty;

                // add the name_lines into components
                components.push(vec![format!("name {}", name.node_display().join(""))]);

                if !type_args.is_empty() {
                    components.push(type_args.node_display());
                }

                // components
                draw_branches_for_children(&components)
            }
            Type::Ref(ref_ty) => child_branch(&ref_ty.node_display()),
            Type::RawRef(ref_ty) => child_branch(&ref_ty.node_display()),
            Type::TypeVar(var) => child_branch(&[format!("var \"{}\"", var.name)]),
            Type::Existential => child_branch(&["existential".to_string()]),
            Type::Infer => child_branch(&["infer".to_string()]),
        };

        lines.into_iter().chain(child_lines).collect()
    }
}

impl NodeDisplay for Literal<'_> {
    fn node_display(&self) -> Vec<String> {
        let mut lines = vec![];
        let mut next_lines = vec![];

        match &self {
            Literal::Str(s) => lines.push(format!("string \"{}\"", STRING_LITERAL_MAP.lookup(*s))),
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
                    let child_lines = element.node_display();
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
                            .chain(child_branch(&key.node_display()))
                            .collect();
                        let value_lines = vec!["value".to_string()]
                            .into_iter()
                            .chain(child_branch(&value.node_display()))
                            .collect();

                        entry.extend(draw_branches_for_children(&[key_lines, value_lines]));
                        entry
                    })
                    .collect();

                next_lines.extend(draw_branches_for_children(&entries));
            }
            Literal::Struct(struct_lit) => {
                lines.push("struct".to_string());

                let mut components = vec![struct_lit.name.node_display()];

                // now deal with type_arguments here
                if !struct_lit.type_args.is_empty() {
                    components.push(struct_lit.type_args.node_display());
                }

                if !struct_lit.entries.is_empty() {
                    let entries: Vec<Vec<String>> = struct_lit
                        .entries
                        .iter()
                        .map(|arg| arg.node_display())
                        .collect();

                    // @@Naming: change this to 'fields' rather than 'entries'?
                    let entry_lines = iter::once("entries".to_string())
                        .into_iter()
                        .chain(draw_branches_for_children(&entries))
                        .collect();

                    components.push(entry_lines);
                }

                next_lines.extend(draw_branches_for_children(&components));
            }
            Literal::Function(fn_defn) => {
                lines.push("function_defn".to_string());

                let mut components = vec![];

                // deal with the args
                if !fn_defn.args.is_empty() {
                    let arg_lines = fn_defn
                        .args
                        .iter()
                        .map(|arg| arg.node_display())
                        .collect::<Vec<Vec<String>>>();

                    let args = draw_branches_for_children(&arg_lines);
                    components.push(vec!["args".to_string()].into_iter().chain(args).collect());
                }

                // if there is a return type on the function, then add it to the tree
                if let Some(return_ty) = &fn_defn.return_ty {
                    let return_ty_lines = vec!["return_type".to_string()]
                        .into_iter()
                        .chain(child_branch(&return_ty.node_display()))
                        .collect();

                    components.push(return_ty_lines);
                }

                // deal with the function body
                let body = vec!["body".to_string()]
                    .into_iter()
                    // we don't need to deal with branches here since the block will already add a parental
                    // branch
                    .chain(child_branch(&fn_defn.fn_body.node_display()))
                    .collect();

                components.push(body);

                next_lines.extend(draw_branches_for_children(&components));
            }
        };

        lines.extend(next_lines);
        lines
    }
}

impl NodeDisplay for FunctionDefArg<'_> {
    fn node_display(&self) -> Vec<String> {
        // deal with the name and type as separate branches
        let mut arg_components = vec![vec![format!("name {}", self.name.node_display().join(""))]];

        if let Some(ty) = &self.ty {
            arg_components.push(ty.node_display())
        }

        let component_lines = draw_branches_for_children(&arg_components);
        iter::once("arg".to_string())
            .into_iter()
            .chain(component_lines)
            .collect()
    }
}

impl NodeDisplay for StructLiteralEntry<'_> {
    fn node_display(&self) -> Vec<String> {
        let name = vec![format!("field {}", self.name)];

        let value = iter::once("value".to_string())
            .chain(child_branch(&self.value.node_display()))
            .collect();

        iter::once("entry".to_string())
            .chain(draw_branches_for_children(&[name, value]))
            .collect()
    }
}

impl NodeDisplay for AccessName<'_> {
    fn node_display(&self) -> Vec<String> {
        vec![format!(
            "\"{}\"",
            (self
                .path
                .iter()
                .map(|x| IDENTIFIER_MAP.ident_name(*x).to_owned())
                .collect::<Vec<String>>()
                .join("::"))
        )]
    }
}

impl NodeDisplay for Name {
    fn node_display(&self) -> Vec<String> {
        vec![format!("\"{}\"", IDENTIFIER_MAP.ident_name(self.ident))]
    }
}

impl NodeDisplay for Statement<'_> {
    fn node_display(&self) -> Vec<String> {
        let (node_name, child_lines) = match &self {
            Statement::Expr(expr) => (None, expr.node_display()),
            Statement::Return(expr) => {
                let lines = match expr {
                    Some(ret) => child_branch(&ret.node_display()),
                    None => vec![],
                };

                (Some("ret".to_string()), lines)
            }
            Statement::Block(block) => (Some("block".to_string()), block.node_display()),
            Statement::Break => (Some("break".to_string()), vec![]),
            Statement::Continue => (Some("continue".to_string()), vec![]),
            Statement::Let(decl) => {
                let mut components = vec![decl.pattern.node_display()];

                // optionally add the type of the argument, as specified by the user
                if let Some(ty) = &decl.ty {
                    components.push(ty.node_display());
                }

                // optionally deal with the bound of the let statement
                if let Some(bound) = &decl.bound {
                    components.push(bound.node_display())
                }

                // optionally deal with the value of the let statement
                if let Some(value) = &decl.value {
                    components.push(
                        iter::once("value".to_string())
                            .chain(child_branch(&value.node_display()))
                            .collect(),
                    );
                }

                (
                    Some("let".to_string()),
                    draw_branches_for_children(&components),
                )
            }
            Statement::Assign(decl) => {
                // add a mid connector for the lhs section, and then add vertical pipe
                // to the lhs so that it can be joined with the rhs of the assign expr
                let lhs_lines = iter::once("lhs".to_string())
                    .chain(child_branch(&decl.lhs.node_display()))
                    .collect();

                // now deal with the rhs
                let rhs_lines = iter::once("rhs".to_string())
                    .chain(child_branch(&decl.rhs.node_display()))
                    .collect();

                (
                    Some("assign".to_string()),
                    draw_branches_for_children(&[lhs_lines, rhs_lines]),
                )
            }
            Statement::StructDef(defn) => {
                let mut components =
                    vec![vec![format!("name {}", defn.name.node_display().join(""))]];

                if let Some(bound) = &defn.bound {
                    components.push(bound.node_display())
                }

                // append the entries if there is more than one
                if !defn.entries.is_empty() {
                    let lines = defn
                        .entries
                        .iter()
                        .map(|entry| entry.node_display())
                        .collect::<Vec<Vec<String>>>();

                    // the enum definition entries
                    let entries = iter::once("entries".to_string())
                        .into_iter()
                        .chain(draw_branches_for_children(&lines))
                        .collect();

                    components.push(entries);
                }

                (
                    Some("struct_defn".to_string()),
                    draw_branches_for_children(&components),
                )
            }
            Statement::EnumDef(defn) => {
                let mut components =
                    vec![vec![format!("name {}", defn.name.node_display().join(""))]];

                if let Some(bound) = &defn.bound {
                    components.push(bound.node_display())
                }

                // append the entries if there is more than one
                if !defn.entries.is_empty() {
                    let lines = defn
                        .entries
                        .iter()
                        .map(|entry| entry.node_display())
                        .collect::<Vec<Vec<String>>>();

                    // the enum definition entries
                    let entries = iter::once("entries".to_string())
                        .into_iter()
                        .chain(draw_branches_for_children(&lines))
                        .collect();

                    components.push(entries);
                }

                (
                    Some("enum_defn".to_string()),
                    draw_branches_for_children(&components),
                )
            }
            Statement::TraitDef(defn) => {
                let components = vec![
                    vec![format!("name {}", defn.name.node_display().join(""))],
                    defn.bound.node_display(),
                    defn.trait_type.node_display(),
                ];

                (
                    Some("trait_defn".to_string()),
                    draw_branches_for_children(&components),
                )
            }
        };

        node_name.into_iter().chain(child_lines).collect()
    }
}

impl NodeDisplay for EnumDefEntry<'_> {
    fn node_display(&self) -> Vec<String> {
        let components = vec![
            vec![format!("name {}", self.name.node_display().join(""))],
            self.args.node_display(),
        ];

        iter::once("field".to_string())
            .chain(draw_branches_for_children(&components))
            .collect()
    }
}

impl NodeDisplay for StructDefEntry<'_> {
    fn node_display(&self) -> Vec<String> {
        let mut components = vec![vec![format!("name {}", self.name.node_display().join(""))]];

        if let Some(ty) = &self.ty {
            components.push(ty.node_display())
        }

        if let Some(default) = &self.default {
            components.push(
                iter::once("default".to_string())
                    .chain(child_branch(&default.node_display()))
                    .collect(),
            )
        }

        iter::once("field".to_string())
            .chain(draw_branches_for_children(&components))
            .collect()
    }
}

impl NodeDisplay for Bound<'_> {
    fn node_display(&self) -> Vec<String> {
        let mut components = vec![self.type_args.node_display()];

        if !self.trait_bounds.is_empty() {
            let trait_bounds = draw_branches_for_children(
                &self
                    .trait_bounds
                    .iter()
                    .map(|bound| bound.node_display())
                    .collect::<Vec<Vec<String>>>(),
            );

            components.push(
                iter::once("trait_bounds".to_string())
                    .chain(trait_bounds)
                    .collect(),
            );
        }

        iter::once("bound".to_string())
            .chain(draw_branches_for_children(&components))
            .collect()
    }
}

impl NodeDisplay for TraitBound<'_> {
    fn node_display(&self) -> Vec<String> {
        let components = vec![
            vec![format!("name {}", self.name.node_display().join(""))],
            self.type_args.node_display(),
        ];

        iter::once("trait_bound".to_string())
            .chain(draw_branches_for_children(&components))
            .collect()
    }
}

impl NodeDisplay for Import {
    fn node_display(&self) -> Vec<String> {
        vec![format!(
            "import \"{}\"",
            STRING_LITERAL_MAP.lookup(self.path)
        )]
    }
}

impl NodeDisplay for Expression<'_> {
    fn node_display(&self) -> Vec<String> {
        match self.kind() {
            ExpressionKind::FunctionCall(func) => {
                let mut components = vec![iter::once("subject".to_string())
                    .chain(child_branch(&func.subject.node_display()))
                    .collect()];

                let arguments = &func.args.entries;

                // now deal with the function args if there are any
                if !arguments.is_empty() {
                    let args: Vec<Vec<String>> = arguments
                        .iter()
                        .map(|arg| {
                            // Add 'arg' prefix to each part of the function call argument
                            iter::once("arg".to_string())
                                .chain(child_branch(&arg.node_display()))
                                .collect()
                        })
                        .collect();

                    let arg_lines = iter::once("args".to_string())
                        .chain(draw_branches_for_children(&args))
                        .collect();

                    components.push(arg_lines);
                }
                iter::once("function_call".to_string())
                    .chain(draw_branches_for_children(&components))
                    .collect()
            }
            ExpressionKind::Intrinsic(intrinsic) => {
                vec![format!(
                    "intrinsic \"{}\"",
                    IDENTIFIER_MAP.ident_name(intrinsic.name)
                )]
            }
            ExpressionKind::Variable(var) => {
                // check if the length of type_args to this ident, if not
                // we don't produce any children nodes for it
                let ident = format!("ident {}", var.name.node_display().join(""));

                if !var.type_args.is_empty() {
                    let components = vec![vec![ident], var.type_args.node_display()];

                    iter::once("variable".to_string())
                        .chain(draw_branches_for_children(&components))
                        .collect()
                } else {
                    // we don't construct a complex tree structure here since we want to avoid
                    // verbosity as much, since most of the time variables aren't going to have
                    // type arguments.
                    vec![ident]
                }
            }
            ExpressionKind::PropertyAccess(expr) => {
                // deal with the subject
                let subject_lines = vec!["subject".to_string()]
                    .into_iter()
                    .chain(child_branch(&expr.subject.node_display()))
                    .collect();

                // now deal with the field
                let field_lines = vec![format!(
                    "field \"{}\"",
                    IDENTIFIER_MAP.ident_name(expr.property.body().ident)
                )];

                iter::once("property_access".to_string())
                    .chain(draw_branches_for_children(&[subject_lines, field_lines]))
                    .collect()
            }
            ExpressionKind::Ref(expr) | ExpressionKind::Deref(expr) => {
                // Match again to determine whether it is a deref or a ref!
                let prefix = match self.kind() {
                    ExpressionKind::Ref(_) => "ref",
                    ExpressionKind::Deref(_) => "deref",
                    _ => unreachable!(),
                }
                .to_string();

                iter::once(prefix)
                    .chain(child_branch(&expr.node_display()))
                    .collect()
            }
            ExpressionKind::LiteralExpr(literal) => literal.node_display(),
            ExpressionKind::Typed(expr) => {
                let TypedExpr { expr, ty } = expr;

                // the type line is handled by the implementation
                let type_lines = ty.node_display();

                // now deal with the expression
                let mut expr_lines = vec!["subject".to_string()];
                expr_lines.extend(child_branch(&expr.node_display()));

                let next_lines = draw_branches_for_children(&[expr_lines, type_lines]);
                iter::once("typed_expr".to_string())
                    .chain(pad_lines(next_lines, 1))
                    .collect()
            }
            ExpressionKind::Block(block) => iter::once("block".to_string())
                .chain(block.node_display())
                .collect::<Vec<_>>(),
            ExpressionKind::Import(import) => import.node_display(),
        }
    }
}

impl NodeDisplay for Block<'_> {
    fn node_display(&self) -> Vec<String> {
        match &self {
            Block::Match(match_block) => {
                let mut components: Vec<Vec<String>> = vec![iter::once("subject".to_string())
                    .chain(child_branch(&match_block.subject.node_display()))
                    .collect()];

                // now consider the cases
                if !match_block.cases.is_empty() {
                    let cases = match_block
                        .cases
                        .iter()
                        .map(|case| case.node_display())
                        .collect::<Vec<Vec<String>>>();

                    let case_lines = iter::once("cases".to_string())
                        .chain(draw_branches_for_children(&cases))
                        .collect();

                    components.push(case_lines);
                }

                iter::once("match".to_string())
                    .chain(draw_branches_for_children(&components))
                    .collect::<Vec<String>>()
            }
            Block::Loop(loop_body) => {
                let mut lines = vec!["loop".to_string()];

                // @@Cleanup: This is a block but we don't display this as a block with the branch because
                // it doesn't go through the Statement implementation which deals with the block
                lines.extend(pad_lines(loop_body.node_display(), 2));
                draw_branches_for_lines(&lines, END_PIPE, "")
            }
            Block::Body(body) => body.node_display(),
        }
    }
}

impl NodeDisplay for MatchCase<'_> {
    fn node_display(&self) -> Vec<String> {
        let mut lines = vec!["case".to_string()];

        // deal with the pattern for this case
        let pattern_lines = self.pattern.node_display();

        // deal with the block for this case
        let branch_lines = vec!["branch".to_string()]
            .into_iter()
            .chain(self.expr.node_display())
            .collect();

        // append child_lines with padding and vertical lines being drawn
        lines.extend(draw_branches_for_children(&[pattern_lines, branch_lines]));
        lines
    }
}

impl NodeDisplay for LiteralPattern {
    fn node_display(&self) -> Vec<String> {
        vec![match &self {
            LiteralPattern::Str(s) => format!("string \"{}\"", STRING_LITERAL_MAP.lookup(*s)),
            LiteralPattern::Char(c) => format!("char \'{}\'", c),
            LiteralPattern::Int(i) => format!("number {}", i),
            LiteralPattern::Float(f) => format!("float {}", f),
        }]
    }
}

impl NodeDisplay for DestructuringPattern<'_> {
    fn node_display(&self) -> Vec<String> {
        let name = vec![format!("ident {}", self.name.node_display().join(""))];
        let pat = self.pattern.node_display();

        draw_branches_for_children(&[name, pat])
    }
}

impl NodeDisplay for Pattern<'_> {
    fn node_display(&self) -> Vec<String> {
        let mut lines = vec!["pattern".to_string()];

        let child_components = match &self {
            Pattern::Enum(enum_pat) => {
                let mut components = vec![vec![format!(
                    "ident {}",
                    enum_pat.name.node_display().join("")
                )]];

                let patterns: Vec<Vec<String>> =
                    enum_pat.args.iter().map(|pat| pat.node_display()).collect();

                components.push(
                    iter::once("patterns".to_string())
                        .chain(draw_branches_for_children(&patterns))
                        .collect(),
                );

                vec![iter::once("enum".to_string())
                    .chain(draw_branches_for_children(&components))
                    .collect()]
            }
            Pattern::Struct(struct_pat) => {
                let mut components = vec![vec![format!(
                    "ident {}",
                    struct_pat.name.node_display().join("")
                )]];

                let patterns: Vec<Vec<String>> = struct_pat
                    .entries
                    .iter()
                    .map(|pat| pat.node_display())
                    .collect();

                components.push(
                    iter::once("patterns".to_string())
                        .chain(draw_branches_for_children(&patterns))
                        .collect(),
                );

                vec![iter::once("struct".to_string())
                    .chain(draw_branches_for_children(&components))
                    .collect()]
            }
            Pattern::Namespace(namespace) => {
                let patterns: Vec<Vec<String>> = namespace
                    .patterns
                    .iter()
                    .map(|pat| pat.node_display())
                    .collect();

                vec![iter::once("namespace".to_string())
                    .chain(draw_branches_for_children(&patterns))
                    .collect()]
            }
            Pattern::Tuple(tup) => {
                let patterns: Vec<Vec<String>> =
                    tup.elements.iter().map(|pat| pat.node_display()).collect();

                vec![iter::once("tuple".to_string())
                    .chain(draw_branches_for_children(&patterns))
                    .collect()]
            }
            Pattern::Literal(lit) => vec![iter::once("literal".to_string())
                .chain(child_branch(&lit.node_display()))
                .collect()],
            Pattern::Or(pat) => {
                let variants = pat
                    .variants
                    .iter()
                    .map(|pat| pat.node_display())
                    .collect::<Vec<Vec<String>>>();

                vec![iter::once("or".to_string())
                    .chain(draw_branches_for_children(&variants))
                    .collect()]
            }
            Pattern::If(pat) => {
                let pattern = pat.pattern.node_display();

                // add a 'condition' prefix branch to the expression
                let condition = iter::once("condition".to_string())
                    .chain(child_branch(&pat.condition.node_display()))
                    .collect();

                vec![iter::once("if".to_string())
                    .chain(draw_branches_for_children(&[pattern, condition]))
                    .collect()]
            }
            Pattern::Binding(x) => vec![vec![format!("bind {}", x.node_display().join(""))]],
            Pattern::Ignore => vec![vec!["ignore".to_string()]],
        };

        lines.extend(draw_branches_for_children(&child_components));
        lines
    }
}

impl NodeDisplay for BodyBlock<'_> {
    fn node_display(&self) -> Vec<String> {
        let mut statements: Vec<Vec<String>> = self
            .statements
            .iter()
            .map(|statement| statement.node_display())
            .collect();

        // check if body block has an expression at the end
        if let Some(expr) = &self.expr {
            statements.push(expr.node_display());
        }

        draw_branches_for_children(&statements)
    }
}
