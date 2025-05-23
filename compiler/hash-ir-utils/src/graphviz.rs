//! Graph visualisation tools for the IR. This module contains a builder for
//! generating a `.dot` [graphviz](https://graphviz.org/) file from the IR.
//! This writing backend for the IR will emit the specified [Body] into the
//! `.dot` syntax which can later be interpreted by `graphviz` to generate
//! a visual representation of the IR in formats such as `pdf`, `svg`, `png`,
//! etc.

// @@Todo: add unit tests for the graph writer.

use std::fmt;

use derive_more::Constructor;
use hash_const_eval::print::ConstWriter;
use hash_ir::ir::{BasicBlock, BasicBlockData, Body, BodySource, TerminatorKind};
use hash_repr::{compute::LayoutComputer, constant::Const};
use hash_target::data_layout::HasDataLayout;
use html_escape::encode_text;

use crate::WriteIr;

/// Used to separate line statements between each declaration within
/// a particular body graph.
const LINE_SEPARATOR: &str = r#"<br align="left"/>"#;

#[derive(Debug, Clone)]
pub struct IrGraphOptions {
    /// The font to use for the graph when writing labels, and other
    /// textual snippets.
    font: String,

    /// The background colour of each node as the header of the graph.
    _background_colour: String,

    /// Whether the body should be written directly to the graph or a
    /// sub-graph should be created. If the `use_subgraph` option is
    /// set, then this points to the index to use for the sub-graph
    /// when printing edges, and labels for things.
    use_subgraph: Option<usize>,
}

impl Default for IrGraphOptions {
    fn default() -> Self {
        Self {
            font: "Courier, monospace".to_string(),
            _background_colour: "gray".to_string(),
            use_subgraph: None,
        }
    }
}

#[derive(Constructor)]
pub struct IrBodyWriter<'ir> {
    /// The body that is being outputted as a graph
    body: &'ir Body,

    /// The layout computer.
    lc: LayoutComputer<'ir>,

    /// Options for the style of the graph that is being emitted
    options: IrGraphOptions,
}

impl fmt::Display for IrBodyWriter<'_> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(index) = self.options.use_subgraph {
            writeln!(w, "subgraph cluster_{index} {{")?;
        } else {
            writeln!(w, "digraph {{")?;
        }

        // First of all, we need to write the graph options for the `graph`, `node`, and
        // the `edge`.
        writeln!(w, "  graph [fontname=\"{}\"];", self.options.font)?;
        writeln!(w, "  node [fontname=\"{}\"];", self.options.font)?;
        writeln!(w, "  edge [fontname=\"{}\"];", self.options.font)?;

        // Now we write the `label` of the graph which is essentially the type of
        // the function and any local declarations that have been defined within the
        // body.
        let mut declarations = self.body.locals.iter();

        // return_type declaration, this is always located at `0`
        let return_ty_decl = declarations.next().unwrap();

        match self.body.metadata().source() {
            BodySource::Item => {
                write!(w, "  label=<{}(", self.body.metadata().name,)?;

                // Write the arguments of the function
                for (i, param) in declarations.take(self.body.arg_count).enumerate() {
                    if i > 0 {
                        write!(w, ", ")?;
                    }

                    // We add 1 to the index because the return type is always
                    // located at `0`.
                    write!(w, "{}", encode_text(&format!("_{}: {}", i + 1, param.ty())))?;
                }
                writeln!(
                    w,
                    "{}{}",
                    encode_text(&format!(") -> {} {{", return_ty_decl.ty())),
                    LINE_SEPARATOR
                )?;
            }
            BodySource::Const => {
                let header = format!("{}", self.body.metadata().ty());

                // @@Todo: maybe figure out a better format for this?
                write!(
                    w,
                    "  label=<{}{}{}",
                    self.body.metadata().name,
                    encode_text(&header),
                    LINE_SEPARATOR
                )?;
            }
        };

        // Now we can emit the local declarations that have been defined within the
        // body...
        let declarations = self.body.locals.iter_enumerated();
        let offset = 1 + self.body.arg_count;

        for (local, decl) in declarations.skip(offset) {
            write!(
                w,
                "{}{local:?}: {};{}",
                decl.mutability(),
                encode_text(&format!("{}", decl.ty())),
                LINE_SEPARATOR
            )?;
        }

        // terminate the label
        writeln!(w, ">;")?;

        // Now we write all of the blocks
        for (id, block) in self.body.blocks().iter_enumerated() {
            write!(w, "{}", IrBlockWriter::new(self.body, id, block, &self.options, self.lc))?;
        }

        // Now we need to write all of the edges of the control flow graph
        for (id, block) in self.body.blocks().iter_enumerated() {
            if let Some(terminator) = &block.terminator {
                let prefix = if let Some(index) = self.options.use_subgraph {
                    format!("c{index}_")
                } else {
                    "".to_string()
                };

                match &terminator.kind {
                    TerminatorKind::Assert { target, .. } | TerminatorKind::Goto(target) => {
                        writeln!(w, r#"  {prefix}{id:?} -> {prefix}{target:?} [label=""];"#)?;
                    }
                    TerminatorKind::Call { target, .. } if target.is_some() => {
                        writeln!(
                            w,
                            r#"  {prefix}{:?} -> {prefix}{:?} [label="return"];"#,
                            id,
                            target.unwrap()
                        )?;
                    }
                    TerminatorKind::Switch { targets, value } => {
                        let target_ty = value.ty(&self.body.aux());

                        // Add all of the table cases
                        for (value, target) in targets.iter() {
                            // We want to create an a constant from this value
                            // with the type, and then print it.
                            let value =
                                Const::from_scalar_like(value, target_ty, self.lc.data_layout());

                            writeln!(
                                w,
                                r#"  {prefix}{id:?} -> {prefix}{target:?} [label="{}"];"#,
                                ConstWriter::new(&value, self.lc)
                            )?;
                        }

                        // Add the otherwise case
                        if let Some(otherwise) = targets.otherwise {
                            writeln!(
                                w,
                                r#"  {prefix}{id:?} -> {prefix}{otherwise:?} [label="otherwise"];"#
                            )?;
                        }
                    }
                    TerminatorKind::Call { .. }
                    | TerminatorKind::Unreachable
                    | TerminatorKind::Return => {}
                }
            }
        }

        writeln!(w, "}}")
    }
}

/// Function that writes a block to the appropriate writer. Each block is
/// written with as a table of the name of the block (which is the table
/// header) and a collection of rows which are the statements of the
/// particular block. This function does not deal with all of the
/// outgoing edges of the block, but rather just the statements.
/// The terminator is printed in a similar way to statements, i.e. without
/// denoting all of the edges.
///
/// So for a basic block that has the following shape:
/// ```text
/// bb0 {
///    _1 = moo(const 2_i32) -> bb1;
/// }
/// ```
/// In this example, the local `_1` is being assigned with the return value
/// of `moo`, and after the function `moo` returns, the control flow will
/// jump to `bb1` (since function calls are terminators in the IR).
///
/// An example output table would look like:
/// ```html
/// <table border="0" cellborder="1" cellspacing="0">
///     <tr>
///         <td bgcolor="gray" align="center" colspan="1">0</td>
///     </tr>
///     <tr>
///         <td align="left">_1 = moo(const 2_i32)</td>
///     </tr>
/// </table>
/// ```
/// Each row of the table corresponds to a statement within the block, and
/// the header is the ID of the block.
#[derive(Constructor)]
struct IrBlockWriter<'ir> {
    body: &'ir Body,
    id: BasicBlock,
    block: &'ir BasicBlockData,
    options: &'ir IrGraphOptions,
    lc: LayoutComputer<'ir>,
}

impl fmt::Display for IrBlockWriter<'_> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Now we write the first row, which is the basic block header
        let prefix = if let Some(index) = self.options.use_subgraph {
            format!("c{index}_")
        } else {
            "".to_string()
        };
        let id = format!("{prefix}{:?}", self.id);

        // First write the table, and the header of the table
        write!(
            w,
            r#"  {id} [shape="none", label=<<table border="0" cellborder="1" cellspacing="0">"#
        )?;

        write!(
            w,
            r#"<tr><td bgcolor="{}" align="center" colspan="1">{}</td></tr>"#,
            self.options._background_colour,
            self.id.raw(),
        )?;

        // Now we can write all of the statements within this block
        for statement in self.block.statements.iter() {
            write!(
                w,
                r#"<tr><td align="left" balign="left">{}</td></tr>"#,
                encode_text(&format!("{}", statement.with_edges(self.body.aux(), self.lc, false)))
            )?;
        }

        // write the terminator as the last item of the table
        if let Some(terminator) = &self.block.terminator {
            write!(
                w,
                r#"<tr><td align="left">{}</td></tr>"#,
                encode_text(&format!("{}", terminator.with_edges(self.body.aux(), self.lc, false)))
            )?;
        }

        // close of the table and the label
        writeln!(w, "</table>>];")
    }
}

/// Utility struct to dump all of the provided [Body]s to standard output using
/// the `dot` format.
#[derive(Constructor)]
pub struct IrGraphWriter<'ir> {
    /// The body that is being outputted as a graph
    body: &'ir [&'ir Body],

    /// The layout computer.
    lc: LayoutComputer<'ir>,
}

impl fmt::Display for IrGraphWriter<'_> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(w, "digraph program {{")?;

        for (id, body) in self.body.iter().enumerate() {
            let opts = IrGraphOptions { use_subgraph: Some(id), ..IrGraphOptions::default() };
            writeln!(w, "{}", IrBodyWriter::new(body, self.lc, opts))?;
        }

        writeln!(w, "}}")
    }
}
