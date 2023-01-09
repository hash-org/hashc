//! Graph visualisation tools for the IR. This module contains a builder for
//! generating a `.dot` [graphviz](https://graphviz.org/) file from the IR.
//! This writing backend for the IR will emit the specified [Body] into the
//! `.dot` syntax which can later be interpreted by `graphviz` to generate
//! a visual representation of the IR in formats such as `pdf`, `svg`, `png`,
//! etc.

use std::io;

use html_escape::encode_text;

use crate::{
    ir::{BasicBlock, BasicBlockData, Body, BodySource, Const, TerminatorKind},
    write::WriteIr,
    IrCtx,
};

/// Used to separate line statements between each declaration within
/// a particular body graph.
const LINE_SEPARATOR: &str = r#"<br align="left"/>"#;

pub struct IrGraphWriter<'ir> {
    /// Store that contains all interned data for the IR.
    ctx: &'ir IrCtx,

    /// The body that is being outputted as a graph
    body: &'ir Body,

    /// Options for the style of the graph that is being emitted
    options: IrGraphOptions,
}

#[derive(Debug, Clone)]
pub struct IrGraphOptions {
    /// The font to use for the graph when writing labels, and other
    /// textual snippets.
    font: String,

    /// The background colour of each node as the header of the graph.
    background_colour: String,

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
            background_colour: "gray".to_string(),
            use_subgraph: None,
        }
    }
}

impl<'ir> IrGraphWriter<'ir> {
    pub fn new(ctx: &'ir IrCtx, body: &'ir Body, options: IrGraphOptions) -> Self {
        Self { ctx, body, options }
    }

    /// Function that writes the body to the appropriate writer.
    pub fn write_body(&self, w: &mut impl io::Write) -> io::Result<()> {
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

        // Compute the header of the current graph.
        let header = match self.body.info().source() {
            BodySource::Item | BodySource::Intrinsic => {
                format!("{}", self.body.info().ty().fmt_with_opts(self.ctx, true, false))
            }
            BodySource::Const => {
                // @@Todo: maybe figure out a better format for this?
                format!(": {}", self.body.info().ty().fmt_with_opts(self.ctx, true, false))
            }
        };

        // Now we write the `label` of the graph which is essentially the type of
        // the function and any local declarations that have been defined within the
        // body.
        write!(w, "  label=<{}{}{}", self.body.info().name, encode_text(&header), LINE_SEPARATOR)?;

        // Now we can emit the local declarations that have been defined within the
        // body...
        let declarations = self.body.declarations.iter_enumerated();
        let offset = 1 + self.body.arg_count;

        for (local, decl) in declarations.skip(offset) {
            write!(
                w,
                "{}{local:?}: {};{}",
                decl.mutability(),
                encode_text(&format!("{}", decl.ty().fmt_with_opts(self.ctx, true, false))),
                LINE_SEPARATOR
            )?;
        }

        // terminate the label
        writeln!(w, ">;")?;

        // Now we write all of the blocks
        for (id, block) in self.body.blocks().iter_enumerated() {
            self.write_block(w, id, block)?;
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
                    TerminatorKind::Switch { targets, .. } => {
                        // Add all of the table cases
                        for (value, target) in targets.iter() {
                            // We want to create an a constant from this value
                            // with the type, and then print it.
                            let value = Const::from_scalar(value, targets.ty, self.ctx);

                            writeln!(
                                w,
                                r#"  {prefix}{id:?} -> {prefix}{target:?} [label="{value}"];"#
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
    fn write_block(
        &self,
        w: &mut impl io::Write,
        id: BasicBlock,
        block: &'ir BasicBlockData,
    ) -> io::Result<()> {
        // Now we write the first row, which is the basic block header
        let block_id = if let Some(index) = self.options.use_subgraph {
            format!("c{index}_{id:?}")
        } else {
            format!("{:?}", id.raw())
        };

        // First write the table, and the header of the table
        write!(
            w,
            r#"  {block_id} [shape="none", label=<<table border="0" cellborder="1" cellspacing="0">"#
        )?;

        write!(
            w,
            r#"<tr><td bgcolor="{}" align="center" colspan="1">{}</td></tr>"#,
            self.options.background_colour,
            id.raw(),
        )?;

        // Now we can write all of the statements within this block
        for statement in block.statements.iter() {
            write!(
                w,
                r#"<tr><td align="left" balign="left">{}</td></tr>"#,
                encode_text(&format!("{}", statement.for_fmt(self.ctx)))
            )?;
        }

        // write the terminator as the last item of the table
        if let Some(terminator) = &block.terminator {
            write!(
                w,
                r#"<tr><td align="left">{}</td></tr>"#,
                encode_text(&format!("{}", terminator.fmt_with_opts(self.ctx, false, false)))
            )?;
        }

        // close of the table and the label
        writeln!(w, "</table>>];")
    }
}

/// Dump all of the provided [Body]s to standard output using the `dot` format.
pub fn dump_ir_bodies(ctx: &IrCtx, bodies: &[Body], dump_all: bool) {
    let mut w = io::stdout();

    println!("digraph program {{");

    for (id, body) in bodies.iter().enumerate() {
        // Check if we need to print this body (or if we're printing all of them)
        // and then skip bodies that we didn't request to print.
        if !dump_all && !body.needs_dumping() {
            continue;
        }

        let opts = IrGraphOptions { use_subgraph: Some(id), ..IrGraphOptions::default() };
        let dumper = IrGraphWriter::new(ctx, body, opts);
        dumper.write_body(&mut w).unwrap();
    }

    println!("}}");
}
