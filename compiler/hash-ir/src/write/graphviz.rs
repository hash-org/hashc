//! Graph visualisation tools for the IR. This module contains a builder for
//! generating a `.dot` [graphviz](https://graphviz.org/) file from the IR. This can be used to
//! convert a [Body] into a graph that can be visualised. This writing backend
//! for the IR will emit

use html_escape::encode_text;

use crate::{
    ir::{BasicBlock, BasicBlockData, Body, TerminatorKind},
    write::WriteIr,
    IrStorage,
};

/// Used to separate line statements between each declaration within
/// a particular body graph.
const LINE_SEPARATOR: &str = r#"<br align="left"/>"#;

pub struct IrGraphWriter<'ir> {
    /// The IR storage that contains
    ctx: &'ir IrStorage,

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
}

impl Default for IrGraphOptions {
    fn default() -> Self {
        Self { font: "Courier, monospace".to_string(), background_colour: "gray".to_string() }
    }
}

impl<'ir> IrGraphWriter<'ir> {
    pub fn new(storage: &'ir IrStorage, body: &'ir Body, options: IrGraphOptions) -> Self {
        Self { ctx: storage, body, options }
    }

    /// Function that writes the body to the appropriate writer.
    pub fn write_body(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        writeln!(w, "digraph {} {{", self.body.name)?;

        // First of all, we need to write the graph options for the `graph`, `node`, and
        // the `edge`.
        writeln!(
            w,
            "  graph [fontname=\"{}\", bgcolor=\"{}\"]",
            self.options.font, self.options.background_colour
        )?;
        writeln!(
            w,
            "  node [fontname=\"{}\", bgcolor=\"{}\"]",
            self.options.font, self.options.background_colour
        )?;
        writeln!(
            w,
            "  edge [fontname=\"{}\", bgcolor=\"{}\"]",
            self.options.font, self.options.background_colour
        )?;

        // Now we write the `label` of the graph which is essentially the type of
        // the function and any local declarations that have been defined within the
        // body.
        write!(
            w,
            " label=<{}{}{}",
            self.body.name,
            self.body.ty.fmt_with_opts(self.ctx, true, true),
            LINE_SEPARATOR
        )?;

        // Now we can emit the local declarations that have been defined within the
        // body...
        let declarations = self.body.declarations.iter_enumerated();
        let offset = 1 + self.body.arg_count;

        for (local, decl) in declarations.skip(offset) {
            write!(
                w,
                "{}{local:?}: {};{}",
                decl.mutability(),
                decl.ty().fmt_with_opts(self.ctx, true, true),
                LINE_SEPARATOR
            )?;
        }

        // terminate the label
        writeln!(w, ">;")?;

        // Now we write all of the blocks
        for (id, block) in self.body.blocks.iter_enumerated() {
            self.write_block(w, id, block)?;
        }

        // Now we need to write all of the edges of the control flow graph
        for (id, block) in self.body.blocks.iter_enumerated() {
            if let Some(terminator) = &block.terminator {
                match &terminator.kind {
                    TerminatorKind::Assert { target, .. } | TerminatorKind::Goto(target) => {
                        writeln!(w, r#"  {id:?} -> {target:?} [label=""];"#)?;
                    }
                    TerminatorKind::Call { target, .. } => {
                        writeln!(w, r#"  {id:?} -> {target:?} [label="return"];"#)?;
                    }
                    TerminatorKind::Switch { table, otherwise, .. } => {
                        // Add all of the table cases
                        for (value, target) in table.iter() {
                            writeln!(w, r#"  {id:?} -> {target:?} [label="{value}"];"#)?;
                        }

                        // Add the otherwise case
                        writeln!(w, r#"  {id:?} -> {otherwise:?} [label="otherwise"];"#)?;
                    }
                    TerminatorKind::Unreachable | TerminatorKind::Return => {}
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
        w: &mut impl std::io::Write,
        id: BasicBlock,
        block: &'ir BasicBlockData,
    ) -> std::io::Result<()> {
        // First write the table, and the header of the table
        write!(
            w,
            "  {id:?} [shape=none, label=<<table border=\"0\", cellborder=\"1\" cellspacing=\"0\">"
        )?;

        // Now we write the first row, which is the basic block header
        write!(w, r#"<tr><td bgcolor="gray" align="center" colspan="1">{}</td></tr>"#, id.raw())?;

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
                r#"<tr><td align="left" balign="left">{}</td></tr>"#,
                encode_text(&format!("{}", terminator.for_fmt(self.ctx)))
            )?;
        }

        // close of the table and the label
        writeln!(w, "</table>>];")
    }
}
