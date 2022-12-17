//! Implementation of the pretty printer for the IR.

use std::fmt;

use hash_source::SourceMap;

use super::WriteIr;
use crate::{
    ir::{BasicBlock, Body, BodySource},
    IrStorage,
};

/// [IrBodyWriter] is used to encapsulate the logic of pretty-printing a
/// [IrBody] to a [fmt::Formatter]. The [IrBodyWriter] is uses the standalone
/// implementations for displaying each IR component with the addition of adding
/// formatting, and additional information about the IR in the style of comments
/// on each IR line (if additional information exists).
pub struct IrBodyWriter<'ir> {
    /// The type context allowing for printing any additional
    /// metadata about types within the ir.
    ctx: &'ir IrStorage,
    /// The body that is being printed
    body: &'ir Body,
}

impl<'ir> IrBodyWriter<'ir> {
    /// Create a new IR writer for the given body.
    pub fn new(ctx: &'ir IrStorage, body: &'ir Body) -> Self {
        Self { ctx, body }
    }

    /// Function to deal with a [Body] header which is formatted depending on
    /// the [BodySource] of the [Body]. For function items, the format mimics
    /// a function declaration:
    /// ```ignore
    /// foo(_0: i32, _1: i32) -> i32 {
    ///    ...
    /// }
    /// ```
    /// and for constants:
    /// ```ignore
    /// const foo {
    ///    ...
    /// }
    /// ```
    fn write_header(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut declarations = self.body.declarations.iter();

        // return_type declaration, this is always located at `0`
        let return_ty_decl = declarations.next().unwrap();

        match self.body.info().source() {
            BodySource::Item | BodySource::Intrinsic => {
                write!(f, "{}(", self.body.info().name)?;

                for (i, param) in declarations.take(self.body.arg_count).enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    // We add 1 to the index because the return type is always
                    // located at `0`.
                    write!(f, "_{}: {}", i + 1, param.ty().for_fmt(self.ctx))?;
                }
                writeln!(f, ") -> {} {{", return_ty_decl.ty().for_fmt(self.ctx))?;
            }
            BodySource::Const => {
                writeln!(f, "const {} {{", self.body.info().name)?;
            }
        }

        // Print the return place declaration
        writeln!(
            f,
            "    {}_0: {};",
            return_ty_decl.mutability(),
            return_ty_decl.ty().for_fmt(self.ctx)
        )
    }

    /// Write the body to the given formatter.
    fn write_body(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write_header(f)?;

        let declarations = self.body.declarations.iter_enumerated();
        let offset = 1 + self.body.arg_count;

        for (local, decl) in declarations.skip(offset) {
            write!(f, "    {}{local:?}: {};", decl.mutability(), decl.ty().for_fmt(self.ctx))?;

            if let Some(name) = decl.name && !decl.auxiliary() {
                writeln!(f, "\t\t// parameter `{name}`")?;
            } else {
                writeln!(f)?;
            }
        }

        // Print all of the basic blocks
        for (bb, _) in self.body.basic_blocks.blocks.iter_enumerated() {
            writeln!(f)?;
            self.write_block(bb, f)?;
        }

        writeln!(f, "}}")
    }

    fn write_block(&self, block: BasicBlock, f: &mut fmt::Formatter) -> fmt::Result {
        // Print the label for the block
        writeln!(f, "{: <1$}{block:?} {{", "", 4)?;
        let block_data = &self.body.blocks()[block];

        // Write all of the statements within the block
        for statement in &block_data.statements {
            writeln!(f, "{: <2$}{};", "", statement.for_fmt(self.ctx), 8)?;
        }

        // Write the terminator of the block. If the terminator is
        // not present, this is an invariant but we don't care here.
        if let Some(terminator) = &block_data.terminator {
            writeln!(f, "{: <2$}{};", "", terminator.fmt_with_opts(self.ctx, false, true), 8)?;
        }

        writeln!(f, "{: <1$}}}", "", 4)
    }
}

impl fmt::Display for IrBodyWriter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write_body(f)
    }
}

/// Dump all of the provided [Body]s to standard output using the `dot` format.
pub fn dump_ir_bodies(
    storage: &IrStorage,
    source_map: &SourceMap,
    bodies: &[Body],
    dump_all: bool,
) {
    for (index, body) in bodies.iter().enumerate() {
        // Check if we need to print this body (or if we're printing all of them)
        // and then skip bodies that we didn't request to print.
        if !dump_all && !body.needs_dumping() {
            continue;
        }

        // Padding between each body
        if index > 0 {
            println!();
        }

        println!(
            "IR dump for {} `{}` defined at {}\n{}",
            body.info().source(),
            body.info().name(),
            source_map.fmt_location(body.location()),
            IrBodyWriter::new(storage, body)
        );
    }
}
