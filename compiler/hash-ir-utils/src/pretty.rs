//! Implementation of the pretty printer for the IR.

use std::fmt;

use hash_ir::ir::{BasicBlock, Body, BodySource};
use hash_repr::compute::LayoutComputer;
use hash_utils::{derive_more::Constructor, itertools::Itertools};

use crate::WriteIr;

/// [IrBodyWriter] is used to encapsulate the logic of pretty-printing a
/// [Body] to a [fmt::Formatter]. The [IrBodyWriter] is uses the standalone
/// implementations for displaying each IR component with the addition of adding
/// formatting, and additional information about the IR in the style of comments
/// on each IR line (if additional information exists).
pub struct IrBodyWriter<'ir> {
    /// The body that is being printed
    body: &'ir Body,

    /// The layout computer is used to compute the layout of the data
    /// under the constant.
    lc: LayoutComputer<'ir>,
}

impl<'ir> IrBodyWriter<'ir> {
    /// Create a new IR writer for the given body.
    pub fn new(body: &'ir Body, lc: LayoutComputer<'ir>) -> Self {
        Self { body, lc }
    }

    /// Function to deal with a [Body] header which is formatted depending on
    /// the [BodySource] of the [Body]. For function items, the format mimics
    /// a function declaration:
    /// ```ignore
    /// foo := (_0: i32, _1: i32) -> i32 {
    ///    ...
    /// }
    /// ```
    /// and for constants:
    /// ```ignore
    /// const koo {
    ///    ...
    /// }
    /// ```
    fn write_header(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut declarations = self.body.locals.iter();

        // return_type declaration, this is always located at `0`
        let return_ty_decl = declarations.next().unwrap();

        match self.body.metadata().source() {
            BodySource::Item => {
                write!(f, "{} := (", self.body.metadata().name)?;

                for (i, param) in declarations.take(self.body.arg_count).enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    // We add 1 to the index because the return type is always
                    // located at `0`.
                    write!(f, "_{}: {}", i + 1, param.ty())?;
                }
                writeln!(f, ") -> {} {{", return_ty_decl.ty())?;
            }
            BodySource::Const => {
                writeln!(f, "const {} {{", self.body.metadata().name)?;
            }
        }

        // Print the return place declaration
        writeln!(f, "    {}_0: {};", return_ty_decl.mutability(), return_ty_decl.ty())
    }

    /// Write the body to the given formatter.
    fn write_body(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write_header(f)?;

        let declarations = self.body.locals.iter_enumerated().take(self.body.arg_count + 1);

        // We write debug information about the parameters of the function in
        // the format of `// parameter <name> -> _index`
        if self.body.arg_count > 0 {
            writeln!(f)?;
        }

        for (local, decl) in declarations {
            if let Some(name) = decl.name
                && !decl.auxiliary()
            {
                writeln!(f, "    // parameter `{}` -> _{}", name, local.index())?;
            }
        }

        // Add some spacing between the parameter comments
        if self.body.arg_count > 0 {
            writeln!(f)?;
        }

        // Next, we render the declarations and then we will render them in order
        // top properly align all of the comments on the right hand side.
        let offset = 1 + self.body.arg_count;
        let declarations = self.body.locals.iter_enumerated().skip(offset);

        let mut longest_line = 0;
        let rendered_declarations = declarations
            .map(|(local, decl)| {
                let s = format!("{}{local:?}: {};", decl.mutability(), decl.ty());

                if let Some(name) = decl.name
                    && !decl.auxiliary()
                {
                    longest_line = longest_line.max(s.len());
                    (s, Some(format!("// parameter `{name}`")))
                } else {
                    (s, None)
                }
            })
            .collect_vec();

        for (declaration, comment) in rendered_declarations {
            write!(f, "    {declaration}")?;
            if let Some(comment) = comment {
                writeln!(f, "{: <1$}\t{comment}", "", longest_line - declaration.len())?;
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
            writeln!(
                f,
                "{: <2$}{};",
                "",
                statement.with_edges(self.body.aux(), self.lc, false),
                8
            )?;
        }

        // Write the terminator of the block. If the terminator is
        // not present, this is an invariant but we don't care here.
        if let Some(terminator) = &block_data.terminator {
            writeln!(
                f,
                "{: <2$}{};",
                "",
                terminator.with_edges(self.body.aux(), self.lc, true),
                8
            )?;
        }

        writeln!(f, "{: <1$}}}", "", 4)
    }
}

impl fmt::Display for IrBodyWriter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write_body(f)
    }
}

#[derive(Constructor)]
pub struct IrPrettyWriter<'ir> {
    /// The body that is being outputted as a graph
    bodies: &'ir [&'ir Body],

    /// The layout computer.
    lc: LayoutComputer<'ir>,
}

impl fmt::Display for IrPrettyWriter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Self { bodies, lc } = *self;

        for (index, body) in bodies.iter().enumerate() {
            // Padding between each body
            if index > 0 {
                writeln!(f)?;
            }

            writeln!(
                f,
                "IR dump for {} `{}` defined at {}\n{}",
                body.metadata().source(),
                body.metadata().name(),
                body.span().fmt_path(),
                IrBodyWriter::new(body, lc)
            )?;
        }

        Ok(())
    }
}
