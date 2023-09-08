//! Implementation of the `#dump_ast` attribute.

use std::fmt;

use hash_utils::{
    clap,
    tree_writing::{CharacterSet, TreeWriter, TreeWriterConfig},
};

use crate::{attr::AttrNode, pretty::AstPrettyPrinter, tree::AstTreePrinter};

/// Enum representing the different options for dumping the IR. It can either
/// be emitted in the pretty-printing format, or in the `graphviz` format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum AstDumpMode {
    /// Dump the AST using a pretty-printed format
    Pretty,

    /// Dump the AST using the `tree` format
    Tree,
}

impl fmt::Display for AstDumpMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Pretty => write!(f, "pretty"),
            Self::Tree => write!(f, "tree"),
        }
    }
}

/// Dump the given [AttrNode] to the given [fmt::Write] using the given
/// [AstDumpMode].
pub fn dump_ast(
    node: AttrNode<'_>,
    mode: AstDumpMode,
    character_set: CharacterSet,
    writer: &mut impl std::io::Write,
) -> std::io::Result<()> {
    match mode {
        AstDumpMode::Pretty => {
            let printer = AstPrettyPrinter::new(writer);
            node.visit_mut(printer)?;
        }
        AstDumpMode::Tree => {
            // In the tree mode, we prepend the output with the item that we dumped.
            writeln!(writer, "AST for `{}`:", node.id().span().fmt_path())?;

            let tree = node.visit(AstTreePrinter).unwrap();
            let config = TreeWriterConfig::from_character_set(character_set);
            writeln!(writer, "{}", TreeWriter::new_with_config(&tree, config))?;
        }
    }

    Ok(())
}
