//! Implementation of the `#dump_ast` attribute.

use std::fmt;

use derive_more::Constructor;
use hash_utils::{
    clap,
    schemars::{self, JsonSchema},
    serde::{self, Deserialize, Serialize},
    temp_writer::TempWriter,
    tree_writing::{CharacterSet, TreeWriter, TreeWriterConfig},
};

use crate::{attr::AttrNode, pretty::AstPrettyPrinter, tree::AstTreePrinter};

/// Enum representing the different options for dumping the IR. It can either
/// be emitted in the pretty-printing format, or in the `graphviz` format.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum, Deserialize, Serialize, JsonSchema,
)]
#[serde(crate = "self::serde")]
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

/// A utility that is used to dump the AST in a given format.
///
/// Specifically, dump the given [AttrNode] using the given [AstDumpMode] and
/// an optional [CharacterSet] for the `tree` format.
#[derive(Constructor)]
pub struct AstDump<'ast> {
    /// The AST node that should be dumped.
    node: AttrNode<'ast>,

    /// The style in which the AST should be dumped.
    mode: AstDumpMode,

    /// The character set that should be used when dumping
    /// the AST in the `tree` format. It can a number of options such as, but
    /// not limited to [`CharacterSet::Ascii`] or [`CharacterSet::Unicode`].
    character_set: CharacterSet,
}

impl fmt::Display for AstDump<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { node, mode, character_set } = self;

        writeln!(f, "AST for {}:", node.id().span().fmt_path())?;

        match mode {
            AstDumpMode::Pretty => {
                let mut buf = TempWriter::default();
                let printer = AstPrettyPrinter::new(&mut buf);

                // @@TODO: Handle error properly or convert the visitor to just
                // use a fmt::Error?
                node.visit_mut(printer).map_err(|_| fmt::Error)?;
                writeln!(f, "{}", buf.as_str())
            }
            AstDumpMode::Tree => {
                let tree = node.visit(AstTreePrinter).unwrap();
                let config = TreeWriterConfig::from_character_set(*character_set);
                write!(f, "{}", TreeWriter::new_with_config(&tree, config))
            }
        }
    }
}
