//! Utilities and logic to print a collection of items with a specified
//! delimiter and other configuration options.

use hash_ast::{ast, visitor::AstVisitorMutSelf};
use hash_token::delimiter::Delimiter;

use crate::AstPrinter;

/// Various options that can be used to configure how a collection is printed
/// by the `AstPrinter`.
pub struct CollectionPrintingOptions {
    /// The delimiter to use when printing the collection.
    pub delimiter: Option<Delimiter>,

    /// Whether to increase the level of indentation when needing to print
    /// items on a new line, or when `per_line` is specified as true. This
    /// is usually set to `true`.
    pub indent: bool,

    /// Whether to write the delimiters on separate line, and consequently
    /// terminate the line after the delimiter is written.
    pub terminating_delimiters: bool,

    /// Whether to start writing a new item on each collection, this means that
    /// an item is printed, the separator is applied, and then finally a newline
    /// and indentation is added before the next item is printed.
    pub per_line: bool,

    /// Whether to use a separator between each item in the collection.
    pub separator: &'static str,

    /// Whether to apply an ending separator or not, and if so, what to use.
    pub ending_separator: Option<&'static str>,
}

impl CollectionPrintingOptions {
    /// Create a new collection printing options with the default values.
    pub fn separated(separator: &'static str) -> Self {
        Self {
            separator,
            delimiter: None,
            terminating_delimiters: false,
            indent: false,
            per_line: false,
            ending_separator: None,
        }
    }

    /// Create options with a specified delimiter and separator.
    pub fn delimited(delimiter: Delimiter, separator: &'static str) -> Self {
        Self {
            delimiter: Some(delimiter),
            separator,
            terminating_delimiters: false,
            indent: false,
            per_line: false,
            ending_separator: None,
        }
    }

    pub fn with_delimiter(&mut self, delimiter: Delimiter) -> &mut Self {
        self.delimiter = Some(delimiter);
        self
    }

    pub fn with_separator(&mut self, separator: &'static str) -> &mut Self {
        self.separator = separator;
        self
    }

    pub fn with_ending_separator(&mut self, separator: &'static str) -> &mut Self {
        self.ending_separator = Some(separator);
        self
    }

    pub fn indented(&mut self) -> &mut Self {
        self.indent = true;
        self
    }

    pub fn terminating_delimiters(&mut self) -> &mut Self {
        self.terminating_delimiters = true;
        self
    }

    pub fn per_line(&mut self) -> &mut Self {
        self.per_line = true;
        self
    }
}

impl<'ast, T> AstPrinter<'ast, T>
where
    T: std::io::Write,
{
    pub fn print_separated_collection<'k, N>(
        &mut self,
        collection: &'k ast::AstNodes<N>,
        options: CollectionPrintingOptions,
        mut print_item: impl FnMut(&mut Self, ast::AstNodeRef<'k, N>) -> std::io::Result<()>,
    ) -> std::io::Result<()> {
        let len = collection.len();

        let CollectionPrintingOptions {
            delimiter,
            indent,
            per_line,
            separator,
            ending_separator,
            terminating_delimiters,
        } = options;

        if let Some(delimiter) = delimiter {
            self.write(format!("{}", delimiter.left()))?;

            if terminating_delimiters {
                self.terminate_line("")?;
            }
        }

        if indent {
            self.increment_indentation();
        }

        for (i, item) in collection.iter().enumerate() {
            if per_line {
                self.indent()?;
            }

            print_item(self, item.ast_ref())?;

            if i != len - 1 {
                self.write(separator)?;
            } else if let Some(separator) = ending_separator {
                self.write(separator)?;
            }

            // We need to finish the line if an item should be printed per line.
            if per_line {
                self.terminate_line("")?;
            }
        }

        if indent {
            self.decrement_indentation();
        }

        if let Some(delimiter) = delimiter {
            if terminating_delimiters {
                self.indent()?;
            }

            self.write(format!("{}", delimiter.right()))?;

            // @@Cleanup: we don't do this here since the caller will **most**
            // likely terminate the line after this, and so this
            // would cause an extra newline to be printed, which is
            // not what we want.
            //
            // if terminating_delimiters {
            //     self.terminate_line("")?;
            // }
        }

        Ok(())
    }

    pub fn print_pattern_collection<'k, N>(
        &mut self,
        collection: &'k ast::AstNodes<N>,
        spread: &'k Option<ast::AstNode<ast::SpreadPat>>,
        mut print_item: impl FnMut(&mut Self, ast::AstNodeRef<'k, N>) -> std::io::Result<()>,
    ) -> std::io::Result<()> {
        let spread_pos = spread.as_ref().map(|s| s.body().position);

        for (i, item) in collection.iter().enumerate() {
            if i > 0 {
                self.write(", ")?;
            }

            // For the spread pattern, we just insert it into the location that it needs to
            // be in.
            if let Some(pos) = spread_pos && pos == i {
                self.visit_spread_pat(spread.as_ref().unwrap().ast_ref())?;

                if i != collection.len() - 1 {
                    self.write(", ")?;
                }
            }

            print_item(self, item.ast_ref())?;
        }

        Ok(())
    }
}
