//! Logic and implementation for printing raw tokens that appear in the AST.

use hash_source::location::SpannedSource;
use hash_token::{Token, TokenKind, delimiter::Delimiter};

use super::{AstPrettyPrinter, FmtResult};

impl<T> AstPrettyPrinter<'_, T>
where
    T: std::io::Write,
{
    /// Write a token tree.
    ///
    /// @@Todo: potentially format token trees in some way that preserves the
    /// line order.
    pub(super) fn write_token_tree(
        &mut self,
        delimiter: Delimiter,
        tree: &[Token],
        source: SpannedSource<'_>,
    ) -> FmtResult {
        self.write_char(delimiter.left())?;

        for token in tree {
            if let TokenKind::Tree(delim, length) = token.kind {
                self.write_token_tree(delim, &tree[..(length as usize)], source)?;
            } else {
                self.write_token(token, source)?;
            }

            // @@Future: figure out the exact formatting for this. Currently, we will just
            // pretty-print the tokens as they are separated by spaces, we might
            // want to take in account token spacing in the future.
            self.write(" ")?;
        }

        self.write_char(delimiter.right())
    }

    /// Write an atomic token, i.e. one that is not a tree.
    fn write_token(&mut self, token: &Token, source: SpannedSource<'_>) -> FmtResult {
        self.write(token.pretty_print(source))
    }
}
