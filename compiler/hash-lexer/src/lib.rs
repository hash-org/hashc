//! Hash Compiler Lexer crate.
#![feature(if_let_guard)]

use std::cell::Cell;

use hash_reporting::{
    diagnostic::HasDiagnosticsMut, unicode_normalization::char::is_combining_mark,
};
use hash_source::{
    SourceId,
    constant::LocalStringTable,
    identifier::{IDENTS, Identifier},
    location::{ByteRange, Span, SpannedSource},
};
use hash_target::primitives::{FloatTy, IntTy};
use hash_token::{
    Base, FloatLitKind, IntLitKind, Token, TokenKind, delimiter::Delimiter,
    keyword::ident_is_keyword,
};
use hash_utils::{itertools::Itertools, thin_vec::thin_vec};

use crate::{
    error::{LexerDiagnostics, LexerError, LexerErrorKind, LexerResult, NumericLitKind},
    utils::{is_id_continue, is_id_start},
};

pub mod error;
mod utils;

/// Information about a tree that is being lexed by the [Lexer]. Includes
/// information about the start of the lexer (in the token buffer), and if the
/// lexer consumed a delimiter token.
#[derive(Clone, Copy, Debug)]
struct TreeInfo {
    /// An index into the stream of tokens, pointing to where the tree begins.
    start: usize,

    /// The kind of [Delimiter] that the tree is.
    delimiter: Option<Delimiter>,
}

/// Useful information that the lexer collects during the lexing process, and
/// which is used after the lexer has finished performing AST generation.
pub struct LexerMetadata {
    /// Token tree store, essentially a collection of token trees that are
    /// produced when the lexer encounters bracketed token streams.
    pub tokens: Vec<Token>,

    /// Local lexer string table.
    pub strings: LocalStringTable,

    pub diagnostics: LexerDiagnostics,
}

/// Representing the end of stream, or the initial character that is set as
/// 'prev' in a [Lexer] since there is no character before the start.
const EOF_CHAR: char = '\0';

/// The [Lexer] is a representation of the source in tokens that can be turned
/// into the AST. The [Lexer] has methods that can parse various token types
/// from the source, transform the entire contents into a vector of tokens and
/// some useful lexing utilities.
pub struct Lexer<'a> {
    /// Location of the lexer in the current stream.
    offset: Cell<usize>,

    /// The contents that are to be lexed.
    contents: SpannedSource<'a>,

    /// Representative module index of the current source.
    source_id: SourceId,

    tree: Cell<Option<TreeInfo>>,

    /// Local lexer string table.
    strings: LocalStringTable,

    /// The tokens that the lexer produced.
    tokens: Vec<Token>,

    /// The lexer diagnostics store
    diagnostics: LexerDiagnostics,
}

impl<'a> Lexer<'a> {
    /// Create a new [Lexer] from the given string input.
    pub fn new(contents: SpannedSource<'a>, source_id: SourceId) -> Self {
        Self {
            offset: Cell::new(0),
            source_id,
            tree: Cell::new(None),
            contents,
            // @@Explain the 3/16
            tokens: Vec::with_capacity(contents.0.len() * 3 / 16),
            diagnostics: LexerDiagnostics::default(),
            strings: LocalStringTable::default(),
        }
    }

    /// Emit an error into [LexerDiagnostics] and also
    /// set `has_fatal_error` flag to true so that the
    /// lexer terminates on the next advancement.
    #[inline]
    fn emit_fatal_error(&mut self, kind: LexerErrorKind, span: ByteRange) -> TokenKind {
        self.diagnostics.has_fatal_error.set(true);
        self.emit_error(kind, span)
    }

    /// Put an error into the [LexerDiagnostics], whilst returning a
    /// [TokenKind::Err] in place of a lexed token.
    #[inline]
    fn emit_error(&mut self, kind: LexerErrorKind, span: ByteRange) -> TokenKind {
        self.add_error(LexerError { kind, location: Span { range: span, id: self.source_id } });

        TokenKind::Err
    }

    /// Create a Lexer error and return a [Result], but internally
    /// it is always the [Err] variant.
    #[inline]
    fn error<T>(&self, kind: LexerErrorKind, span: ByteRange) -> Result<T, LexerError> {
        Err(LexerError { kind, location: Span { range: span, id: self.source_id } })
    }

    /// Tokenise the given input stream
    pub fn tokenise(mut self) -> LexerMetadata {
        // Avoid shebang at the start of the source...
        self.strip_shebang();

        while let Some(token) = self.advance_token() {
            self.tokens.push(token);
        }

        LexerMetadata { tokens: self.tokens, diagnostics: self.diagnostics, strings: self.strings }
    }

    /// Returns amount of already consumed symbols.
    #[inline(always)]
    fn len_consumed(&self) -> usize {
        self.offset.get() - 1
    }

    /// Get the remaining un-lexed contents as a raw string.
    #[inline]
    unsafe fn as_slice(&self) -> &str {
        let offset = self.offset.get();

        // ##Safety: We rely that the byte offset is correctly computed when stepping
        // over the characters in the iterator.
        unsafe { std::str::from_utf8_unchecked(self.contents.0.as_bytes().get_unchecked(offset..)) }
    }

    /// Returns nth character relative to the current position.
    /// If requested position doesn't exist, `EOF_CHAR` is returned.
    /// However, getting `EOF_CHAR` doesn't always mean actual end of file,
    /// it should be checked with `is_eof` method.
    fn nth_char(&self, n: usize) -> char {
        let slice = unsafe { self.as_slice() };

        slice.chars().nth(n).unwrap_or(EOF_CHAR)
    }

    /// Peeks the next symbol from the input stream without consuming it.
    #[inline]
    fn peek(&self) -> char {
        self.nth_char(0)
    }

    /// Peeks the second symbol from the input stream without consuming it.
    #[inline]
    fn peek_second(&self) -> char {
        self.nth_char(1)
    }

    /// Moves to the next character.
    #[inline]
    fn next(&mut self) -> Option<char> {
        let slice = unsafe { self.as_slice() };
        let ch = slice.chars().next()?;
        self.offset.update(|x| x + ch.len_utf8());
        Some(ch)
    }

    /// Move to the next character and skip it essentially.
    #[inline]
    fn skip(&self) {
        let slice = unsafe { self.as_slice() };
        let ch = slice.chars().next().unwrap();
        self.offset.update(|x| x + ch.len_utf8());
    }

    #[inline]
    fn skip_ascii(&self) {
        self.offset.update(|x| x + 1);
    }

    /// Checks if there is nothing more to consume.
    fn is_eof(&self) -> bool {
        self.contents.0.len() == self.offset.get()
    }

    /// Strip the shebang, e.g. "#!/usr/bin/hashc", from a source assuming that
    /// this is the start of the file.
    fn strip_shebang(&mut self) {
        if self.peek() == '#' && self.peek_second() == '!' {
            // This is a module level attribute on the first line, so we don't treat
            // this as a shebang.
            if self.nth_char(2) == '[' {
                return;
            }

            self.eat_while_and_discard(|c| c != '\n');
        }
    }

    /// Parses a token from the input string.
    pub fn advance_token(&mut self) -> Option<Token> {
        // Eat any comments or whitespace before processing the token...
        loop {
            match self.peek() {
                c if c.is_whitespace() => self.eat_while_and_discard(char::is_whitespace),
                '/' => match self.peek_second() {
                    '*' => self.block_comment(),
                    '/' => self.line_comment(),
                    _ => {
                        self.skip_ascii();
                        let offset = self.offset.get();

                        // ##Hack: since we already compare if the first item is a slash, we'll just
                        // return here the slash and advance it by one.
                        return Some(Token::new(
                            TokenKind::Slash,
                            ByteRange::new(offset, offset + 1),
                        ));
                    }
                },
                _ => break,
            }
        }

        let offset = self.offset.get();
        let kind = match self.next()? {
            '~' => TokenKind::Tilde,
            '!' => TokenKind::Exclamation,
            '+' => TokenKind::Plus,
            '*' => TokenKind::Star,
            '%' => TokenKind::Percent,
            '>' => TokenKind::Gt,
            '<' => TokenKind::Lt,
            '|' => TokenKind::Pipe,
            '^' => TokenKind::Caret,
            '&' => TokenKind::Amp,
            ';' => TokenKind::Semi,
            ',' => TokenKind::Comma,
            '#' => TokenKind::Pound,
            '@' => TokenKind::At,
            '$' => TokenKind::Dollar,
            '?' => TokenKind::Question,
            '.' => match self.peek() {
                '.' => {
                    self.skip_ascii();
                    match self.peek() {
                        '.' => {
                            self.skip_ascii();
                            TokenKind::Ellipsis
                        }
                        '<' => {
                            self.skip_ascii();
                            TokenKind::RangeExclusive
                        }
                        _ => TokenKind::Range,
                    }
                }
                _ => TokenKind::Dot,
            },
            ':' => match self.peek() {
                ':' => {
                    self.skip_ascii();
                    TokenKind::Access
                }
                _ => TokenKind::Colon,
            },
            '=' => match self.peek() {
                '>' => {
                    self.skip_ascii();
                    TokenKind::FatArrow
                }
                _ => TokenKind::Eq,
            },
            '-' => match self.peek() {
                '>' => {
                    self.skip_ascii();
                    TokenKind::ThinArrow
                }
                ch if ch.is_ascii_digit() => self.number(self.peek(), true),
                _ => TokenKind::Minus,
            },
            // Consume a token tree, which is a starting delimiter, followed by a an arbitrary
            // number of tokens and closed by a following delimiter...
            ch @ ('(' | '{' | '[') => {
                let delimiter = Delimiter::from_left(ch).unwrap();
                self.tokens.push(Token::new(
                    TokenKind::Tree(delimiter, 0),
                    ByteRange::new(offset, self.len_consumed()),
                ));

                let _ = self.eat_token_tree(delimiter);

                if self.diagnostics.has_fatal_error.get() {
                    return None;
                }

                // Immediately try to index the next token...
                return self.advance_token();
            }
            ch @ '0'..='9' => self.number(ch, false),
            '\'' => self.char(false),
            '"' => self.string(),
            ch @ 'b' => match self.peek() {
                '\'' => {
                    self.skip_ascii();
                    self.byte_literal()
                }
                _ => self.ident(ch),
            },

            // Identifier (this should be checked after other variant that can
            // start as identifier).
            ch if is_id_start(ch) => self.ident(ch),
            // We have to exit the current tree if we encounter a closing delimiter...
            ch @ (')' | '}' | ']') if let Some(mut info) = self.tree.get() => {
                info.delimiter = Some(Delimiter::from_right(ch).unwrap());
                self.tree.set(Some(info));

                return None;
            }
            ')' => TokenKind::RightDelim(Delimiter::Paren),
            '}' => TokenKind::RightDelim(Delimiter::Brace),
            ']' => TokenKind::RightDelim(Delimiter::Bracket),
            // We didn't get a hit on the right token...
            ch => TokenKind::Unexpected(ch),
        };

        // If we encountered a unrecoverable error, then terminate
        if self.diagnostics.has_fatal_error.get() {
            return None;
        }

        let location = ByteRange::new(offset, self.len_consumed());
        Some(Token::new(kind, location))
    }

    /// This will essentially recursively consume tokens until it reaches the
    /// right hand-side variant of the provided delimiter. If no delimiter
    /// is reached, but the stream has reached EOF, this is reported
    /// as an error because it is essentially an un-closed block. This kind of
    /// behaviour is desired and avoids performing complex delimiter depth
    /// analysis later on.
    fn eat_token_tree(&mut self, delimiter: Delimiter) -> TokenKind {
        let delim_offset = self.offset.get() - 1; // we need to ge the previous location to accurately denote the error...

        // we need to reset self.prev here as it might be polluted with previous token
        // trees
        let tree = Cell::new(Some(TreeInfo { start: self.tokens.len(), delimiter: None }));
        self.tree.swap(&tree);

        // `None` here doesn't just mean EOF, it could also be that
        // the next token failed to be parsed.
        while !self.is_eof() {
            match self.advance_token() {
                Some(token) => self.tokens.push(token),
                None => break,
            }
        }

        // ##Note: Now that we have done parsing the inner tree (with or without error),
        // we want to put the `old` tree value back into `self.tree`, and
        // retrieve the one that we were working with. Beyond this point,
        // everyone should refer to `tree`, not `self.tree` since this is now
        // the old one.
        self.tree.swap(&tree);

        // If there is a fatal error, then we need to abort
        if self.diagnostics.has_fatal_error.get() {
            return TokenKind::Err;
        }

        match tree.get() {
            Some(TreeInfo { delimiter: Some(d), start, .. }) if d == delimiter => {
                // Update the tree token with the length of the tree.
                self.tokens[start - 1] = Token::new(
                    TokenKind::Tree(delimiter, (self.tokens.len() - start) as u32),
                    ByteRange::new(delim_offset, self.len_consumed()),
                );

                // ##Hack: This token won't be put into the token stream, it's just
                // a dummy token to denote the end of the tree.
                TokenKind::RightDelim(delimiter)
            }
            _ => {
                // backtrack a single token, so that if other trees exist, they can
                // still be properly handled.
                self.offset.set(self.offset.get() - 1);

                self.emit_error(
                    LexerErrorKind::Unclosed(delimiter),
                    ByteRange::singleton(delim_offset),
                )
            }
        }
    }

    /// Consume an identifier, at this stage keywords are also considered to be
    /// identifiers. The function expects that the first character of the
    /// identifier is consumed when the function is called.
    #[inline(always)]
    fn ident(&mut self, first: char) -> TokenKind {
        debug_assert!(is_id_start(first));

        let start = self.offset.get() - first.len_utf8();
        self.eat_while_and_discard(is_id_continue);

        let name = &self.contents.0[start..self.offset.get()];

        ident_is_keyword(name).map_or_else(|| TokenKind::Ident(name.into()), TokenKind::Keyword)
    }

    /// Function to create an integer constant from characters and
    /// a specific radix.
    fn create_int_const(&mut self, base: Base, maybe_suffix: Option<Identifier>) -> TokenKind {
        // If we have a suffix, then we immediately try and parse it as a type.

        let kind = if let Some(suffix) = maybe_suffix {
            match IntTy::try_from(suffix) {
                Ok(suffix) => IntLitKind::Suffixed(suffix),
                Err(_) => {
                    return self.emit_error(
                        LexerErrorKind::InvalidLitSuffix(NumericLitKind::Integer, suffix),
                        ByteRange::new(self.offset.get(), self.offset.get()),
                    );
                }
            }
        } else {
            IntLitKind::Unsuffixed
        };

        TokenKind::Int(base, kind)
    }

    /// Attempt to eat an identifier if the next token is one, otherwise don't
    /// do anything
    fn maybe_eat_ident(&self) -> Option<Identifier> {
        match self.peek() {
            ch if is_id_start(ch) => {
                self.skip();
                let start = self.offset.get() - ch.len_utf8();

                self.eat_while_and_discard(is_id_continue);
                let name = &self.contents.0[start..self.offset.get()];

                Some(name.into())
            }
            _ => None,
        }
    }

    /// Consume a number literal, either float or integer. The function expects
    /// that the first character of the numeric literal is consumed when the
    /// function is called.
    fn number(&mut self, prev: char, skip: bool) -> TokenKind {
        // record the start location of the literal
        let start = self.offset.get() - (skip as usize);

        // firstly, figure out if this literal has a base, if so then we need to perform
        // some magic at the end to cast it into the correct base...
        if prev == '0' {
            let maybe_radix = match self.peek() {
                'b' => Some(2),
                'o' => Some(8),
                'd' => Some(10),
                'x' => Some(16),
                _ => None,
            };

            // if this does have a radix then we need to handle the radix
            if let Some(radix) = maybe_radix {
                self.skip_ascii(); // accounting for the radix
                let chars = self.eat_decimal_digits(radix).to_string();

                // If we didn't get any characters, this means that
                if chars.is_empty() {
                    // @@Future: we want to return a `IntLit` token, and recover since this is not a
                    // fatal error...
                    return self.emit_error(
                        LexerErrorKind::MissingDigits,
                        ByteRange::new(start, self.len_consumed()),
                    );
                }

                let suffix = self.maybe_eat_ident();

                // If this specifies a radix, and then also has a suffix which denotes
                // that this literal is a `float`, then we error since we don't support
                // non-decimal float literals.
                if matches!(suffix, Some(s) if s == IDENTS.f32 || s == IDENTS.f64) && radix != 10 {
                    // @@Future: we want to return a `IntLit` token, and recover since this is not a
                    // fatal error...
                    return self.emit_error(
                        LexerErrorKind::UnsupportedFloatBaseLiteral(radix.into()),
                        ByteRange::new(start, self.len_consumed()),
                    );
                } else {
                    return self.create_int_const(radix.into(), suffix);
                }
            }
        }

        // If we didn't get a radix, then we eat all the digits that we can, and then
        // check if it is a float literal.
        self.eat_while_and_slice(move |c| c.is_ascii_digit() || c == '_');

        match self.peek() {
            // here we have to check if the next char valid char is potentially a character that
            // begins an identifier. This enables for infix calls on integer literals in
            // the form of '2.pow(...)' If we don't check this here, it leads to the
            // tokeniser being too greedy and eating the 'dot' without reason.
            // Admittedly, this is a slight ambiguity in the language syntax, but
            // there isn't currently a clear way to resolve this ambiguity.
            '.' if !is_id_start(self.peek_second()) && self.peek_second() != '.' => {
                self.skip_ascii();
                self.eat_while_and_slice(move |c| c.is_ascii_digit() || c == '_');
                self.eat_float_lit(start)
            }
            // Immediate exponent
            'e' | 'E' => self.eat_float_lit(start),
            _ => {
                let maybe_suffix = self.maybe_eat_ident();

                // If the suffix is equal to a float-like one, convert this token into
                // a `float`...
                if let Some(suffix) = maybe_suffix {
                    match FloatTy::try_from(suffix) {
                        Ok(suffix) => TokenKind::Float(FloatLitKind::Suffixed(suffix)),
                        _ => self.create_int_const(Base::Decimal, maybe_suffix),
                    }
                } else {
                    self.create_int_const(Base::Decimal, maybe_suffix)
                }
            }
        }
    }

    /// Function to apply an exponent to a floating point literal.
    fn eat_float_lit(&mut self, start: usize) -> TokenKind {
        match self.eat_exponent(start) {
            Ok(_) => {
                // Get the type ascription if any...
                let maybe_suffix = self.maybe_eat_ident();

                // Check that the suffix is correct for the literal
                let kind = if let Some(suffix) = maybe_suffix {
                    match FloatTy::try_from(suffix) {
                        Ok(suffix) => FloatLitKind::Suffixed(suffix),
                        Err(_) => {
                            return self.emit_error(
                                LexerErrorKind::InvalidLitSuffix(NumericLitKind::Float, suffix),
                                ByteRange::new(start, self.len_consumed()),
                            );
                        }
                    }
                } else {
                    FloatLitKind::Unsuffixed
                };

                TokenKind::Float(kind)
            }
            Err(err) => {
                self.add_error(err);
                TokenKind::Err
            }
        }
    }

    /// Consume an exponent for a float literal.
    fn eat_exponent(&mut self, start: usize) -> LexerResult<()> {
        if !matches!(self.peek(), 'e' | 'E') {
            return Ok(());
        }

        self.skip_ascii(); // consume the exponent

        // Check if there is a sign before the digits start in the exponent...
        if self.peek() == '-' {
            self.skip_ascii();
        };

        // Check that there is at least on digit in the exponent
        if self.peek() == EOF_CHAR {
            return self.error(
                LexerErrorKind::MissingExponentDigits,
                ByteRange::new(start, self.len_consumed()),
            );
        }

        if self.eat_decimal_digits(10).parse::<i32>().is_err() {
            self.error(
                LexerErrorKind::InvalidFloatExponent,
                ByteRange::new(start, self.len_consumed()),
            )
        } else {
            Ok(())
        }
    }

    /// Consume only decimal digits up to encountering a non-decimal digit
    /// whilst taking into account that the language supports '_' as digit
    /// separators which should just be skipped over...
    fn eat_decimal_digits(&self, radix: u32) -> &str {
        self.eat_while_and_slice(move |c| c.is_digit(radix) || c == '_')
    }

    /// Transform an ordinary character into a well known escape sequence
    /// specified by the escape literal rules. More information about the
    /// escape sequences can be found at [escape sequences](https://hash-org.github.io/lang/basics/intro.html).
    fn escaped_char(&mut self, byte_lit: bool) -> LexerResult<char> {
        let c = self.next().unwrap();

        // we need to compute the old byte offset by accounting for both the 'u'
        // character and the '\\' character, but since this is known to be 2
        // bytes, we can just subtract it from the current offset
        let start = self.offset.get() - 1;
        match c {
            '0' => Ok('\0'),
            'n' => Ok('\n'),
            't' => Ok('\t'),
            'u' => {
                // The next character should be a '{', otherwise this isn't a correct escaped
                // literal
                if self.peek() != '{' {
                    return self.error(
                        LexerErrorKind::MalformedUnicodeLit,
                        ByteRange::new(start, self.len_consumed()),
                    );
                }

                self.skip_ascii(); // Eat the '{' beginning part of the scape sequence

                // here we expect up to 6 hex digits, which is finally closed by a '}'
                let chars = self.eat_while_and_slice(|c| c != '\'' && c != '\"' && c != '}');

                if self.peek() != '}' {
                    return self.error(
                        LexerErrorKind::UnclosedUnicodeLit,
                        ByteRange::new(self.offset.get(), self.offset.get()),
                    );
                }
                self.skip_ascii(); // Eat the '}' ending part of the scape sequence

                // Check that all of the provided digits are valid.
                for (index, char) in chars.chars().enumerate() {
                    if !char.is_ascii_hexdigit() {
                        return self.error(
                            LexerErrorKind::InvalidUnicodeEscape(char),
                            ByteRange::singleton(start + 2 + index),
                        );
                    }
                }

                if chars.len() > 6 {
                    return self.error(
                        LexerErrorKind::UnicodeLitTooLong,
                        ByteRange::new(start, self.len_consumed()),
                    );
                }

                match u32::from_str_radix(chars, 16) {
                    Ok(value) => {
                        // If we are in a byte literal, we emit an error saying
                        // that unicode chars aren't allowed in byte literals.
                        if byte_lit {
                            return self.error(
                                LexerErrorKind::UnicodeEscapeInByteLit,
                                ByteRange::new(start, self.len_consumed()),
                            );
                        }

                        // If the value is larger than the maximum unicode code point, then we error
                        // since this is an invalid unicode code point.
                        if value > 0x10FFFF {
                            return self.error(
                                LexerErrorKind::UnicodeLitTooLarge,
                                ByteRange::new(start, self.len_consumed()),
                            );
                        }

                        Ok(char::from_u32(value).unwrap())
                    }
                    // We handle the error above... so this parsing should never fail!
                    Err(_) => unreachable!(),
                }
            }
            'x' => {
                // Examples of the \x.. Escape sequence would be things like `\x07` or `\x0b`,
                // Essentially 2 hex_ascii_digits and the rest is not part of
                // the escape sequence and can be left alone.
                let chars: Result<String, LexerError> = (0..2)
                    .map(|_| match self.peek() {
                        c if c.is_ascii_hexdigit() => Ok(self.next().unwrap()),
                        EOF_CHAR | '"' | '\'' => self.error(
                            LexerErrorKind::NumericEscapeSequenceTooShort,
                            ByteRange::new(start, self.len_consumed()),
                        ),
                        c => self.error(
                            LexerErrorKind::InvalidNumericEscapeSequence(c),
                            ByteRange::singleton(self.offset.get()),
                        ),
                    })
                    .collect();

                // ##Safety: Safe to unwrap since we check that both chars are hex valid and two
                // hex chars will always to fit into a u32
                let value = u32::from_str_radix(chars?.as_str(), 16).unwrap();

                // If we aren't parsing a byte literal, then we
                // can ignore the restriction of the maximum ASCII
                // code point.
                if !byte_lit && value > 0x7F {
                    return self.error(
                        LexerErrorKind::NumericEscapeSequenceTooLarge,
                        ByteRange::new(start, self.len_consumed()),
                    );
                }

                Ok(char::from_u32(value).unwrap())
            }
            'a' => Ok('\x07'),
            'b' => Ok('\x08'),
            'f' => Ok('\x1b'),
            'r' => Ok('\r'),
            'v' => Ok('\x0b'),
            '\\' => Ok('\\'),
            '"' => Ok('\"'),
            '\'' => Ok('\''),
            ch => {
                self.error(LexerErrorKind::UnknownEscapeSequence(ch), ByteRange::new(start, start))
            }
        }
    }

    /// Parse a byte literal, this is essentially the same as a char literal
    /// but we disallow unicode escapes, and don't restrict hex escape codes
    /// to be within the ASCII range.
    fn byte_literal(&mut self) -> TokenKind {
        // We parse a `char` but we know that it is a byte literal, so we
        // need to check that the value is within the range of a byte.
        let lit = self.char(/* byte_lit: */ true);

        if let TokenKind::Char(ch) = lit { TokenKind::Byte(ch as u8) } else { lit }
    }

    /// Consume a char literal provided that the current previous token is a
    /// single quote, this will produce a [TokenKind::CharLit] provided
    /// that the literal is correctly formed and is ended before the end of
    /// file is reached. This function expects the the callee has previously
    /// eaten the starting single quote.
    fn char(&mut self, byte_lit: bool) -> TokenKind {
        // Subtract one to capture the previous quote, since we know it's one byte in
        // size
        let start = self.offset.get() - (1 + byte_lit as usize);

        // Slow path, we have an escaped character.
        if self.peek() == '\\' {
            self.skip_ascii(); // eat the backslash

            match self.escaped_char(byte_lit) {
                Ok(ch) => {
                    let next = self.peek();

                    // eat the single quote after the character
                    if next != '\'' {
                        return self.emit_char_lit_error(start, Some(ch), byte_lit);
                    }

                    self.skip_ascii(); // eat the ending part of the character literal `'`
                    return TokenKind::Char(ch);
                }
                Err(err) => {
                    // Add the error to the diagnostics, and then try to recover by seeing if we can
                    // get the next token to be a `'`
                    self.add_error(err);

                    if self.peek() != '\'' {
                        self.diagnostics.has_fatal_error.set(true);
                    }

                    // Recover...
                    if !self.is_eof() {
                        self.skip();
                    }

                    return TokenKind::Err;
                }
            };
        } else if self.peek() == '\'' {
            self.skip_ascii();
            return self.emit_error(
                LexerErrorKind::EmptyCharLit,
                ByteRange::singleton(self.len_consumed()),
            );
        } else if self.peek_second() == '\'' {
            let pos = self.offset.get();
            let ch = self.next().unwrap();
            self.skip_ascii();

            // Check if the character literal is out of range of a byte.
            if byte_lit && !ch.is_ascii() {
                return self
                    .emit_error(LexerErrorKind::NonAsciiByteLit(ch), ByteRange::singleton(pos));
            }

            return TokenKind::Char(ch);
        }

        // Not a valid character, now compute the error message based on the character
        // that we encountered.
        self.emit_char_lit_error(start, None, byte_lit)
    }

    /// We emit an error for when a character literal is encountered that
    /// is not valid for a number of potential reasons. If a character literal
    /// is parsed, it begins with `'`, and then it is later followed by one
    /// of the following things:
    ///
    /// - (1) A `'` character, which means that the character literal is empty
    ///   (this is not handled here).
    ///
    /// - (2) A unicode character, then followed by a `'` character.
    ///
    /// - (3) A `\` (backslash), followed by some valid escape pattern, and
    ///   finally a closing `'` character.
    ///
    /// If after parsing the initial character (2) or escape pattern (3), then
    /// we end up here because we get an unclosed literal. This function
    /// will then attempt to recover and potentially emit a more precise
    /// error. The following errors could occur:
    ///
    /// - (1e) The next character is <EOF>, hence the character is unclosed.
    ///
    /// - (2e) The next character is non-<EOF>, and non-`'`, hence the character
    ///   is unclosed.
    ///
    ///   - In this case, we will try to eat up until the next `'` or
    ///     (whitespace or EOF) to report about the specifics of the error.
    ///
    ///   - If we stop at a non-`'` character, then we emit an error saying that
    ///     the character is unclosed.
    ///
    ///   - Otherwise, two other errors can occur:
    fn emit_char_lit_error(
        &mut self,
        pos: usize,
        starting_char: Option<char>,
        byte_lit: bool,
    ) -> TokenKind {
        // So here we know that this is an invalid character literal, to improve
        // the reporting aspect, we want to eat up until the next `'` in order
        // to highlight the entire literal
        let lit = self.eat_while_and_slice(move |c| c != '\'' && !c.is_whitespace());

        if self.peek() != '\'' {
            return self.emit_fatal_error(
                LexerErrorKind::UnclosedCharLit,
                ByteRange::singleton(self.offset.get()),
            );
        }

        // The next character is either eof or `'`, so we skip it and emit an error
        if !self.is_eof() {
            self.skip_ascii();
        }

        // Split the literal into the starting character, and the rest...
        let chars = lit.chars().collect_vec();
        let (start, rest) = match starting_char {
            Some(ref ch) => (ch, chars.as_slice()),
            None => chars.split_first().unwrap_or((&'\'', &[])),
        };

        let mut combining_marks = thin_vec![];
        let mut all_combining = true;

        // Iterate through the "rest" of the characters and check if they are combining
        // marks
        for ch in rest {
            if is_combining_mark(*ch) {
                combining_marks.push(*ch);
            } else {
                all_combining = false;
                break;
            }
        }

        // If all of the marks weren't combining we avoid reporting the
        // additional details about the combining marks...
        if !all_combining {
            combining_marks.clear();
        }

        self.emit_error(
            LexerErrorKind::MultipleCharCodePoints { start: *start, combining_marks, byte_lit },
            ByteRange::new(pos, self.len_consumed()),
        )
    }

    /// Consume a string literal provided that the current previous token is a
    /// double quote, this will produce a [TokenKind::StrLit] provided
    /// that the literal is correctly formed and is ended before the end of
    /// file is reached.
    fn string(&mut self) -> TokenKind {
        let mut value = String::from("");
        let mut closed = false;

        let start = self.offset.get();

        while let Some(c) = self.next() {
            match c {
                '"' => {
                    closed = true;
                    break;
                }
                '\\' => match self.escaped_char(false) {
                    Ok(ch) => value.push(ch),
                    Err(err) => {
                        self.add_error(err);
                        return TokenKind::Err;
                    }
                },
                ch => value.push(ch),
            }
        }

        // Report that the literal is unclosed and set the error as being fatal
        if !closed {
            return self.emit_fatal_error(
                LexerErrorKind::UnclosedStringLit,
                ByteRange::new(start, self.len_consumed()),
            );
        }

        // Avoid interning on a global level until later, we check locally if we've
        // seen the string, and then push it into our literal map if we haven't...
        value.shrink_to_fit();
        TokenKind::Str(self.strings.add(value))
    }

    /// Consume a line comment after the first following slash, essentially
    /// eating characters up to the next `\n` encountered. If we reach `EOF`
    /// before a newline, then we stop eating there.
    ///
    /// @@DocSupport: These could return a TokenKind so that we can feed it into
    /// some kind of documentation generator tool
    fn line_comment(&mut self) {
        debug_assert!(self.peek() == '/' && self.peek_second() == '/');
        self.eat_while_and_discard(|c| c != '\n')
    }

    /// Consume a block comment after the first following `/*a` sequence of
    /// characters. If the iterator encounters the start of another block
    /// comment, we increment a nested comment counter to ensure that nested
    /// block comments are accounted for and handled gracefully.
    ///
    /// @@DocSupport: These could return a TokenKind so that we can feed it into
    /// some kind of documentation generator tool
    fn block_comment(&mut self) {
        debug_assert!(self.peek() == '/' && self.peek_second() == '*');
        self.skip_ascii();

        // since we aren't as dumb as C++, we want to count the depth of block comments
        // and account for nested ones, we keep track of it whilst consuming the
        // block...
        let mut depth: u32 = 1;

        while let Some(c) = self.next() {
            match c {
                '/' if self.peek() == '*' => {
                    self.skip_ascii();
                    depth += 1;
                }
                '*' if self.peek() == '/' => {
                    self.skip_ascii();
                    depth -= 1;

                    // we finally reached the end of the block comment, if any subsequent '*/'
                    // sequences are present after this one, they will be
                    // tokenised separately
                    if depth == 0 {
                        break;
                    }
                }
                _ => (),
            }
        }
    }

    /// Eat while the condition holds, and discard any characters that it
    /// encounters whilst eating the input, this is useful because in some
    /// cases we don't want to preserve what the token represents, such as
    /// comments or white-spaces...
    fn eat_while_and_discard(&self, mut condition: impl FnMut(char) -> bool) {
        if self.is_eof() {
            return;
        }

        let slice = unsafe { self.as_slice() };
        let index = slice.find(|c| !condition(c)).unwrap_or(slice.len());
        self.offset.update(|x| x + index);
    }

    /// Eat while the condition holds, and produces a slice from where it began
    /// to eat the input and where it finished, this is sometimes beneficial
    /// as the slice doesn't have to be re-allocated as a string.
    fn eat_while_and_slice(&self, condition: impl FnMut(char) -> bool) -> &str {
        if self.is_eof() {
            return "";
        }

        // Capture the range of the slice, and then finally update the offset
        let start = self.offset.get();
        self.eat_while_and_discard(condition);
        let consumed = self.offset.get();
        let end = if consumed == start { start } else { consumed - 1 };

        self.contents.hunk(ByteRange::new(start, end))
    }
}
