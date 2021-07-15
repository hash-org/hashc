//! Hash compiler low level implementation for the language lexer. Convert
//! an arbitrary string into a sequence of Lexemes.
//!
//! All rights reserved 2021 (c) The Hash Language authors
use hash_ast::ast::AstString;
use hash_ast::ident::IDENTIFIER_MAP;
use hash_ast::location::Location;

use crate::idents::*;
use crate::token::Token;
use crate::token::TokenKind;
use std::str::Chars;

/// Representing the end of stream, or the initial character that is set as 'prev' in
/// a [Lexer] since there is no character before the start.
const EOF_CHAR: char = '\0';

pub(crate) struct Lexer<'a> {
    /// The size of the input stream, since it is unrealiable to check the size of the
    /// stream via the iterator, we record the initial size at creation.
    length: usize,

    /// Location of the lexer in the current stream.
    offset: usize,

    /// The iterator of characters that represents the input stream
    contents: Chars<'a>,

    /// The previous character of the current stream, this is useful for keeping track
    /// of state when tokenising compound inputs that rely on previous context.
    prev: char,
}

impl<'a> Lexer<'a> {
    /// Create a new [Lexer] from the given string input.
    pub(crate) fn new(input: &'a str) -> Self {
        Lexer {
            length: input.len(),
            offset: 0,
            contents: input.chars(),
            prev: EOF_CHAR,
        }
    }

    /// Returns a `Chars` iterator over the remaining characters.
    fn chars(&self) -> Chars<'a> {
        self.contents.clone()
    }

    /// Returns amount of already consumed symbols.
    pub(crate) fn len_consumed(&self) -> usize {
        self.length - self.offset
    }

    /// Peeks the next symbol from the input stream without consuming it.
    pub(crate) fn peek(&self) -> char {
        self.nth_char(0)
    }

    /// Peeks the second symbol from the input stream without consuming it.
    pub(crate) fn peek_second(&self) -> char {
        self.nth_char(1)
    }

    /// Returns nth character relative to the current position.
    /// If requested position doesn't exist, `EOF_CHAR` is returned.
    /// However, getting `EOF_CHAR` doesn't always mean actual end of file,
    /// it should be checked with `is_eof` method.
    fn nth_char(&self, n: usize) -> char {
        self.chars().nth(n).unwrap_or(EOF_CHAR)
    }

    /// Moves to the next character.
    pub(crate) fn next(&mut self) -> Option<char> {
        let c = self.contents.next()?;

        // only increment the offset by one if there is a next character
        self.prev = c;
        self.offset += 1;
        Some(c)
    }

    /// Checks if there is nothing more to consume.
    pub(crate) fn is_eof(&self) -> bool {
        self.contents.as_str().is_empty()
    }

    /// Parses a token from the input string.
    pub(crate) fn advance_token(&mut self) -> Option<Token> {
        let token_kind = loop {
            let next_char = self.next();

            // well if the next char is None, does that mean we hit EOF prematurely?
            if matches!(next_char, None) {
                return None;
            }

            match next_char.unwrap() {
                // Slash, comment or block comment.
                '/' => match self.peek() {
                    '/' => self.line_comment(),
                    '*' => self.block_comment(),
                    _ => break TokenKind::Slash,
                },

                // Whitespace sequence.
                c if c.is_whitespace() => self.eat_while_and_discard(char::is_whitespace),

                // One-symbol tokens.
                ';' => break TokenKind::Semi,
                ',' => break TokenKind::Comma,
                '.' => break TokenKind::Dot,
                '(' => break TokenKind::OpenParen,
                ')' => break TokenKind::CloseParen,
                '{' => break TokenKind::OpenBrace,
                '}' => break TokenKind::CloseBrace,
                '[' => break TokenKind::OpenBracket,
                ']' => break TokenKind::CloseBracket,
                '~' => break TokenKind::Tilde,
                ':' => break TokenKind::Colon,
                '=' => break TokenKind::Eq,
                '!' => break TokenKind::Exclamation,
                '<' => break TokenKind::Lt,
                '>' => break TokenKind::Gt,
                '-' => break TokenKind::Minus,
                '&' => break TokenKind::And,
                '|' => break TokenKind::Pipe,
                '+' => break TokenKind::Plus,
                '*' => break TokenKind::Star,
                '^' => break TokenKind::Caret,
                '%' => break TokenKind::Percent,

                // Identifier (this should be checked after other variant that can
                // start as identifier).
                c if is_id_start(c) => break self.ident(),

                // Numeric literal.
                '0'..='9' => break self.number(),
                // character literal.
                '\'' => break self.char(),

                // String literal.
                '"' => break self.string(),

                _ => break TokenKind::Unexpected,
            }
        };

        let location = Location::span(self.offset, self.len_consumed());
        Some(Token::new(token_kind, location))
    }

    /// Consume an identifier, at this stage keywords are also considered to be identfiers
    pub(crate) fn ident(&mut self) -> TokenKind {
        debug_assert!(is_id_start(self.prev));

        let first = self.prev;
        let suffix = self.eat_while(is_id_continue);
        let name = format!("{}{}", first, suffix);

        // create the identifier here from the created map
        let ident = IDENTIFIER_MAP.create_ident(AstString::Owned(name.as_str().to_owned()));
        TokenKind::Ident(ident)
    }

    pub(crate) fn number(&mut self) -> TokenKind {
        debug_assert!('0' <= self.prev && self.prev <= '9');

        // firstly, figure out if this literal has a base, if so then we need to perform
        // some magic at the end to cast it into the correct base...
        if self.prev == '0' {
            match self.peek() {
                'b' => {
                    todo!()
                }
                'o' => {
                    todo!()
                }
                'x' => {
                    todo!()
                }
                // Number literal without a prefix!
                '0'..='9' | '_' | '.' | 'e' | 'E' => {
                    todo!()
                }
                _ => TokenKind::IntLiteral(0),
            }
        } else {
            let num = self.eat_decimal_digits().parse::<u64>().unwrap();
            TokenKind::IntLiteral(num)
        }
    }

    // TODO: support floats here?
    pub(crate) fn eat_decimal_digits(&mut self) -> String {
        let mut digits = String::from(self.prev);

        loop {
            match self.peek() {
                '_' => {
                    self.next();
                }
                c @ '0'..='9' => {
                    self.next();
                    digits.push(c);
                }
                _ => break,
            }
        }
        digits
    }

    fn char_from_escape_seq(&mut self) -> Option<char> {
        debug_assert!(self.prev == '\\');

        // @@Incomplete: come up with a better algorithm to transform escaped literals, rather than manual
        // transformations!
        let c = self.next().unwrap();
        match c {
            'n' => Some('\n'),
            't' => Some('\t'),
            'u' => panic!("Unicode escape sequences not supported yet!"),
            'a' => Some('\x07'),
            'b' => Some('\x08'),
            'f' => Some('\x1b'),
            'r' => Some('\r'),
            'v' => Some('\x0b'),
            '\\' => Some('\\'),
            '"' => Some('"'),
            '\'' => Some('\''),
            _ => None,
        }
    }

    pub(crate) fn char(&mut self) -> TokenKind {
        debug_assert!(self.prev == '\'');

        // check whether the next character is a backslash, as in escaping a char, if not
        // eat the next char and expect the second character to be a "\'" char...
        if self.peek_second() == '\'' {
            if self.peek() != '\\' {
                let c = self.next().unwrap();
                return TokenKind::ChatLiteral(c);
            }

            // otherwise, this is an escaped char and hence we eat the '\' and use the next char as
            // the actual char by escaping it
            self.next();

            // @@BadPanic: Don't panic here, just error, char_from_escape_seq should return a Result<char, ParseError>
            //             so that we can print it and give additional details about why the error occured.
            let ch = self
                .char_from_escape_seq()
                .unwrap_or_else(|| panic!("Unsuported escape sequence!"));
            return TokenKind::ChatLiteral(ch);
        }

        TokenKind::Unexpected
    }

    pub(crate) fn string(&mut self) -> TokenKind {
        debug_assert!(self.prev == '"');

        let mut value = String::from("");

        while let Some(c) = self.next() {
            match c {
                '"' => break,
                '\\' => {
                    // @@BadPanic: Don't panic here, just error, char_from_escape_seq should return a Result<char, ParseError>
                    //             so that we can print it and give additional details about why the error occured.
                    let ch = self
                        .char_from_escape_seq()
                        .unwrap_or_else(|| panic!("Unsuported escape sequence!"));

                    value.push(ch);
                }
                ch => value.push(ch),
            }
        }

        TokenKind::StrLiteral(value)
    }

    /// Consume a line comment after the first folloing slash, essentially eating
    /// characters up to the next '\n' encountered. If we reach EOF before a newline, then
    /// we stop eating there.
    //@@DocSupport: These could return a TokenKind so that we can feed it into some kind of documentation generator tool
    pub(crate) fn line_comment(&mut self) {
        debug_assert!(self.prev == '/' && self.peek() == '/');
        self.next();
        self.eat_while_and_discard(|c| c != '\n');
    }

    /// Consume a block comment after the first following '/*' sequence of characters. If the
    /// iterator encounters the start of another block comment, we increment a nested comment
    /// counter to ensure that nested block comments are accounted for and handeled gracefully.
    //@@DocSupport: These could return a TokenKind so that we can feed it into some kind of documentation generator tool
    pub(crate) fn block_comment(&mut self) {
        debug_assert!(self.prev == '/' && self.peek() == '*');
        self.next();

        // since we aren't as dumb as C++, we want to count the depth of block comments
        // and account for nested ones, we keep track of it whilst consuming the block...
        let mut depth: u32 = 1;

        while let Some(c) = self.next() {
            match c {
                '/' if self.peek() == '*' => {
                    self.next();
                    depth += 1;
                }
                '*' if self.peek() == '/' => {
                    self.next();
                    depth -= 1;

                    // we finally reached the end of the block comment, if any subsequent '*/' sequences
                    // are present after this one, they will be tokenised seperately
                    if depth == 0 {
                        break;
                    }
                }
                _ => (),
            }
        }
    }

    fn eat_while_and_discard(&mut self, mut condition: impl FnMut(char) -> bool) {
        while condition(self.peek()) && !self.is_eof() {
            self.next();
        }
    }

    fn eat_while(&mut self, mut condition: impl FnMut(char) -> bool) -> String {
        let mut collector = String::new();

        while condition(self.peek()) && !self.is_eof() {
            collector.push(self.next().unwrap());
        }

        collector
    }
}

pub fn tokenise(input: &str) -> impl Iterator<Item = Token> + '_ {
    let mut lexer = Lexer::new(input);

    std::iter::from_fn(move || {
        if input.is_empty() {
            return None;
        }

        lexer.advance_token()
    })
}
