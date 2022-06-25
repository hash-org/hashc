//! Hash Compiler error and warning reporting module.
use std::ops::BitOr;

/// Variants of highlighter colour that can be used.
pub enum Colour {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,
}

/// Colour modifiers specifying if the colour should also
/// apply a text effect such as bold or underlined.
pub enum Modifier {
    Bold,
    Underline,
    Inverted,
}

/// Trait that enables combining colour and modifiers using the [BitOr]
/// operator.
impl BitOr<Modifier> for Colour {
    type Output = Decoration;

    fn bitor(self, rhs: Modifier) -> Self::Output {
        Decoration { colour: self, modifier: rhs }
    }
}

/// Trait that enables combining colour and modifiers using the [BitOr]
/// operator.
impl BitOr<Colour> for Modifier {
    type Output = Decoration;

    fn bitor(self, rhs: Colour) -> Self::Output {
        Decoration { colour: rhs, modifier: self }
    }
}

/// Trait that implements a single function which defines how text modifiers
/// are applied to the actual text.
pub trait Highlighter {
    fn escape_code(&self) -> String;
}

/// Highlighter trait implementation for a [Colour].
impl Highlighter for Colour {
    fn escape_code(&self) -> String {
        match self {
            Colour::Black => "\u{001b}[30;1m",
            Colour::Red => "\u{001b}[31;1m",
            Colour::Green => "\u{001b}[32;1m",
            Colour::Yellow => "\u{001b}[33;1m",
            Colour::Blue => "\u{001b}[34;1m",
            Colour::Magenta => "\u{001b}[35;1m",
            Colour::Cyan => "\u{001b}[36;1m",
            Colour::White => "\u{001b}[37;1m",
        }
        .to_owned()
    }
}

/// Highlighter trait implementation for a [Modifier].
impl Highlighter for Modifier {
    fn escape_code(&self) -> String {
        match self {
            Modifier::Bold => "\u{001b}[1m",
            Modifier::Underline => "\u{001b}[4m",
            Modifier::Inverted => "\u{001b}[7m",
        }
        .to_owned()
    }
}

/// Type that holds the union of a colour and a text modifier. This type is the
/// resultant type when combining a text colour and a modifier.
pub struct Decoration {
    /// The colour of the decoration.
    pub colour: Colour,
    /// The text modifier of the decoration.
    pub modifier: Modifier,
}

/// Implementation of the [Highlighter] trait for a Decoration. It first applies
/// the Colour modifier and then the text modifier.
impl Highlighter for Decoration {
    fn escape_code(&self) -> String {
        self.colour.escape_code().chars().chain(self.modifier.escape_code().chars()).collect()
    }
}

/// General function to apply a highlighter on a string. This will call the
/// provided [Highlighter] implementation and then apply it to the passed
/// message, resetting the effect at the end of the message.
pub fn highlight(highlighter: impl Highlighter, message: impl ToString) -> String {
    const RESET: &str = "\u{001b}[0m";

    highlighter
        .escape_code()
        .chars()
        .chain(message.to_string().chars())
        .chain(RESET.chars())
        .collect()
}
