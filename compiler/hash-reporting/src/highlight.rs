use std::ops::BitOr;

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

pub enum Modifier {
    Bold,
    Underline,
    Inverted,
}

impl BitOr<Modifier> for Colour {
    type Output = Decoration;

    fn bitor(self, rhs: Modifier) -> Self::Output {
        Decoration {
            colour: self,
            modifier: rhs,
        }
    }
}

impl BitOr<Colour> for Modifier {
    type Output = Decoration;

    fn bitor(self, rhs: Colour) -> Self::Output {
        Decoration {
            colour: rhs,
            modifier: self,
        }
    }
}

trait Highlighter {
    fn escape_code(&self) -> String;
}

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

pub struct Decoration {
    pub colour: Colour,
    pub modifier: Modifier,
}

impl Highlighter for Decoration {
    fn escape_code(&self) -> String {
        self.colour
            .escape_code()
            .chars()
            .chain(self.modifier.escape_code().chars())
            .collect()
    }
}

pub fn highlight(highlighter: impl Highlighter, message: &str) -> String {
    const COLOUR_ESCAPE_SIZE: usize = 7;
    const RESET: &str = "\u{001b}[0m";

    highlighter
        .escape_code()
        .chars()
        .chain(message.chars())
        .chain(RESET.chars())
        .collect()
}
