use std::{borrow::Cow, fmt::Debug};

use hash_ast::{
    keyword::Keyword,
    operator::{CompoundFn, OperatorFn},
    resolve::ModuleResolver,
};

use crate::{gen::AstGen, token::TokenKind};

/// Struct representing an operator with a kind and a flag
/// denoting whether the operator is re-assigning the left
/// hand side expression.
#[derive(Debug, Clone)]
pub struct Operator {
    /// The kind of operator.
    pub kind: OperatorKind,
    /// Flag representing where the operator is re-assigning or not.
    pub assignable: bool,
}

#[derive(Clone)]
/// The operator kind enumeration. This represents all types of
/// operator present in the language.
pub enum OperatorKind {
    /// '=='
    EqEq,
    /// '!='
    NotEq,
    /// '|'
    BitOr,
    /// '||'
    Or,
    /// '&'
    BitAnd,
    /// '&&'
    And,
    /// '^'
    BitXor,
    /// '^^'
    Exp,
    /// '>'
    Gt,
    /// '>='
    GtEq,
    /// '<'
    Lt,
    /// '<='
    LtEq,
    /// '>>'
    Shr,
    /// '<<'
    Shl,
    /// '+'
    Add,
    /// '-'
    Sub,
    /// '*'
    Mul,
    /// '/'
    Div,
    /// '%'
    Mod,

    // @@Cleanup: This is a special operator since it performs a higher order operation compared
    //            to all other members of the Operator enum, maybe it should be in it's own enum??
    As,
}

impl Operator {
    /// This function is used to pickup 'glued' operator tokens to form more complex binary operators
    /// that might be made up of multiple tokens. The function will peek ahead (2 tokens at most since
    /// all binary operators are made of that many tokens). The function returns an optional derived
    /// operator, and the number of tokens that was consumed deriving the operator, it is the responsibility
    /// of the caller to increment the token stream by the provided number.
    pub(crate) fn from_token_stream<R: ModuleResolver>(gen: &AstGen<R>) -> (Option<Operator>, u8) {
        let token = gen.peek();

        // check if there is a token that we can peek at ahead...
        if token.is_none() {
            return (None, 0);
        }

        let (op, mut consumed): (_, u8) = match &(token.unwrap()).kind {
            // Since the 'as' keyword is also a binary operator, we have to handle it here...
            TokenKind::Keyword(Keyword::As) => (Some(OperatorKind::As), 1),
            TokenKind::Eq => match gen.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::EqEq), 2),
                _ => (None, 0),
            },
            TokenKind::Lt => match gen.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::LtEq), 2),
                Some(token) if token.kind == TokenKind::Lt => (Some(OperatorKind::Shl), 2),
                _ => (Some(OperatorKind::Lt), 1),
            },
            TokenKind::Gt => match gen.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::GtEq), 2),
                Some(token) if token.kind == TokenKind::Gt => (Some(OperatorKind::Shr), 2),
                _ => (Some(OperatorKind::Gt), 1),
            },
            TokenKind::Plus => (Some(OperatorKind::Add), 1),
            TokenKind::Minus => (Some(OperatorKind::Sub), 1),
            TokenKind::Star => (Some(OperatorKind::Mul), 1),
            TokenKind::Slash => (Some(OperatorKind::Div), 1),
            TokenKind::Percent => (Some(OperatorKind::Mod), 1),
            TokenKind::Caret => match gen.peek_second() {
                Some(token) if token.kind == TokenKind::Caret => (Some(OperatorKind::Exp), 2),
                _ => (Some(OperatorKind::BitXor), 1),
            },
            TokenKind::Amp => match gen.peek_second() {
                Some(token) if token.kind == TokenKind::Amp => (Some(OperatorKind::And), 2),
                _ => (Some(OperatorKind::BitAnd), 1),
            },
            TokenKind::Pipe => match gen.peek_second() {
                Some(token) if token.kind == TokenKind::Pipe => (Some(OperatorKind::Or), 2),
                _ => (Some(OperatorKind::BitOr), 1),
            },
            TokenKind::Exclamation => match gen.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::NotEq), 2),
                _ => (None, 0), // this is a unary operator '!'
            },
            _ => (None, 0),
        };

        match op {
            // check if the operator is re-assignable and if so try to parse a equality operator.
            // If we see this one then we can parse and then just convert the operator into the
            // 'Eq' version.
            Some(kind) => {
                let assignable = match gen.peek_nth(consumed as usize) {
                    Some(token) if kind.is_re_assignable() && token.has_kind(TokenKind::Eq) => {
                        consumed += 1;
                        true
                    }
                    _ => false,
                };

                (Some(Operator { kind, assignable }), consumed)
            }
            None => (None, 0),
        }
    }
}

/// This implementation will be used for printing code from tokens.
impl std::fmt::Display for OperatorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OperatorKind::EqEq => write!(f, "=="),
            OperatorKind::NotEq => write!(f, "!="),
            OperatorKind::BitOr => write!(f, "|"),
            OperatorKind::Or => write!(f, "||"),
            OperatorKind::BitAnd => write!(f, "&"),
            OperatorKind::And => write!(f, "&&"),
            OperatorKind::BitXor => write!(f, "^"),
            OperatorKind::Exp => write!(f, "^^"),
            OperatorKind::Gt => write!(f, ">"),
            OperatorKind::GtEq => write!(f, ">="),
            OperatorKind::Lt => write!(f, "<"),
            OperatorKind::LtEq => write!(f, "<="),
            OperatorKind::Shr => write!(f, "<<"),
            OperatorKind::Shl => write!(f, ">>"),
            OperatorKind::Add => write!(f, "+"),
            OperatorKind::Sub => write!(f, "-"),
            OperatorKind::Mul => write!(f, "*"),
            OperatorKind::Div => write!(f, "/"),
            OperatorKind::Mod => write!(f, "%"),
            OperatorKind::As => write!(f, "as"),
        }
    }
}

/// This implementation will be used for error messages. The debug formatter is
/// mainly used in error reports whereas the display formatter is used when
/// printing code from tokens.
impl std::fmt::Debug for OperatorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OperatorKind::EqEq => write!(f, "eq"),
            OperatorKind::NotEq => write!(f, "neq"),
            OperatorKind::BitOr => write!(f, "bit_or"),
            OperatorKind::Or => write!(f, "orl"),
            OperatorKind::BitAnd => write!(f, "bit_and"),
            OperatorKind::And => write!(f, "and"),
            OperatorKind::BitXor => write!(f, "bit_xor"),
            OperatorKind::Exp => write!(f, "exp"),
            OperatorKind::Gt => write!(f, "gt"),
            OperatorKind::GtEq => write!(f, "gt_eq"),
            OperatorKind::Lt => write!(f, "lt"),
            OperatorKind::LtEq => write!(f, "lt_eq"),
            OperatorKind::Shr => write!(f, "shr"),
            OperatorKind::Shl => write!(f, "shl"),
            OperatorKind::Add => write!(f, "add"),
            OperatorKind::Sub => write!(f, "sub"),
            OperatorKind::Mul => write!(f, "mul"),
            OperatorKind::Div => write!(f, "div"),
            OperatorKind::Mod => write!(f, "mod"),
            OperatorKind::As => write!(f, "as"),
        }
    }
}

impl OperatorKind {
    /// This returns if an operator is actually re-assignable. By re-assignable, this is in the sense
    /// that you can add a '=' to mean that you are performing a re-assigning operation using the left
    /// hand-side expression as a starting point and the rhs as the other argument to the operator.
    /// For example, `a += b` is re-assigning because it means `a = a + b`.
    pub(crate) fn is_re_assignable(&self) -> bool {
        matches!(
            self,
            OperatorKind::BitOr
                | OperatorKind::Or
                | OperatorKind::BitAnd
                | OperatorKind::And
                | OperatorKind::BitXor
                | OperatorKind::Exp
                | OperatorKind::Shr
                | OperatorKind::Shl
                | OperatorKind::Add
                | OperatorKind::Sub
                | OperatorKind::Mul
                | OperatorKind::Div
                | OperatorKind::Mod
        )
    }

    /// Compute the precedence for an operator
    pub(crate) fn infix_binding_power(&self) -> (u8, u8) {
        match self {
            OperatorKind::Or => (2, 3),
            OperatorKind::And => (4, 5),
            OperatorKind::EqEq | OperatorKind::NotEq => (6, 5),
            OperatorKind::Gt | OperatorKind::GtEq | OperatorKind::Lt | OperatorKind::LtEq => (7, 8),
            OperatorKind::BitOr | OperatorKind::BitXor => (9, 10),
            OperatorKind::BitAnd => (11, 12),
            OperatorKind::Shr | OperatorKind::Shl => (13, 14),
            OperatorKind::Add | OperatorKind::Sub => (15, 16),
            OperatorKind::Mul | OperatorKind::Div | OperatorKind::Mod => (17, 18),
            OperatorKind::Exp => (20, 19),
            OperatorKind::As => (21, 22),
        }
    }
}

impl From<Operator> for OperatorFn {
    fn from(op: Operator) -> Self {
        let Operator { kind, assignable } = op;

        match kind {
            OperatorKind::As => panic!("Cannot convert 'as' into a function call."),
            // Lazy named functions
            OperatorKind::Or | OperatorKind::And => OperatorFn::LazyNamed {
                name: Cow::Owned(kind.to_string()),
                assigning: assignable,
            },
            // Compound functions
            OperatorKind::Gt | OperatorKind::GtEq | OperatorKind::Lt | OperatorKind::LtEq => {
                // @@Cleanup: re-map the operator kind into a CompoundFn, so we avoid typing
                // the return type 4 times...
                let compound_kind = match kind {
                    OperatorKind::Gt => CompoundFn::Gt,
                    OperatorKind::GtEq => CompoundFn::Geq,
                    OperatorKind::Lt => CompoundFn::Lt,
                    OperatorKind::LtEq => CompoundFn::Leq,
                    _ => unreachable!(),
                };

                OperatorFn::Compound {
                    name: compound_kind,
                    assigning: assignable,
                }
            }
            // Simple named functions
            k => OperatorFn::Named {
                name: Cow::Owned(k.to_string()),
                assigning: assignable,
            },
        }
    }
}
