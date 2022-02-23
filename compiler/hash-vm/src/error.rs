use std::fmt;

use hash_reporting::reporting::{Report, ReportKind};

#[derive(Debug)]
pub enum StackAccessKind {
    Push,
    Pop,
}

impl fmt::Display for StackAccessKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StackAccessKind::Push => write!(f, "push"),
            StackAccessKind::Pop => write!(f, "pop"),
        }
    }
}

#[derive(Debug)]
pub enum RuntimeError {
    StackViolationAccess {
        kind: StackAccessKind,
        size: u8,
        total: usize,
    },
}

pub type RuntimeResult<T> = Result<T, RuntimeError>;

impl From<RuntimeError> for Report {
    fn from(err: RuntimeError) -> Self {
        match err {
            RuntimeError::StackViolationAccess { kind, size, total } => {
                Report {
                    kind: ReportKind::Error,
                    message: format!("Stack access violation occurred: tried to `{}` {}bytes from stack, but stack size is {}", kind, size, total ),
                    error_code: None,
                    contents: vec![],
                }
            },
        }
    }
}
