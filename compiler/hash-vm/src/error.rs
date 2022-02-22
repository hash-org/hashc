use hash_reporting::reporting::{Report, ReportKind};


pub enum StackAccessKind {
    Push,
    Pop
}

pub enum RuntimeError {
    StackViolationAccess {
        kind: StackAccessKind,
        size: u8,
        total: usize
    }
}

pub type RuntimeResult<T> = Result<T, RuntimeError>;

impl From<RuntimeError> for Report {
    fn from(_: RuntimeError) -> Self {
        Report {
            kind: ReportKind::Error,
            message: "Failed to execute".to_string(),
            error_code: None,
            contents: vec![],
        }
    }
}
