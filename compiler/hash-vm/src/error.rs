use hash_reporting::reporting::{Report, ReportKind};

pub enum RuntimeError {}

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
