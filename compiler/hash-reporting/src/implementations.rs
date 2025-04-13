//! Various implementations to convert errors into reports that
//! cannot be defined in the originating crate due to dependency
//! cycles.
//!
//! Additionally, this provides some boilerplate implementations of
//! converting various error kinds into the equivalent [Report]
//! representations.

use std::{convert::Infallible, io};

use hash_target::data_layout::TargetDataLayoutParseError;

use crate::report::{Report, ReportKind};

/// Some basic conversions into reports
impl From<io::Error> for Report {
    fn from(err: io::Error) -> Self {
        let mut report = Report::new();

        // @@ErrorReporting: we might want to show a bit more info here.
        report.kind(ReportKind::Error).title(err.to_string());
        report
    }
}

impl From<Infallible> for Report {
    fn from(err: Infallible) -> Self {
        match err {}
    }
}

impl From<TargetDataLayoutParseError<'_>> for Report {
    fn from(value: TargetDataLayoutParseError) -> Self {
        let mut report = Report::new();

        let message = match value {
            TargetDataLayoutParseError::Malformed { dl } => {
                format!("malformed \"data-layout\" string: `{dl}`")
            }
            TargetDataLayoutParseError::InvalidAddressSpace { addr_space, err } => {
                format!("invalid address space `{addr_space}` in \"data-layout\", cause: {err}")
            }
            TargetDataLayoutParseError::InvalidAlignment { cause } => {
                format!("invalid alignment for `{cause}` in \"data-layout\"")
            }
            TargetDataLayoutParseError::MissingAlignment { cause } => {
                format!("missing alignment for `{cause}` in \"data-layout\"")
            }
            TargetDataLayoutParseError::InvalidBits { kind, bit, cause, err } => {
                format!("invalid {kind} `{bit}` for `{cause}` in \"data-layout\", err: {err}")
            }
            TargetDataLayoutParseError::InconsistentTargetArchitecture { dl, target } => {
                format!(
                    "inconsistent target specification: \"data-layout\" claims architecture is {dl}-endian, while \"target-endian\" is `{target}`"
                )
            }
            TargetDataLayoutParseError::InconsistentTargetPointerWidth { size, target } => {
                format!(
                    "inconsistent target specification: \"data-layout\" claims pointer size is `{size}` bits, while \"target-pointer-width\" is `{target}`"
                )
            }
            TargetDataLayoutParseError::InvalidEnumSize { err } => err,
        };

        report.kind(ReportKind::Error).title(message);
        report
    }
}
