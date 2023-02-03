//! Defines all of the errors that can occur during the
//! orchestration of the of compiler code generation backend,
//! whether there is no defined entry point, or the settings
//! applied to the backend don't match, etc.

use hash_reporting::reporter::{Reporter, Reports};

pub(crate) enum BackendError {
    /// If an entry point was expected, but none was found, this error
    /// will be returned.
    MissingEntryPoint,
}

impl From<BackendError> for Reports {
    fn from(value: BackendError) -> Self {
        match value {
            BackendError::MissingEntryPoint => {
                let mut builder = Reporter::new();
                builder.error().title("no entry point specified").add_note(
                    "when building an executable, an entry point must be specified in the source.\nThis can be done by using the `main` keyword, or by using the `#entry_point` directive."
                );

                builder.into_reports()
            }
        }
    }
}
