//! Hash AST semantic passes error definitions.
//!
//! All rights reserved 2022 (c) The Hash Language authors.
use hash_reporting::reporting::Report;

/// An error that can occur during the semantic pass
pub struct SemanticPassError {}

impl From<SemanticPassError> for Report {
    fn from(_: SemanticPassError) -> Self {
        todo!()
    }
}
