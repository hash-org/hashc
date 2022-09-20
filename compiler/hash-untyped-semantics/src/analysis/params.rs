//! Hash semantic analysis module for validating that parameters of nominal
//! definitions are all named or all un-named.

use std::fmt::Display;

use hash_ast::ast::{AstNodeRef, Param};

use super::SemanticAnalyser;
use crate::diagnostics::error::AnalysisErrorKind;

/// Represents what naming convention the analyser expected from a set of
/// fields originating from a nominal definition, i.e. a struct or a enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldNamingExpectation {
    /// The fields should all be named.
    Named,
    /// The fields should all be nameless.
    Nameless,
}

impl Display for FieldNamingExpectation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FieldNamingExpectation::Named => write!(f, "named"),
            FieldNamingExpectation::Nameless => write!(f, "un-named"),
        }
    }
}

impl SemanticAnalyser<'_> {
    /// Function to check whether the naming convention of a set of fields is
    /// consistent. Consistency is determined whether all of the fields
    /// are named or if they are all un-named.
    pub(crate) fn check_field_naming<'s>(
        &mut self,
        mut members: impl Iterator<Item = AstNodeRef<'s, Param>>,
    ) {
        let naming_expectation =
            if members.next().map(|param| param.body().name.is_some()).unwrap_or(false) {
                FieldNamingExpectation::Named
            } else {
                FieldNamingExpectation::Nameless
            };

        for member in members {
            match (member.body().name.as_ref(), naming_expectation) {
                (Some(_), FieldNamingExpectation::Nameless)
                | (None, FieldNamingExpectation::Named) => self.append_error(
                    AnalysisErrorKind::InconsistentFieldNaming {
                        origin: member.origin,
                        naming_expectation,
                    },
                    member,
                ),
                _ => {}
            }
        }
    }
}
