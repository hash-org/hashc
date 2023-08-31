//! Hash semantic analysis module for validating that parameters of nominal
//! definitions are all named or all un-named.

use std::fmt::Display;

use hash_ast::{ast, origin::BlockOrigin};
use hash_source::identifier::IDENTS;

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
        origin: ast::ParamOrigin,
        mut members: impl Iterator<Item = ast::AstNodeRef<'s, ast::Param>>,
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
                    AnalysisErrorKind::InconsistentFieldNaming { origin, naming_expectation },
                    member,
                ),
                _ => {}
            }
        }
    }

    pub(crate) fn check_fn_param_type_annotations(
        &mut self,
        origin: ast::ParamOrigin,
        param: ast::AstNodeRef<ast::Param>,
    ) {
        if !matches!(origin, ast::ParamOrigin::Fn) {
            return;
        }

        match self.current_block {
                // Check that `self` cannot be within a free standing functions
                BlockOrigin::Root => {
                    if let Some(name) = param.name.as_ref() && name.is(IDENTS.self_i) {
                        self.append_error(AnalysisErrorKind::SelfInFreeStandingFn, param);
                    }
                }
                BlockOrigin::Impl | BlockOrigin::Trait | BlockOrigin::Mod  => {
                    // If both the type definition is missing and the default expression assignment
                    // to the struct-def field, then a type cannot be inferred and is thus
                    // ambiguous.
                    if let Some(name) = param.name.as_ref() && !name.is(IDENTS.self_i)
                        && param.ty.is_none()
                        && param.default.is_none()
                    {
                        self.append_error(
                            AnalysisErrorKind::InsufficientTypeAnnotations { origin },
                            param,
                        );
                    }
                }
                _ => {}
            }
    }
}
