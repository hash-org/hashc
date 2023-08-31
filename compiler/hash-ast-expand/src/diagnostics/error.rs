//! Definitions of the various kinds of errors that can occur during the
//! expansion phase of the compiler.
use hash_ast::ast::AstNodeId;
use hash_attrs::{
    attr::{AttrArgIdx, AttrValueKind},
    builtin::ATTR_MAP,
    diagnostics::AttrError,
    target::AttrTarget,
};
use hash_reporting::{
    hash_error_codes::error_codes::HashErrorCode,
    reporter::{Reporter, Reports},
};
use hash_source::identifier::Identifier;
use hash_tir::{tys::TyId, utils::params::ParamError};
use hash_utils::derive_more::Constructor;

#[derive(Constructor, Debug)]
pub struct ExpansionError {
    /// The kind of error that occurred.
    pub kind: ExpansionErrorKind,

    /// The node that caused the error.
    pub id: AstNodeId,
}

#[derive(Debug)]
pub enum ExpansionErrorKind {
    /// The applied attribute does not exist.
    UnknownAttribute { name: Identifier },

    /// When multiple invocations of the same attribute occur
    /// on the same node, hence creating a conflict.
    DuplicateAttributes { name: Identifier, first: AstNodeId },

    /// When a directive is expecting a particular expression, but received an
    /// unexpected kind...
    InvalidAttributeParams(ParamError),

    /// When an attribute is applied onto an invalid subject.
    InvalidAttributeSubject {
        /// The name of the attribute that was applied.
        name: Identifier,

        /// The [AttrTarget] of the subject that the attribute
        /// was applied onto...
        target: AttrTarget,
    },

    /// When the type of an attribute argument is not the same as the type
    /// that the parameter expects.
    InvalidAttributeArgTy {
        /// The name of the attribute that was applied.
        name: Identifier,

        /// The target of the parameter that invalid.
        target: AttrArgIdx,

        /// The value of the argument that was supplied.
        value: AttrValueKind,

        /// The type of the parameter that was expected.
        ty: TyId,
    },

    /// A more general error that can occur from specific restrictions on
    /// attributes being applied, this is generated specific attribute checks.
    InvalidAttributeApplication(AttrError),

    /// When an argument to an attribute is a non-literal, non string, integer,
    /// character or float value. This is only a temporary restriction until
    /// macros are fully implemented, and the specification is determined.
    InvalidAttributeArg(AttrTarget),
}

impl From<ExpansionError> for Reports {
    fn from(err: ExpansionError) -> Self {
        let mut reporter = Reporter::new();
        let subject = err.id.span();

        match err.kind {
            ExpansionErrorKind::UnknownAttribute { name } => {
                reporter
                    .error()
                    .title(format!("could not resolve macro `{name}`"))
                    .add_labelled_span(
                        subject,
                        format!("`{name}` is not a built-in attribute macro"),
                    );
            }
            ExpansionErrorKind::DuplicateAttributes { name, first } => {
                reporter
                    .error()
                    .title(format!("duplicate application of attribute `{name}`"))
                    .add_labelled_span(
                        first.span(),
                        format!("attribute `{name}` was already applied here"),
                    )
                    .add_labelled_span(subject, "duplicate application here");
            }
            ExpansionErrorKind::InvalidAttributeParams(error) => {
                error.add_to_reporter(&mut reporter);
            }
            ExpansionErrorKind::InvalidAttributeSubject { name, target } => {
                // Get the attribute so we know the valid subject kind
                let attr = ATTR_MAP.get_by_name(name).unwrap();

                reporter
                    .error()
                    .title(format!("attribute `{name}` cannot be applied to an {target}"))
                    .add_labelled_span(subject, format!("`{name}` cannot be applied to {target}"))
                    .add_help(format!("`{name}` can only be applied to {}", attr.subject));
            }
            ExpansionErrorKind::InvalidAttributeApplication(error) => {
                error.add_to_reporter(&mut reporter);
            }
            ExpansionErrorKind::InvalidAttributeArg(target) => {
                reporter
                    .error()
                    .title("invalid attribute argument")
                    .add_labelled_span(
                        subject,
                        format!("this {target} is not allowed to be used as an attribute argument"),
                    )
                    .add_note(
                        "attribute arguments must be integer, float, char, or string literals",
                    );
            }
            ExpansionErrorKind::InvalidAttributeArgTy { name, target, value, ty } => {
                let received = match value {
                    AttrValueKind::Str(_) => "str",
                    AttrValueKind::Int(_) => "i32",
                    AttrValueKind::Float(_) => "f64",
                    AttrValueKind::Char(_) => "char",
                };

                reporter.error().code(HashErrorCode::TypeMismatch)
                .title("invalid attribute argument")
                .add_labelled_span(subject, format!("attribute `{name}` parameter `{target}` expects `{ty}`, but got `{received}`"));
            }
        }

        reporter.into_reports()
    }
}
