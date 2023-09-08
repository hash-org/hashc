//! Errors that can occur from attribute checking.

use hash_ast::ast::AstNodeId;
use hash_ast_utils::attr::AttrTarget;
use hash_reporting::reporter::Reporter;
use hash_utils::printing::SequenceDisplay;

use crate::attr::{AttrValue, REPR_OPTIONS};

/// Utility type which wraps a [Result] with an [AttrError].
pub type AttrResult<T = ()> = Result<T, AttrError>;

#[derive(Debug)]
pub enum AttrError {
    /// When the `#intrinsics` directive is being used in the
    /// non-prelude module which is disallowed.
    NonPreludeIntrinsics {
        /// The origin of the `#intrinsics` directive.
        origin: AstNodeId,
    },

    /// When multiple `repr` attributes are being applied whilst having
    /// incompatible arguments.
    IncompatibleReprArgs {
        /// The origin of the `repr` attribute.
        origin: AstNodeId,

        /// The second argument of the `repr` attribute.
        second: AstNodeId,
    },

    /// When a `repr` value is not a known or useable
    /// representation.
    UnknownReprArg {
        /// The unknown argument of the `repr` attribute.
        arg: AttrValue,
    },

    /// When the specified `repr` for an item cannot be used
    /// because it is incompatible with the item. For example,
    /// when specifying a `u8` repr for a `struct` item.
    InvalidReprForItem {
        /// The origin of the `repr` attribute.
        origin: AstNodeId,

        /// The item that the `repr` is being applied to. It will always
        /// be either a `enum` or a `struct` here.
        item: AttrTarget,

        /// The specified `repr` value.
        arg: AttrValue,
    },

    /// When `#layout_of` is being applied to a `struct` or
    /// `enum` value with a non-zero amount of generics.
    LayoutOfGenericItem {
        /// The origin of the `#layout_of` attribute.
        origin: AstNodeId,

        /// The item that the `#layout_of` is being applied to. It will always
        /// be either a `enum` or a `struct` here.
        item: AttrTarget,

        /// The node of the generics.
        generics: AstNodeId,
    },

    /// When a `ubig` or `ibig` is being used as a `repr` value.
    InvalidReprIntKind { arg: AttrValue },
}

impl AttrError {
    /// Adds the given [AttrError] to the [Reporter].
    pub fn add_to_reporter(&self, reporter: &mut Reporter) {
        match self {
            AttrError::NonPreludeIntrinsics { origin } => {
                reporter
                    .error()
                    .title("cannot use `#intrinsics` in non-prelude module")
                    .add_labelled_span(origin.span(), "this `#intrinsics` is not allowed here")
                    .add_note("only the prelude module can use `#intrinsics`");
            }
            AttrError::IncompatibleReprArgs { origin, second } => {
                reporter
                    .error()
                    .title("conflicting `repr` arguments")
                    .add_labelled_span(origin.span(), "this `repr` argument is incompatible")
                    .add_labelled_span(second.span(), "this `repr` argument is incompatible");
            }
            AttrError::UnknownReprArg { arg: value } => {
                reporter
                    .error()
                    .title(format!("unknown `repr` option `{value}`"))
                    .add_labelled_span(value.origin.span(), "this `repr` argument is unknown")
                    .add_note(format!(
                        "valid arguments are {}",
                        SequenceDisplay::either(REPR_OPTIONS)
                    ));
            }
            AttrError::InvalidReprForItem { origin, item, arg: value } => {
                reporter
                    .error()
                    .title(format!("invalid `repr` for {item}"))
                    .add_labelled_span(origin.span(), "this `repr` is not valid for this item")
                    .add_note(format!("`{value}` cannot be applied to a {item}"));
            }
            AttrError::LayoutOfGenericItem { origin, generics, item } => {
                reporter
                    .error()
                    .title(format!("cannot use `#layout_of` on {item} with generic parameters"))
                    .add_labelled_span(origin.span(), "this item is generic")
                    .add_labelled_span(generics.span(), "generic parameters declared here");
            }
            AttrError::InvalidReprIntKind { arg } => {
                reporter
                    .error()
                    .title("invalid `repr` integer kind")
                    .add_labelled_span(arg.origin.span(), "this `repr` argument is invalid")
                    .add_note("`ubig` and `ibig` cannot be used as a `repr` argument because they are unbounded integer types.");
            }
        }
    }
}

#[derive(Debug)]
pub enum AttrWarning {
    /// When an attribute is not being used because it cannot
    /// be applied to the target or is already being applied.
    /// For example, in the snippet:
    /// ```ignore
    /// #[foo, foo]
    /// bar := () => { ... }
    /// ```
    ///
    /// If `foo` is considered to be idempotent, then the second application
    /// of `foo` is redundant and will be considered un-used.
    Unused {
        /// The origin of the attribute that is un-used.
        origin: AstNodeId,

        /// The preceeding attribute that makes this attribute un-used.
        preceeding: AstNodeId,
    },
}

impl AttrWarning {
    /// Adds the given [AttrWarning] to the [Reporter].
    pub fn add_to_reporter(&self, reporter: &mut Reporter) {
        match self {
            AttrWarning::Unused { origin, preceeding } => {
                reporter
                    .warning()
                    .title("unused attribute")
                    .add_labelled_span(origin.span(), "remove this attribute")
                    .add_labelled_span(preceeding.span(), "previously specified here");
            }
        }
    }
}
