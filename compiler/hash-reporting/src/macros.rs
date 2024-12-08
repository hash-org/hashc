//! Utility macros for performing various operations when it comes to
//! working with reports
use hash_source::{location::Span, ModuleId, ModuleKind};
#[allow(unused_imports)]
use hash_utils::stream_less_ewriteln;

use crate::reporter::Reporter;

/// The macro `panic_on_span` is essentially used to create a
/// [crate::report::Report], build it and then print it whilst panicking. This
/// is a useful utility to denote where a panic occurs and provide additional
/// context about where the panic occurred in regards to traversing the sources.
pub macro panic_on_span {
    ($location:expr, $fmt: expr) => {
        {

            let mut reporter = $crate::reporter::Reporter::new();
            reporter.internal()
                .title($fmt)
                .add_labelled_span($location, "here");

            stream_less_ewriteln!("{}", reporter);
            std::panic::panic_any("A fatal error occurred during compilation on the reported node");
        }
    },
    ($location:expr, $fmt: expr, $($arg:tt)*) => {
        panic_on_span!($location, format!($fmt, $($arg)*))
    }
}

/// A guard on when to print a particular message using `note_on_span`
/// and `panic_on_span` family functions.
#[derive(Clone, Copy)]
pub enum SpanGuard {
    /// No guard, we're always printing for any given module.
    Always,

    /// Guarded by a specific module.
    Module(ModuleId),

    /// Non-prelude print, we'll only print something when
    /// we're in a non-prelude context.
    NonPrelude,

    /// Only print on the specified entry point of the given
    /// workspace, handy for when debugging simple things.
    EntryPoint,
}

/// This macro will produce a [crate::report::Report] and then print it to the
/// standard output, this does not panic, it is intended as a debugging utility
/// to quickly print the `span` of something and the `message` associated with
/// it.
#[track_caller]
pub fn guarded_note_on_span(location: impl Into<Span>, message: impl ToString, guard: SpanGuard) {
    let span: Span = location.into();

    let should_execute = match (guard, span.id) {
        (SpanGuard::Always, _) => true,
        (SpanGuard::Module(id), span) if span.is_module() => id == ModuleId::from(span),
        (SpanGuard::NonPrelude, span) => !span.is_prelude(),
        (SpanGuard::EntryPoint, span) => matches!(span.module_kind(), Some(ModuleKind::EntryPoint)),
        _ => false,
    };

    // Don't report if the span guard isn't met.
    if !should_execute {
        return;
    }

    let mut reporter = Reporter::new();
    reporter
        .info()
        .title(message)
        .add_labelled_span(span, "here")
        .add_note(format!("invoked at {}", ::core::panic::Location::caller()));

    stream_less_ewriteln!("{}", reporter);
}

/// This macro will produce a [crate::report::Report] and then print it to the
/// standard output, this does not panic, it is intended as a debugging utility
/// for use when debugging the compiler.
///
/// ```rust
/// // Don't print on `prelude` module.
/// note_on_span(item.span(), "compiling `item`");
///
/// // Always print.
/// note_on_span(item.span(), "compiling `item`");
/// ```
///
/// If you want to only print in certain conditions, i.e. only the entry point,
/// then you can use [guarded_note_on_span] instead.
pub fn note_on_span(location: impl Into<Span>, message: impl ToString) {
    guarded_note_on_span(location, message, SpanGuard::Always);
}

/// A macro which doesn't invoke the printing of a given format expression when
/// the current source is a prelude module. This is useful for when something is
/// difficult to isolate whilst compiler debugging and you want to skip prelude
/// printing.
///
/// @@Future: expand it to potentially only printing on a specific module or
/// span range?
pub macro non_prelude_print {
    ($location:expr, $fmt: expr) => {
        {
            // If the user specifies that they do not want to print the prelude
            if !$location.id.is_prelude() {
                stream_less_ewriteln!("{}", $fmt);
            }
        }
    },
    ($location:expr, $fmt: expr, $($arg:tt)*) => {
        span_guarded_print!($location, format!($fmt, $($arg)*))
    }
}
