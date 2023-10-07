//! Utility macros for performing various operations when it comes to
//! working with reports
#[allow(unused_imports)]
use hash_utils::stream_less_ewriteln;

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

/// This macro will produce a [crate::report::Report] and then print it to the
/// standard output, this does not panic, it is intended as a debugging utility
/// to quickly print the `span` of something and the `message` associated with
/// it.
pub macro note_on_span {
    ($(@no_prelude: $no_prelude:expr,)? $location:expr, $fmt: expr) => {
        {
            let mut print_it = true;

            // If the user specifies that they do not want to print the prelude
            $(
                if $no_prelude && $location.id.is_prelude() {
                    print_it = false;
               }
            )?

            if print_it {
                use hash_utils::stream_less_ewriteln;

                let mut reporter = $crate::reporter::Reporter::new();
                reporter.info()
                    .title($fmt)
                    .add_labelled_span($location, "here");

                stream_less_ewriteln!("{}", reporter);
            }
        }
    },
    ($(@no_prelude: $no_prelude:expr,)? $location:expr, $fmt: expr, $($arg:tt)*) => {
        note_on_span!($(@no_prelude $no_prelude,)? location, format!($fmt, $($arg)*))
    }
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
