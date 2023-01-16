//! Utility macros for performing various operations when it comes to
//! working with reports

/// The macro `panic_on_span` is essentially used to create a
/// [crate::report::Report], build it and then print it whilst panicking. This
/// is a useful utility to denote where a panic occurs and provide additional
/// context about where the panic occurred in regards to traversing the sources.
pub macro panic_on_span {
    ($location:expr, $sources:expr, $fmt: expr) => {
        {
            let mut reporter = $crate::reporter::Reporter::new();
            reporter.internal()
                .title($fmt)
                .add_labelled_span($location, "here");

            eprintln!("{}", $crate::writer::ReportWriter::new(reporter.into_reports(), $sources));
            std::panic::panic_any("A fatal error occurred during compilation on the reported node");
        }
    },
    ($location:expr, $sources:expr, $fmt: expr, $($arg:tt)*) => {
        panic_on_span!($location, $sources, format!($fmt, $($arg)*))
    }
}

/// This macro will produce a [crate::report::Report] and then print it to the
/// standard output, this does not panic, it is intended as a debugging utility
/// to quickly print the `span` of something and the `message` associated with
/// it.
pub macro compiler_note {
    ($location:expr, $sources:expr, $fmt: expr) => {
        {
            let mut reporter = $crate::reporter::Reporter::new();
            reporter.info()
                .title($fmt)
                .add_labelled_span($location, "here");

            eprintln!("{}", $crate::writer::ReportWriter::new(reporter.into_reports(), $sources));
        }
    },
    ($location:expr, $sources:expr, $fmt: expr, $($arg:tt)*) => {
        compiler_note!($location, $sources, format!($fmt, $($arg)*))
    }
}
