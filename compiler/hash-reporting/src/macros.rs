//! Utility macros for performing various operations when it comes to
//! working with reports

/// The macro `panic_on_span` is essentially used to create a
/// [crate::report::Report], build it and then print it whilst panicking. This
/// is a useful utility to denote where a panic occurs and provide additional
/// context about where the panic occurred in regards to traversing the sources.
pub macro panic_on_span {
    ($location:expr, $sources:expr, $fmt: expr) => {
        {
            let mut report = $crate::builder::ReportBuilder::new();
            report
                .with_kind($crate::report::ReportKind::Internal)
                .with_message($fmt)
                .add_element($crate::report::ReportElement::CodeBlock($crate::report::ReportCodeBlock::new(
                    $location,
                    "here",
                )));

            eprintln!("{}", $crate::writer::ReportWriter::new(report.build(), $sources));
            std::panic::panic_any("A fatal error occurred during compilation on the reported node");
        }
    },
    ($location:expr, $sources:expr, $fmt: expr, $($arg:tt)*) => {
        panic_on_span!($location, $sources, format!($fmt, $($arg)*))
    }
}
