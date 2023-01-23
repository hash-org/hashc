//! Utility macros for performing various operations when it comes to
//! working with reports

const TC_FATAL_ERROR_MESSAGE: &str =
    "A fatal error occurred during typechecking on the reported node";

/// The macro `tc_panic` is essentially used to create a
/// [hash_reporting::report::Report], build it and then print it whilst
/// panicking. This is a useful utility to denote where a panic occurs and
/// provide additional context about where the panic occurred in regards to
/// traversing the sources.
///
/// The `storage` argument to the macro is used to access the environment so it
/// must be a type that implements [`AccessToEnv`].
pub macro tc_panic {
    ($term: expr, $storage:expr, $fmt: expr) => {
        {
            use hash_reporting::{report, builder, writer};
            use hash_utils::stream_less_ewriteln;

            let env = $storage.env();

            // get the sources and and the location from the term
            let term_location = env.stores().location().get_location($term);
            let sources = env.source_map();

            // format the message and build the report
            let mut reporter = reporter::Reporter::new();
            let report = reporter.internal();
            report
                .title("The compiler encountered a fatal error")
                .add_info(format!("whilst performing operations on the term `{}`", env.with($term)));

            if let Some(location) = term_location {
                report.add_span(location);
            }

            // Add the `info` note about why the internal panic occurred
            report.add_info($fmt);

            stream_less_ewriteln!("{}", writer::ReportWriter::new(reporter.into_reports(), sources));
            std::panic::panic_any(TC_FATAL_ERROR_MESSAGE);
        }
    },
    ($term: expr, $storage:expr, $fmt: expr, $($arg:tt)*) => {
        tc_panic!($term, $storage, format!($fmt, $($arg)*))
    },
}

/// The macro `tc_panic_on_many` is essentially used to create a
/// [hash_reporting::report::Report], build it and then print it whilst
/// panicking. This macro differs from `tc_panic` because it accepts the `expr`
/// and treats it as an iterable. For each term, a code block element is added
/// to the built report.
pub macro tc_panic_on_many {
    ($terms:expr, $storage:expr, $fmt: expr) => {
        {
            use hash_reporting::{reporter, writer};
            use hash_utils::stream_less_ewriteln;

            let env = $storage.env();

            // get the sources and and the location from the term
            let sources = env.source_map();

            let terms = $terms
                .iter()
                .map(|term| format!("`{}`", env.with(*term)))
                .collect::<Vec<_>>()
                .join(", ");

            // build the report
            let mut reporter = reporter::Reporter::new();
            let report = reporter.internal();
            report
                .title("The compiler encountered a fatal error")
                .add_info(format!("whilst performing operations on the terms: {}", terms));

            // Add all of the locations from the terms that we're provided by the macro
            for (index, term) in $terms.iter().enumerate() {
                let term_location = env.stores().location().get_location(term);

                if let Some(location) = term_location {
                        report.add_labelled_span(location, format!("{} member here", index));
                }
            }

            // Add the `info` note about why the internal panic occurred
            report.add_info($fmt);


            stream_less_ewriteln!("{}", writer::ReportWriter::new(reporter.into_reports(), sources));
            std::panic::panic_any(TC_FATAL_ERROR_MESSAGE);
        }
    },
    ($terms:expr, $storage:expr, $fmt: expr, $($arg:tt)*) => {
        tc_panic_on_many!($terms, $storage, format!($fmt, $($arg)*))
    },
}
