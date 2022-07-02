//! Utility macros for performing various operations when it comes to
//! working with reports

const TC_FATAL_ERROR_MESSAGE: &str =
    "A fatal error occurred during typechecking on the reported node";

/// The macro `tc_panic` is essentially used to create a [Report], build
/// it and then print it whilst panicking. This is a useful utility to denote
/// where a panic occurs and provide additional context about where the panic
/// occurred in regards to traversing the sources.
///
/// The `storage` argument to the macro is used to access the storage in order
/// to resolve the [SourceMap] and [GlobalStorage] so that the term location can
/// be fetched.
pub macro tc_panic {
    ($term: expr, $storage:expr, $fmt: expr, $($arg:tt)*) => {
        {
            use crate::storage::AccessToStorage;
            let storages = $storage.storages();

            // get the sources and and the location from the term
            let term_location = storages.location_store().get_location($term);
            let sources = storages.source_map();

            // format the message and build the report
            let message = format!($fmt, $($arg)*);
            let mut report = hash_reporting::builder::ReportBuilder::new();
            report
                .with_kind(hash_reporting::report::ReportKind::Internal)
                .with_message(message);

            if let Some(location) = term_location {
                builder
                    .add_element(hash_reporting::report::ReportElement::CodeBlock(hash_reporting::report::ReportCodeBlock::new(
                        location,
                        "here",
                    )));
            }

            println!("{}", hash_reporting::writer::ReportWriter::new(report.build(), sources));
            std::panic::panic_any(TC_FATAL_ERROR_MESSAGE);
        }
    },
    ($term: expr, $storage:expr, $fmt: expr) => {
        {
            use crate::storage::AccessToStorage;
            let storages = $storage.storages();

            // get the sources and and the location from the term
            let term_location = storages.location_store().get_location($term);
            let sources = storages.source_map();

            // format the message and build the report
            let mut report = hash_reporting::builder::ReportBuilder::new();
            report
                .with_kind(hash_reporting::report::ReportKind::Internal)
                .with_message($fmt);

                if let Some(location) = term_location {
                    report
                        .add_element(hash_reporting::report::ReportElement::CodeBlock(hash_reporting::report::ReportCodeBlock::new(
                            location,
                            "here",
                        )));
                }

            println!("{}", hash_reporting::writer::ReportWriter::new(report.build(), sources));
            std::panic::panic_any(TC_FATAL_ERROR_MESSAGE);
        }
    }
}

/// The macro `tc_panic_on_many` is essentially used to create a [Report], build
/// it and then print it whilst panicking. This macro differs from `tc_panic`
/// because it accepts the `expr` and treats it as an iterable. For each term, a
/// code block element is added to the built report.
pub macro tc_panic_on_many {
    ($terms: expr, $storage:expr, $fmt: expr, $($arg:tt)*) => {
        {
            use crate::storage::AccessToStorage;
            let storages = $storage.storages();
            let sources = storages.source_map();

            // Build the report
            let mut report = hash_reporting::builder::ReportBuilder::new();
            report
                .with_kind(hash_reporting::report::ReportKind::Internal)
                .with_message(format!($fmt, $($arg)*));

            // Add all of the locations from the terms that we're provided by the macro
            for (index, term) in $terms.iter().enumerate() {
                let term_location = storages.location_store().get_location(term);

                if let Some(location) = term_location {
                    report
                        .add_element(hash_reporting::report::ReportElement::CodeBlock(hash_reporting::report::ReportCodeBlock::new(
                            location,
                            format!("{} member here", index)
                        )));
                }
            }

            println!("{}", hash_reporting::writer::ReportWriter::new(report.build(), sources));
            std::panic::panic_any(TC_FATAL_ERROR_MESSAGE);
        }
    },
    ($terms:expr, $storage:expr, $fmt: expr) => {
        {
            use crate::storage::AccessToStorage;
            let storages = $storage.storages();

            let sources = storages.source_map();

            // build the report
            let mut report = hash_reporting::builder::ReportBuilder::new();
            report
                .with_kind(hash_reporting::report::ReportKind::Internal)
                .with_message($fmt);

            // Add all of the locations from the terms that we're provided by the macro
            for (index, term) in $terms.iter().enumerate() {
                let term_location = storages.location_store().get_location(term);

                if let Some(location) = term_location {
                    report
                        .add_element(hash_reporting::report::ReportElement::CodeBlock(hash_reporting::report::ReportCodeBlock::new(
                            location,
                            format!("{} member here", index)
                        )));
                }
            }

            println!("{}", hash_reporting::writer::ReportWriter::new(report.build(), sources));
            std::panic::panic_any(TC_FATAL_ERROR_MESSAGE);
        }
    }
}
