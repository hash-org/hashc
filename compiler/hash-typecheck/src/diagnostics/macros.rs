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
/// The `storage` argument to the macro is used to access the storage in order
/// to resolve the [hash_source::SourceMap] and
/// [hash_types::storage::GlobalStorage] so that the term location can be
/// fetched.
pub macro tc_panic {
    ($term: expr, $storage:expr, $fmt: expr) => {
        {
            use crate::storage::AccessToStorage;
            use hash_types::fmt::PrepareForFormatting;
            use hash_reporting::{report, builder, writer};

            let storages = $storage.storages();

            // get the sources and and the location from the term
            let term_location = storages.location_store().get_location($term);
            let sources = storages.source_map();

            // format the message and build the report
            let mut report = builder::ReportBuilder::new();
            report
                .with_kind(report::ReportKind::Internal)
                .with_message("The compiler encountered a fatal error")
                .add_element(report::ReportElement::Note(report::ReportNote::new(
                    report::ReportNoteKind::Info,
                    format!("whilst performing operations on the term `{}`", $term.for_formatting(storages.global_storage()))
                )));

            if let Some(location) = term_location {
                report
                    .add_element(report::ReportElement::CodeBlock(report::ReportCodeBlock::new(
                        location,
                        "",
                    )));
            }

            // Add the `info` note about why the internal panic occurred
            report.add_element(report::ReportElement::Note(report::ReportNote::new(
                report::ReportNoteKind::Info,
                $fmt
            )));

            eprintln!("{}", writer::ReportWriter::new(report.build(), sources));
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
    ([$($terms:expr),*  $(,)?], $storage:expr, $fmt: expr) => {
        {
            use crate::storage::AccessToStorage;
            use hash_types::fmt::PrepareForFormatting;
            use hash_reporting::{report, builder, writer};

            let storages = $storage.storages();
            let sources = storages.source_map();

            let terms_formatted = [
                $(
                    format!("`{}`", ($terms).for_formatting(storages.global_storage())),
                )*
            ];
            let terms = terms_formatted.join(", ");

            // build the report
            let mut report = builder::ReportBuilder::new();
            report
                .with_kind(report::ReportKind::Internal)
                .with_message("The compiler encountered a fatal error")
                .add_element(report::ReportElement::Note(
                    report::ReportNote::new(
                        report::ReportNoteKind::Info,
                        format!("whilst performing operations on the terms: {}", terms),
                    ),
                ));

            // Add all of the locations from the terms that we're provided by the macro
            let mut index = 0;
            $(
                #[allow(unused_assignments)]
                {
                    let term_location = storages.location_store().get_location($terms);
                    if let Some(location) = term_location {
                        report.add_element(report::ReportElement::CodeBlock(
                            report::ReportCodeBlock::new(
                                location,
                                format!("{} member here", index),
                            ),
                        ));
                    }

                    index += 1;
                }
            )*

            // Add the `info` note about why the internal panic occurred
            report.add_element(report::ReportElement::Note(
                report::ReportNote::new(
                    report::ReportNoteKind::Info,
                    $fmt,
                ),
            ));

            eprintln!("{}", writer::ReportWriter::new(report.build(), sources));
            std::panic::panic_any(TC_FATAL_ERROR_MESSAGE);
        }
    },
    ([$($terms:expr),*  $(,)?], $storage:expr, $fmt: expr, $($arg:tt)*) => {
        tc_panic_on_many!([$($terms,)*], $storage, format!($fmt, $($arg)*))
    },
    ($terms:expr, $storage:expr, $fmt: expr) => {
        {
            use crate::storage::AccessToStorage;
            use hash_types::fmt::PrepareForFormatting;
            use hash_reporting::{report, builder, writer};

            let storages = $storage.storages();
            let sources = storages.source_map();

            let terms = $terms
                .iter()
                .map(|term| format!("`{}`", term.for_formatting(storages.global_storage())))
                .collect::<Vec<_>>()
                .join(", ");

            // build the report
            let mut report = builder::ReportBuilder::new();
            report
                .with_kind(report::ReportKind::Internal)
                .with_message("The compiler encountered a fatal error")
                .add_element(report::ReportElement::Note(
                    report::ReportNote::new(
                        report::ReportNoteKind::Info,
                        format!("whilst performing operations on the terms: {}", terms),
                    ),
                ));

            // Add all of the locations from the terms that we're provided by the macro
            for (index, term) in $terms.iter().enumerate() {
                let term_location = storages.location_store().get_location(term);

                if let Some(location) = term_location {
                    report.add_element(report::ReportElement::CodeBlock(
                        report::ReportCodeBlock::new(
                            location,
                            format!("{} member here", index),
                        ),
                    ));
                }
            }

            // Add the `info` note about why the internal panic occurred
            report.add_element(report::ReportElement::Note(
                report::ReportNote::new(
                    report::ReportNoteKind::Info,
                    $fmt,
                ),
            ));

            eprintln!("{}", writer::ReportWriter::new(report.build(), sources));
            std::panic::panic_any(TC_FATAL_ERROR_MESSAGE);
        }
    },
    ($terms:expr, $storage:expr, $fmt: expr, $($arg:tt)*) => {
        tc_panic_on_many!($terms, $storage, format!($fmt, $($arg)*))
    },
}
