//! Utility macros for performing various operations when it comes to
//! working with reports

pub macro panic_on_span {
    ($location:expr, $sources:expr, $($arg:tt)*) => {
        let message = format_args_nl!($($arg)*);

        let mut report = $crate::builder::ReportBuilder::new();
        report
            .with_kind(ReportKind::Internal)
            .with_message(message)
            .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                err.location,
                "here",
            )));

        println!("{}", ReportWriter::new(report.build(), $sources));
    }
}
