//! Utilities and functions to work with compiler metrics.

use std::{io::Write, time::Duration};

use hash_pipeline::settings::CompilerStageKind;
use hash_utils::{
    indexmap::IndexMap,
    profiling::{MetricEntry, StageMetrics},
    stream_write, stream_writeln,
};

pub struct StageMetricEntry {
    /// The total metrics for the stage itself, this recorded by the driver.
    pub total: MetricEntry,

    /// Any child stage metrics that were collected by the stage itself.
    pub children: StageMetrics,
}

pub type Metrics = IndexMap<CompilerStageKind, StageMetricEntry>;

/// Utility struct to report compiler metrics.
pub struct MetricReporter<'a> {
    /// The metrics that are going to be reported.
    metrics: &'a Metrics,

    /// The longest key in the metric report, this is for formatting
    /// purposes.
    longest_metric_key: usize,
}

impl<'a> MetricReporter<'a> {
    pub fn new(metrics: &'a Metrics) -> Self {
        let longest_metric_key = metrics
            .iter()
            .map(|(kind, metrics)| {
                let label_size = kind.as_str().len();
                metrics
                    .children
                    .iter()
                    .map(|(item, _)| label_size + item.len() + 2)
                    .max()
                    .unwrap_or(label_size)
            })
            .max()
            .unwrap_or(0);

        Self { metrics, longest_metric_key }
    }

    pub fn report(&self, stream: &mut impl Write) {
        // let mut stage_count = 0;
        let mut total_time = Duration::default();

        // Iterate over each stage and print out the timings.
        for (stage_kind, stage_metric) in self.metrics {
            // This shouldn't occur as we don't record this metric in this way
            if *stage_kind >= CompilerStageKind::Build {
                continue;
            }

            total_time += stage_metric.total.duration;
            self.report_metric(stream, *stage_kind, None, &stage_metric.total);
            self.report_stage_metrics(stream, *stage_kind, &stage_metric.children);
        }

        // Now print the total
        stream_writeln!(
            stream,
            "{: <width$}: {}\n",
            format!("{}", CompilerStageKind::Build),
            self.construct_duration_string(&total_time),
            width = self.longest_metric_key
        );
    }

    fn report_stage_metrics(
        &self,
        stream: &mut impl Write,
        kind: CompilerStageKind,
        metrics: &StageMetrics,
    ) {
        for (name, metric) in metrics.iter() {
            self.report_metric(stream, kind, Some(name), &metric)
        }
    }

    fn report_metric(
        &self,
        stream: &mut impl Write,
        kind: CompilerStageKind,
        child_name: Option<&str>,
        entry: &MetricEntry,
    ) {
        let MetricEntry { duration, start_rss, end_rss } = entry;

        let name =
            if let Some(name) = child_name { format!("{kind}::{name}") } else { format!("{kind}") };

        stream_write!(
            stream,
            "{: <width$}: {}",
            name,
            self.construct_duration_string(duration),
            width = self.longest_metric_key
        );

        stream_writeln!(stream, "{}", self.construct_memory_string(*start_rss, *end_rss));
    }

    /// This will conver the given [Duration] into the number of milliseconds
    /// taken, and format it so that it is always 8 characters wide.
    fn construct_duration_string(&self, duration: &Duration) -> String {
        format!("{:>10.6}ms", duration.as_secs_f64() * 1_000.0)
    }

    fn construct_memory_string(&self, start: Option<usize>, end: Option<usize>) -> String {
        let rss_to_mb = |rss| (rss as f64 / 1_000_000.0).round() as usize;
        let rss_change_to_mb = |rss| (rss as f64 / 1_000_000.0).round() as i128;

        match (start, end) {
            (Some(start_rss), Some(end_rss)) => {
                let change_rss = end_rss as i128 - start_rss as i128;

                format!(
                    "; rss: {:>4}MB -> {:>4}MB ({:>+5}MB)",
                    rss_to_mb(start_rss),
                    rss_to_mb(end_rss),
                    rss_change_to_mb(change_rss),
                )
            }
            (Some(start_rss), None) => {
                format!("; rss start: {:>4}MB", rss_to_mb(start_rss))
            }
            (None, Some(end_rss)) => format!("; rss end: {:>4}MB", rss_to_mb(end_rss)),
            (None, None) => String::new(),
        }
    }
}
