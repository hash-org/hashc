//! Utilities and functions to work with compiler metrics.

use core::fmt;
use std::time::Duration;

use derive_more::Constructor;
use hash_utils::{
    indexmap::IndexMap,
    profiling::{MetricEntry, StageMetrics},
    schemars::{self, JsonSchema},
    serde::{self, Serialize},
};

use crate::settings::CompilerStageKind;

#[derive(Serialize, Clone, JsonSchema)]
#[serde(crate = "self::serde")]
pub struct StageMetricEntry {
    /// The total metrics for the stage itself, this recorded by the driver.
    pub total: MetricEntry,

    /// Any child stage metrics that were collected by the stage itself.
    pub children: StageMetrics,
}

#[derive(Default, Serialize, Clone, JsonSchema)]
#[serde(crate = "self::serde")]
pub struct Metrics(pub IndexMap<CompilerStageKind, StageMetricEntry>);

impl Metrics {
    pub fn new() -> Self {
        Self(IndexMap::new())
    }
}

/// Utility struct to report compiler metrics.
pub struct AggregateMetricReporter<'a> {
    /// The metrics that are going to be reported.
    metrics: &'a Metrics,

    /// The longest key in the metric report, this is for formatting
    /// purposes.
    longest_metric_key: usize,
}

impl<'a> AggregateMetricReporter<'a> {
    pub fn new(metrics: &'a Metrics) -> Self {
        let longest_metric_key = metrics
            .0
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
}

impl fmt::Display for AggregateMetricReporter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // let mut stage_count = 0;
        let mut total_time = Duration::default();

        // Iterate over each stage and print out the timings.
        for (stage_kind, stage_metric) in &self.metrics.0 {
            // This shouldn't occur as we don't record this metric in this way
            if *stage_kind >= CompilerStageKind::Build {
                continue;
            }

            total_time += stage_metric.total.duration;
            writeln!(
                f,
                "{}",
                MetricReporter::new(*stage_kind, None, stage_metric.total, self.longest_metric_key)
            )?;
        }

        // Now print the total
        writeln!(
            f,
            "{: <width$}: {}",
            format!("{}", CompilerStageKind::Build),
            construct_duration_string(&total_time),
            width = self.longest_metric_key
        )
    }
}

#[derive(Constructor)]
pub struct StageMetricsReporter<'a> {
    metrics: &'a StageMetrics,
    kind: CompilerStageKind,
    longest_metric_key: usize,
}

impl fmt::Display for StageMetricsReporter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, metric) in self.metrics.iter() {
            writeln!(
                f,
                "{}",
                MetricReporter::new(self.kind, Some(name), metric, self.longest_metric_key)
            )?;
        }

        Ok(())
    }
}

#[derive(Constructor)]
pub struct MetricReporter<'a> {
    kind: CompilerStageKind,
    child_name: Option<&'a str>,
    metric: MetricEntry,
    longest_metric_key: usize,
}

impl fmt::Display for MetricReporter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { kind, child_name, metric, .. } = *self;
        let MetricEntry { duration, start_rss, end_rss } = metric;

        let name =
            if let Some(name) = child_name { format!("{kind}::{name}") } else { format!("{kind}") };

        write!(
            f,
            "{: <width$}: {}{}",
            name,
            construct_duration_string(&duration),
            construct_memory_string(start_rss, end_rss),
            width = self.longest_metric_key
        )
    }
}

/// This will convert the given [Duration] into the number of milliseconds
/// taken, and format it so that it is always 8 characters wide.
fn construct_duration_string(duration: &Duration) -> String {
    format!("{:>10.6}ms", duration.as_secs_f64() * 1_000.0)
}

fn construct_memory_string(start: Option<usize>, end: Option<usize>) -> String {
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
