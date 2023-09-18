//! Timing/profiling utilities.

use std::{
    cell::RefCell,
    time::{Duration, Instant},
};

use indexmap::IndexMap;
use log::{log_enabled, Level};

/// A [StageMetrics] is a collection of timings for each section of a stage.
#[derive(Default, Debug, Clone)]
pub struct StageMetrics {
    /// The collected timings for each section of the stage.
    pub timings: IndexMap<&'static str, Duration>,
}

impl StageMetrics {
    /// Merge another set of metrics into this one.
    pub fn merge(&mut self, other: &StageMetrics) {
        for (name, time) in &other.timings {
            self.timings.entry(name).and_modify(|e| *e += *time).or_insert(*time);
        }
    }

    /// Create an iterator over the collected timings.
    pub fn iter(&self) -> impl Iterator<Item = (&'static str, Duration)> + '_ {
        self.timings.iter().map(|(item, time)| (*item, *time))
    }
}

/// A trait that can be implemented by a compiler stage in order to
/// store information about the [Duration] of some process within
/// the stage, later reporting it if requested.
pub trait HasMutMetrics {
    fn metrics(&mut self) -> &mut StageMetrics;

    /// Add a metric to the stage.
    fn add_metric(&mut self, name: &'static str, time: Duration) {
        self.metrics().timings.entry(name).and_modify(|e| *e += time).or_insert(time);
    }

    /// Time an item and add the metric to the stage.
    fn time_item<T>(&mut self, name: &'static str, f: impl FnOnce(&mut Self) -> T) -> T {
        let mut time = Duration::default();
        let value = timed(
            || f(self),
            Level::Info,
            |duration| {
                time = duration;
            },
        );

        self.add_metric(name, time);
        value
    }
}

/// Execute the given closure while timing it, and pass the duration to the
/// second closure.
#[inline(always)]
pub fn timed<T>(op: impl FnOnce() -> T, level: log::Level, on_elapsed: impl FnOnce(Duration)) -> T {
    if log_enabled!(level) {
        let begin = Instant::now();
        let result = op();
        on_elapsed(begin.elapsed());
        result
    } else {
        op()
    }
}

impl HasMutMetrics for StageMetrics {
    fn metrics(&mut self) -> &mut StageMetrics {
        self
    }
}

/// A [StageMetrics] is a collection of timings for each section of a stage.
#[derive(Default, Debug, Clone)]
pub struct CellStageMetrics {
    /// The collected timings for each section of the stage.
    pub timings: RefCell<IndexMap<&'static str, Duration>>,
}

impl CellStageMetrics {
    /// Merge another set of metrics into this one.
    pub fn merge(&self, other: &CellStageMetrics) {
        self.timings.borrow_mut().extend(other.timings.borrow().iter())
    }
}

/// Sister trait of [HasMutMetrics] which allows for immutable access to
/// the metrics.
pub trait HasMetrics {
    fn metrics(&self) -> &CellStageMetrics;

    fn add_metric(&self, name: &'static str, time: Duration) {
        self.metrics().timings.borrow_mut().entry(name).and_modify(|e| *e += time).or_insert(time);
    }

    /// Time an the execution of item, whilst saving the result to the
    /// metrics.
    fn time_item<T>(&self, name: &'static str, f: impl FnOnce(&Self) -> T) -> T {
        let mut time = Duration::default();
        let value = timed(
            || f(self),
            Level::Info,
            |duration| {
                time = duration;
            },
        );

        self.add_metric(name, time);
        value
    }
}

impl From<CellStageMetrics> for StageMetrics {
    fn from(metrics: CellStageMetrics) -> Self {
        StageMetrics { timings: metrics.timings.into_inner() }
    }
}
