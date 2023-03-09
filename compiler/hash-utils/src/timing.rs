//! Timing/profiling utilities.

use std::time::{Duration, Instant};

use log::{log_enabled, Level};

/// A trait that can be implemented by a compiler stage in order to
/// store information about the [Duration] of some process within
/// the stage, later reporting it if requested.
pub trait AccessToMetrics {
    fn add_metric(&mut self, name: &'static str, time: Duration);
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

/// Run a stage of the backend whilst also timing it.
pub fn time_item<U: AccessToMetrics, T>(
    this: &mut U,
    stage: &'static str,
    f: impl FnOnce(&mut U) -> T,
) -> T {
    let mut time = Duration::default();
    let value = timed(
        || f(this),
        Level::Info,
        |duration| {
            time = duration;
        },
    );

    this.add_metric(stage, time);
    value
}
