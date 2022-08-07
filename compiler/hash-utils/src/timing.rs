//! Timing/profiling utilities.

use std::time::{Duration, Instant};

use log::log_enabled;

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
