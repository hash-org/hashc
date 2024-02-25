//! Timing/profiling utilities.

use std::{
    cell::{Cell, RefCell},
    cmp,
    ops::{Add, AddAssign},
    time::{Duration, Instant},
};

use derive_more::Constructor;
use indexmap::IndexMap;
use log::{log_enabled, Level};

#[derive(Debug, Clone, Copy, Constructor)]
pub struct MetricEntry {
    /// The time taken for the operation to complete.
    pub duration: Duration,

    /// The starting resident set size of the process.
    pub start_rss: Option<usize>,

    /// The ending resident set size of the process at the end of the operation.
    pub end_rss: Option<usize>,
}

impl MetricEntry {
    pub fn timed(duration: Duration) -> Self {
        Self { duration, start_rss: get_resident_set_size(), end_rss: None }
    }
}

impl Default for MetricEntry {
    fn default() -> Self {
        Self { duration: Default::default(), start_rss: get_resident_set_size(), end_rss: None }
    }
}

impl Add for MetricEntry {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            duration: self.duration + rhs.duration,
            start_rss: self.start_rss,
            end_rss: self.end_rss.map_or(rhs.end_rss, |value| {
                Some(cmp::max(value, rhs.end_rss.unwrap_or_default()))
            }),
        }
    }
}

impl AddAssign for MetricEntry {
    fn add_assign(&mut self, rhs: Self) {
        self.duration += rhs.duration;

        if let Some(value) = self.end_rss.as_mut() {
            *value = cmp::max(*value, rhs.end_rss.unwrap_or_default());
        } else {
            self.end_rss = rhs.end_rss;
        }
    }
}

/// A [StageMetrics] is a collection of timings for each section of a stage.
#[derive(Default, Debug, Clone)]
pub struct StageMetrics {
    /// The collected timings for each section of the stage.
    pub metrics: IndexMap<&'static str, MetricEntry>,

    /// Whether to report RSS statisics. This option is useful to
    /// silence stages that are paralelised or out of order meaning that
    /// measuring RSS at various stages of the compiler pipeline produces
    /// useless results in the sense that stage is capturing memory usage
    /// which it hasn't directly caused. In this case, we don't want to emit
    /// RSS metrics for these stages.
    pub report_rss: bool,
}

impl StageMetrics {
    /// Merge another set of metrics into this one.
    pub fn merge(&mut self, other: &StageMetrics) {
        for (name, time) in &other.metrics {
            self.metrics.entry(name).and_modify(|e| *e += *time).or_insert(*time);
        }

        self.report_rss &= other.report_rss;
    }

    /// Create an iterator over the collected timings.
    pub fn iter(&self) -> impl Iterator<Item = (&'static str, MetricEntry)> + '_ {
        self.metrics.iter().map(|(item, time)| (*item, *time))
    }
}

/// A trait that can be implemented by a compiler stage in order to
/// store information about the [Duration] of some process within
/// the stage, later reporting it if requested.
pub trait HasMutMetrics {
    fn metrics(&mut self) -> &mut StageMetrics;

    /// Add a metric to the stage.
    fn add_metric(&mut self, name: &'static str, item: MetricEntry) {
        self.metrics().metrics.entry(name).and_modify(|e| *e += item).or_insert(item);
    }

    /// Time an item and add the metric to the stage.
    fn record<T>(&mut self, name: &'static str, f: impl FnOnce(&mut Self) -> T) -> T {
        let mut record = MetricEntry::default();

        let value = timed(
            || f(self),
            Level::Info,
            |duration| {
                record.duration = duration;
                record.end_rss = get_resident_set_size();
            },
        );

        self.add_metric(name, record);
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
    pub timings: RefCell<IndexMap<&'static str, MetricEntry>>,

    pub report_rss: Cell<bool>,
}

impl CellStageMetrics {
    /// Merge another set of metrics into this one.
    pub fn merge(&self, other: &CellStageMetrics) {
        self.timings.borrow_mut().extend(other.timings.borrow().iter());
        self.report_rss.update(|value| value & other.report_rss.get());
    }
}

/// Sister trait of [HasMutMetrics] which allows for immutable access to
/// the metrics.
pub trait HasMetrics {
    fn metrics(&self) -> &CellStageMetrics;

    fn add_metric(&self, name: &'static str, item: MetricEntry) {
        self.metrics().timings.borrow_mut().entry(name).and_modify(|e| *e += item).or_insert(item);
    }

    /// Time an the execution of item, whilst saving the result to the
    /// metrics.
    fn record<T>(&self, name: &'static str, f: impl FnOnce(&Self) -> T) -> T {
        let mut record = MetricEntry::default();

        let value = timed(
            || f(self),
            Level::Info,
            |duration| {
                record.duration = duration;
                record.end_rss = get_resident_set_size();
            },
        );

        self.add_metric(name, record);
        value
    }
}

impl From<CellStageMetrics> for StageMetrics {
    fn from(metrics: CellStageMetrics) -> Self {
        StageMetrics { metrics: metrics.timings.into_inner(), report_rss: metrics.report_rss.get() }
    }
}

cfg_match! {
    cfg(windows) => {
        pub fn get_resident_set_size() -> Option<usize> {
            use std::mem;

            use windows::{
                // FIXME: change back to K32GetProcessMemoryInfo when windows crate
                // updated to 0.49.0+ to drop dependency on psapi.dll
                Win32::System::ProcessStatus::{GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS},
                Win32::System::Threading::GetCurrentProcess,
            };

            let mut pmc = PROCESS_MEMORY_COUNTERS::default();
            let pmc_size = mem::size_of_val(&pmc);
            unsafe {
                GetProcessMemoryInfo(
                    GetCurrentProcess(),
                    &mut pmc,
                    pmc_size as u32,
                )
            }
            .ok()
            .ok()?;

            Some(pmc.WorkingSetSize)
        }
    }
    cfg(target_os = "macos")  => {
        pub fn get_resident_set_size() -> Option<usize> {
            use libc::{c_int, c_void, getpid, proc_pidinfo, proc_taskinfo, PROC_PIDTASKINFO};
            use std::mem;
            const PROC_TASKINFO_SIZE: c_int = mem::size_of::<proc_taskinfo>() as c_int;

            unsafe {
                let mut info: proc_taskinfo = mem::zeroed();
                let info_ptr = &mut info as *mut proc_taskinfo as *mut c_void;
                let pid = getpid() as c_int;
                let ret = proc_pidinfo(pid, PROC_PIDTASKINFO, 0, info_ptr, PROC_TASKINFO_SIZE);
                if ret == PROC_TASKINFO_SIZE {
                    Some(info.pti_resident_size as usize)
                } else {
                    None
                }
            }
        }
    }
    cfg(unix) => {
        pub fn get_resident_set_size() -> Option<usize> {
            let field = 1;
            let contents = fs::read("/proc/self/statm").ok()?;
            let contents = String::from_utf8(contents).ok()?;
            let s = contents.split_whitespace().nth(field)?;
            let npages = s.parse::<usize>().ok()?;
            Some(npages * 4096)
        }
    }
    _ => {
        pub fn get_resident_set_size() -> Option<usize> {
            None
        }
    }
}
