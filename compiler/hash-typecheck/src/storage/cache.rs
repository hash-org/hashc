//! Typechecking operations cache storing results for previous simplifications,
//! unifications, and validations.

use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    fmt::Display,
    hash::Hash,
};

use hash_types::{terms::TermId, Sub};
use hash_utils::store::{DefaultPartialStore, PartialStore};
use log::log_enabled;

use crate::ops::validate::TermValidation;

#[derive(Debug)]
pub struct CacheMetrics {
    /// Number of times the cache successfully retrieved a result
    pub hits: usize,
    /// Number of times the cache didn't have an operation stored
    pub misses: usize,
    /// The total size of the cache
    pub size: usize,
}

impl Display for CacheMetrics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "size={}, hits={}, misses={}, success={}%",
            self.size,
            self.hits,
            self.misses,
            (self.hits as f32) / (self.misses as f32 + self.hits as f32) * 100f32
        )
    }
}

#[derive(Debug)]
pub struct CacheStore<K, V> {
    /// The store
    store: DefaultPartialStore<K, V>,
    /// Number of times the cache successfully retrieved a result
    hits: Cell<usize>,
    /// Number of times the cache didn't have an operation stored
    misses: Cell<usize>,
}

impl<K, V> Default for CacheStore<K, V> {
    fn default() -> Self {
        Self {
            store: DefaultPartialStore::new(),
            hits: Default::default(),
            misses: Default::default(),
        }
    }
}

impl<K: Copy + Hash + Eq, V: Clone> PartialStore<K, V> for CacheStore<K, V> {
    fn internal_data(&self) -> &RefCell<HashMap<K, V>> {
        self.store.internal_data()
    }

    /// Get a value by its key, if it exists.
    fn get(&self, key: K) -> Option<V> {
        let value = self.store.get(key);
        // Override for metrics:
        // We don't want to record cache metrics if we're not in debug
        if log_enabled!(log::Level::Debug) {
            if value.is_some() {
                self.hits.set(self.hits.get() + 1);
            } else {
                self.misses.set(self.misses.get() + 1);
            }
        }
        value
    }

    /// Clear the [CacheStore] and metrics.
    fn clear(&self) {
        self.store.clear();
        self.reset_metrics();
    }
}

impl<K: Copy + Hash + Eq, V: Clone> CacheStore<K, V> {
    /// Clear the [CacheStore] metrics on hits/misses
    pub fn reset_metrics(&self) {
        self.misses.set(0);
        self.hits.set(0);
    }

    /// Create [CacheMetrics] from the [CacheStore]
    pub(crate) fn metrics(&self) -> CacheMetrics {
        CacheMetrics { hits: self.hits.get(), misses: self.misses.get(), size: self.len() }
    }
}

#[derive(Debug, Default)]
pub struct Cache {
    /// Inner store for the results from term simplifications
    pub(crate) simplification_store: CacheStore<TermId, TermId>,
    /// Inner store for the results from term simplifications
    pub(crate) validation_store: CacheStore<TermId, TermValidation>,
    /// Inner store for the results from term unifications
    pub(crate) unification_store: CacheStore<(TermId, TermId), Sub>,
    /// Inner store for the results from term inference operations
    pub(crate) inference_store: CacheStore<TermId, TermId>,
}

impl Cache {
    /// Create a new [Cache]
    pub fn new() -> Self {
        Self::default()
    }
}
