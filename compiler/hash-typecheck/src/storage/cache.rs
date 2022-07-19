//! Typechecking operations cache storing results for previous simplifications,
//! unifications, and validations.

use std::{collections::HashMap, fmt::Display, hash::Hash};

use log::log_enabled;

use crate::ops::validate::TermValidation;

use super::primitives::{Sub, TermId};

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
    store: HashMap<K, V>,
    /// Number of times the cache successfully retrieved a result
    hits: usize,
    /// Number of times the cache didn't have an operation stored
    misses: usize,
}

impl<K, V> Default for CacheStore<K, V> {
    fn default() -> Self {
        Self { store: HashMap::new(), hits: Default::default(), misses: Default::default() }
    }
}

impl<K: Hash + Eq, V> CacheStore<K, V> {
    /// Create a new [Cache]
    pub(crate) fn new() -> Self {
        Self { store: HashMap::new(), hits: 0, misses: 0 }
    }

    /// Create a new [CacheStore] with an initial capacity. The capacity
    /// value is used for each inner operation store.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self { store: HashMap::with_capacity(capacity), hits: 0, misses: 0 }
    }
    /// Get a value within the [CacheStore] whilst also recording whether
    /// the value was within the cache or not.

    pub(crate) fn get(&mut self, key: K) -> Option<&V> {
        let value = self.store.get(&key);

        // We don't want to record cache metrics if we're not in debug
        if log_enabled!(log::Level::Debug) {
            if value.is_some() {
                self.hits += 1;
            } else {
                self.misses += 1;
            }
        }

        value
    }

    /// Get the inner store of the [CacheStore]
    pub fn store(&self) -> &HashMap<K, V> {
        &self.store
    }

    /// Put a value into the [CacheStore]
    pub(crate) fn put(&mut self, key: K, value: V) {
        self.store.insert(key, value);
    }

    /// Create [CacheMetrics] from the [CacheStore]
    pub(crate) fn metrics(&self) -> CacheMetrics {
        CacheMetrics { hits: self.hits, misses: self.misses, size: self.store.len() }
    }

    /// Clear the [CacheStore] metrics on hits/misses
    pub fn reset_metrics(&mut self) {
        self.misses = 0;
        self.hits = 0;
    }

    /// Clear the [CacheStore] and store metrics
    pub fn clear(&mut self) {
        self.store.clear();
        self.reset_metrics();
    }
}

#[derive(Debug, Default)]
pub struct Cache {
    /// Inner store for the results from term simplifications.
    pub(crate) simplification_store: CacheStore<TermId, TermId>,
    /// Inner store for the results from term simplifications.
    pub(crate) validation_store: CacheStore<TermId, TermValidation>,
    /// Inner store for the results from term unifications.
    pub(crate) unification_store: CacheStore<(TermId, TermId), Sub>,
}

impl Cache {
    /// Create a new [Cache]
    pub fn new() -> Self {
        Self {
            simplification_store: CacheStore::new(),
            validation_store: CacheStore::new(),
            unification_store: CacheStore::new(),
        }
    }

    /// Create a new [Cache] with an initial capacity. The capacity
    /// value is used for each inner operation store.
    pub fn new_with_capacity(capacity: usize) -> Self {
        Self {
            simplification_store: CacheStore::with_capacity(capacity),
            validation_store: CacheStore::with_capacity(capacity),
            unification_store: CacheStore::with_capacity(capacity),
        }
    }
}
