//! Helper structs for keeping track of state during AST traversal.
use std::{
    cell::{Cell, RefCell},
    ops::{Deref, DerefMut},
};

/// Helper struct for keeping track of light state during AST traversal.
///
/// Light state is state which is small in size and can be copied cheaply.
/// Internally uses a [`Cell`] to store the state.
pub struct LightState<T: Copy> {
    current: Cell<T>,
}

impl<T: Copy> LightState<T> {
    pub fn new(initial: T) -> Self {
        Self { current: Cell::new(initial) }
    }

    /// Run a function with a new value for the state, and then restore the old
    /// value on exit.
    pub fn enter<U>(&self, new_value: T, f: impl FnOnce() -> U) -> U {
        let old_value = self.get();
        self.set(new_value);
        let result = f();
        self.set(old_value);
        result
    }

    /// Get the current value of the state.
    pub fn get(&self) -> T {
        self.current.get()
    }

    /// Set the value of the state.
    pub fn set(&self, value: T) {
        self.current.set(value)
    }

    /// Get a reference to the internal [`Cell`].
    pub fn as_cell(&self) -> &Cell<T> {
        &self.current
    }
}

impl<T: Default + Copy> Default for LightState<T> {
    fn default() -> Self {
        Self { current: Default::default() }
    }
}

impl<T: Default + Copy> LightState<T> {
    /// Take the current value of the state, and replace it with the default
    /// value.
    pub fn take(&self) -> T {
        self.current.take()
    }
}

/// Helper struct for keeping track of heavy state during AST traversal.
///
/// Heavy state is state which is large in size and cannot be copied cheaply.
/// Internally uses a [`RefCell`] to store the state.
pub struct HeavyState<T: Clone> {
    current: RefCell<T>,
}

impl<T: Clone> HeavyState<T> {
    pub fn new(initial: T) -> Self {
        Self { current: RefCell::new(initial) }
    }

    /// Run a function to modify the state, then run the given callback with the
    /// new value, and then restore the old value on exit.
    pub fn enter<U>(&self, modify_value: impl FnOnce(&mut T), f: impl FnOnce() -> U) -> U {
        let old_value = self.current.to_owned().into_inner();
        modify_value(&mut self.current.borrow_mut());
        let result = f();
        *self.current.borrow_mut() = old_value;
        result
    }

    /// Get a reference to the current value of the state.
    pub fn get(&self) -> impl Deref<Target = T> + '_ {
        self.current.borrow()
    }

    /// Get a mutable reference to the current value of the state.
    pub fn get_mut(&self) -> impl Deref<Target = T> + DerefMut + '_ {
        self.current.borrow_mut()
    }

    /// Get a reference to the internal [`RefCell`].
    pub fn as_ref_cell(&self) -> &RefCell<T> {
        &self.current
    }
}
