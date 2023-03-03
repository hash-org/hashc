//! This defines all of the logic that surrounds dealing with program
//! entry points. This defines the [EntryPointState] which is used to
//! keep track of which function is the entry point of the program.

use std::{cell::Cell, fmt};

use crate::identifier::{Identifier, IDENTS};

/// Specifies what kind of entry point was provided to the program.
#[derive(Debug, Clone, Copy)]
pub enum EntryPointKind {
    /// The entry point was declared as a function with the "main"
    /// name within the entry point module.
    Main,

    /// There exists an entry point, however it was specified through
    /// the user directive `#entry_point`.
    Named(Identifier),
}

/// The [EntryPointState] is used to keep track of the declared entry point
/// of the program, if there is one.
#[derive(Debug, Clone, Default)]
pub struct EntryPointState<T: fmt::Debug + Copy> {
    /// This refers to the entry point of the program, the term points
    /// to the function definition within the entry point module.
    ///
    /// @@NewTc: this could just be switched out to an `FnDefId`
    item: Cell<Option<(T, EntryPointKind)>>,
}

impl<T: fmt::Debug + Copy> EntryPointState<T> {
    /// Create a new [EntryPointState].
    pub fn new() -> Self {
        Self { item: Cell::new(None) }
    }

    /// Get the name of the entry point, if there is one. This function
    /// will return [`None`] if there is no present entry point.
    pub fn name(&self) -> Option<Identifier> {
        match self.item.get() {
            Some((_, EntryPointKind::Main)) => Some(IDENTS.main),
            Some((_, EntryPointKind::Named(name))) => Some(name),
            None => None,
        }
    }

    /// Get the item that is the entry point, if there is one.
    pub fn def(&self) -> Option<T> {
        self.item.get().map(|(def, _)| def)
    }

    /// Get the [EntryPointKind] of the entry point, if there is one.
    pub fn kind(&self) -> Option<EntryPointKind> {
        self.item.get().map(|(_, kind)| kind)
    }

    pub fn has(&self) -> bool {
        self.item.get().is_some()
    }

    /// Convert the [EntryPointState] into a [`EntryPointState<U>`] by providing
    /// a conversion function to map with.
    pub fn map_into<U>(self, f: impl FnOnce(T) -> U) -> EntryPointState<U>
    where
        U: fmt::Debug + Copy,
    {
        EntryPointState { item: Cell::new(self.item.get().map(|(def, kind)| (f(def), kind))) }
    }

    /// Specify the entry point of the program. This function will return
    /// an error if there is already an entry point defined.
    pub fn set(&self, def: T, kind: EntryPointKind) -> Option<()> {
        // We disallow multiple entry points, and expect the caller
        // to deal with the duplication problem.
        if self.item.get().is_some() {
            return None;
        }

        // Set the entry point.
        self.item.set(Some((def, kind)));
        Some(())
    }
}
