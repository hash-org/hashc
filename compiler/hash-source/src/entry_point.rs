//! This defines all of the logic that surrounds dealing with program
//! entry points. This defines the [EntryPointState] which is used to
//! keep track of which function is the entry point of the program.

use std::fmt;

use crate::{
    identifier::{Identifier, IDENTS},
    ModuleId,
};

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
#[derive(Debug, Clone, Copy)]
pub struct EntryPointState<T: fmt::Debug + Copy> {
    /// This refers to the entry point of the program, the term points
    /// to the function definition within the entry point module.
    ///
    /// @@NewTc: this could just be switched out to an `FnDefId`
    pub def: Option<T>,

    /// Which kind of entry point was declared in the module.
    pub kind: Option<EntryPointKind>,

    /// This stores the [SourceId] of the module that is the entry
    /// point. If the session is interactive, this is set as [`None`]
    /// since there is no function entry point.
    pub module: Option<ModuleId>,
}

impl<T: fmt::Debug + Copy> EntryPointState<T> {
    /// Create a new [EntryPointState].
    pub fn new(entry_point: Option<ModuleId>) -> Self {
        Self { def: None, kind: None, module: entry_point }
    }

    /// Get the module entry point if there exists one.
    pub fn module(&self) -> Option<ModuleId> {
        self.module
    }

    /// Get the name of the entry point, if there is one. This function
    /// will return [`None`] if there is no present entry point.
    pub fn name(&self) -> Option<Identifier> {
        match self.kind {
            Some(EntryPointKind::Main) => Some(IDENTS.main),
            Some(EntryPointKind::Named(name)) => Some(name),
            None => None,
        }
    }

    /// Convert the [EntryPointState] into a [`EntryPointState<U>`] by providing
    /// a conversion function to map with.
    pub fn map_into<U>(self, f: impl FnOnce(T) -> U) -> EntryPointState<U>
    where
        U: fmt::Debug + Copy,
    {
        EntryPointState { def: self.def.map(f), kind: self.kind, module: self.module }
    }

    /// Specify the entry point of the program. This function will return
    /// an error if there is already an entry point defined.
    pub fn set(&mut self, def: T, kind: EntryPointKind) -> Option<()> {
        // We disallow multiple entry points, and expect the caller
        // to deal with the duplication problem.
        if self.def.is_some() {
            return None;
        }

        self.def = Some(def);
        self.kind = Some(kind);

        Some(())
    }
}
