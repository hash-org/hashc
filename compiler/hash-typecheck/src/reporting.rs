//! Contains utilities to convert a [crate::error::TcError] into a
//! [hash_reporting::report::Report].
use crate::{
    error::TcError,
    storage::{AccessToStorage, StorageRef},
};
use hash_reporting::{builder::ReportBuilder, report::Report};

/// A [TcError] with attached typechecker storage.
pub struct TcErrorWithStorage<'gs, 'ls, 'cd> {
    pub error: TcError,
    pub storage: StorageRef<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for TcErrorWithStorage<'gs, 'ls, 'cd> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> From<TcErrorWithStorage<'gs, 'ls, 'cd>> for Vec<Report> {
    fn from(err: TcErrorWithStorage<'gs, 'ls, 'cd>) -> Self {
        // @@Todo: actually implement this:
        vec![ReportBuilder::new()
            .with_message(format!("{:?}", err.error))
            .build()]
    }
}
