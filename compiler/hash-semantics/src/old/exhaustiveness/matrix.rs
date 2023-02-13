//! This file contains definitions for the pattern matrix that is used
//! during computing the usefulness and exhaustiveness of a
//! set of patterns. [MatrixOps] is a collection of operations
//! that occur on the [Matrix] when the typechecker context
//! is required.
use std::fmt::Debug;

use hash_utils::store::CloneStore;

use super::{stack::PatStack, AccessToUsefulnessOps, PatForFormatting, PreparePatForFormatting};
use crate::old::{
    exhaustiveness::PatCtx,
    ops::AccessToOps,
    storage::{
        exhaustiveness::{DeconstructedCtorId, DeconstructedPatId},
        AccessToStorage, StorageRef,
    },
};

/// A 2D matrix which is used to represent the
/// pattern matrix in order to produce [super::usefulness::Witness]
/// entries when traversing each row.
///
/// Each row can be thought of as a match arm in
/// the match block, however most rows in the
/// [Matrix] are generated from when patterns are
/// specialised or expanded.
#[derive(Clone)]
pub struct Matrix {
    /// The inner rows of the [Matrix].
    pub patterns: Vec<PatStack>,
}

impl Matrix {
    /// Create a new [Matrix] with zero rows and columns.
    pub fn empty() -> Self {
        Matrix { patterns: vec![] }
    }

    /// Number of columns of this matrix. `None` is the matrix is empty.
    pub fn column_count(&self) -> Option<usize> {
        self.patterns.get(0).map(|r| r.len())
    }

    /// Iterate over the first component of each row
    pub fn heads(&self) -> impl Iterator<Item = DeconstructedPatId> + Clone + '_ {
        self.patterns.iter().map(|r| r.head())
    }
}

/// Contains functions related to operations on [Matrix]
pub struct MatrixOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for MatrixOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> MatrixOps<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Pushes a new row to the matrix. If the row starts with an or-pattern,
    /// this recursively expands it.
    pub(crate) fn push(&self, matrix: &mut Matrix, row: PatStack) {
        if !row.is_empty() {
            let reader = self.reader();
            let pat = reader.get_deconstructed_pat(row.head());

            if self.deconstruct_pat_ops().is_or_pat(&pat) {
                return matrix.patterns.extend(self.stack_ops().expand_or_pat(&row));
            }
        }

        matrix.patterns.push(row);
    }

    /// This computes `S(constructor, matrix)`.
    pub(crate) fn specialise_ctor(
        &self,
        ctx: PatCtx,
        matrix: &Matrix,
        ctor_id: DeconstructedCtorId,
    ) -> Matrix {
        let mut specialised_matrix = Matrix::empty();
        let ctor = self.constructor_store().get(ctor_id);
        let reader = self.reader();

        // Iterate on each row, and specialise the `head` of
        // each row within the matrix with the provided constructor,
        // the results of the specialisation as new rows in
        // the matrix.
        for row in &matrix.patterns {
            let row_head_ctor = reader.get_deconstructed_pat_ctor(row.head());

            if self.constructor_ops().is_covered_by(&ctor, &row_head_ctor) {
                let new_row = self.stack_ops().pop_head_constructor(ctx, row, ctor_id);
                self.push(&mut specialised_matrix, new_row);
            }
        }

        specialised_matrix
    }
}

impl PreparePatForFormatting for Matrix {}

/// Pretty-printer for matrices of patterns, example:
///
/// ```text
/// | _     | []                |
/// | true  | [First]           |
/// | true  | [Second(true)]    |
/// | false | [_]               |
/// | _     | [_, _, ...tail]   |
/// ```
impl Debug for PatForFormatting<'_, Matrix> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f)?;

        let Matrix { patterns: m, .. } = &self.item;

        // Firstly, get all the patterns within the matrix as strings...
        let pretty_printed_matrix: Vec<Vec<String>> = m
            .iter()
            .map(|row| {
                row.iter().map(|pat| format!("{:?}", pat.for_formatting(self.storage))).collect()
            })
            .collect();

        let column_count = m.iter().map(|row| row.len()).next().unwrap_or(0);

        // Ensure that all of the rows have the same length
        assert!(m.iter().all(|row| row.len() == column_count));

        let column_widths: Vec<usize> = (0..column_count)
            .map(|col| pretty_printed_matrix.iter().map(|row| row[col].len()).max().unwrap_or(0))
            .collect();

        for row in pretty_printed_matrix {
            write!(f, "|")?;
            for (column, pat_str) in row.into_iter().enumerate() {
                write!(f, " ")?;
                write!(f, "{:1$}", pat_str, column_widths[column])?;
                write!(f, " |")?;
            }
            writeln!(f)?;
        }

        Ok(())
    }
}
