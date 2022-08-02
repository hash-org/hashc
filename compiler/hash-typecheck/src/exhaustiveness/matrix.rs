use crate::{
    exhaustiveness::structures::PatCtx,
    ops::AccessToOps,
    storage::{
        primitives::{ConstructorId, DeconstructedPatId},
        AccessToStorage, StorageRef,
    },
};

use super::{stack::PatStack, AccessToUsefulnessOps};

/// A 2D matrix.
#[derive(Clone)]
pub struct Matrix {
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

// /// Pretty-printer for matrices of patterns, example:
// ///
// /// ```text
// /// | _     | []                |
// /// | true  | [First]           |
// /// | true  | [Second(true)]    |
// /// | false | [_]               |
// /// | _     | [_, _, ...tail]   |
// /// ```
// // impl<'p> fmt::Debug for Matrix<'p> {
// //     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
// //         writeln!(f)?;

// //         let Matrix { patterns: m, .. } = self;
// //         let pretty_printed_matrix: Vec<Vec<String>> =
// //             m.iter().map(|row| row.iter().map(|pat| format!("{:?}",
// pat)).collect()).collect();

// //         let column_count = m.iter().map(|row|
// row.len()).next().unwrap_or(0); //         assert!(m.iter().all(|row|
// row.len() == column_count)); //         let column_widths: Vec<usize> =
// (0..column_count) //             .map(|col|
// pretty_printed_matrix.iter().map(|row| row[col].len()).max().unwrap_or(0)) //
// .collect();

// //         for row in pretty_printed_matrix {
// //             write!(f, "|")?;
// //             for (column, pat_str) in row.into_iter().enumerate() {
// //                 write!(f, " ")?;
// //                 write!(f, "{:1$}", pat_str, column_widths[column])?;
// //                 write!(f, " +")?;
// //             }
// //             writeln!(f)?;
// //         }
// //         Ok(())
// //     }
// // }

/// Contains functions related to operations on [Matrix]
pub struct MatrixOps<'gs, 'ls, 'cd, 's> {
    storage: StorageRef<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for MatrixOps<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 's> MatrixOps<'gs, 'ls, 'cd, 's> {
    pub fn new(storage: StorageRef<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Pushes a new row to the matrix. If the row starts with an or-pattern,
    /// this recursively expands it.
    pub(crate) fn push(&self, matrix: &mut Matrix, row: PatStack) {
        let reader = self.reader();
        let ctor = reader.get_deconstructed_pat(row.head());

        if !row.is_empty() && self.deconstruct_pat_ops().is_or_pat(&ctor) {
            matrix.patterns.extend(self.stack_ops().expand_or_pat(&row));
        } else {
            matrix.patterns.push(row);
        }
    }

    /// This computes `S(constructor, self)`. See top of the file for
    /// explanations.
    pub(crate) fn specialise_ctor(
        &self,
        ctx: PatCtx,
        matrix: &Matrix,
        ctor_id: ConstructorId,
    ) -> Matrix {
        let reader = self.reader();
        let mut s_matrix = Matrix::empty();

        let ctor = self.constructor_store().get(ctor_id);

        for row in &matrix.patterns {
            let head = reader.get_deconstructed_pat(row.head());

            let other = self.constructor_store().get(head.ctor());

            if self.constructor_ops().is_covered_by(ctx, &ctor, &other) {
                let new_row = self.stack_ops().pop_head_constructor(ctx, row, ctor_id);
                self.push(&mut s_matrix, new_row);
            }
        }

        s_matrix
    }
}
