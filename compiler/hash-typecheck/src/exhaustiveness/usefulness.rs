use crate::storage::primitives::DeconstructedPatId;
use hash_source::location::Span;
use smallvec::{smallvec, SmallVec};

#[derive(Debug)]
pub struct Witness(pub Vec<DeconstructedPatId>);

impl Witness {
    /// Asserts that the witness contains a single pattern, and returns it.   
    pub fn single_pattern(self) -> DeconstructedPatId {
        assert_eq!(self.0.len(), 1);

        self.0.into_iter().next().unwrap()
    }
}

// /// A row of a matrix. Rows of len 1 are very common, which is why
// `SmallVec[_; /// 2]` works well.
#[derive(Clone)]
pub struct PatStack {
    pub pats: SmallVec<[DeconstructedPatId; 2]>,
}

impl PatStack {
    // /// Construct a [PatStack] with a single pattern.
    pub fn singleton(pat: DeconstructedPatId) -> Self {
        Self::from_vec(smallvec![pat])
    }

    // /// Construct a [PatStack] from a [SmallVec].
    pub fn from_vec(vec: SmallVec<[DeconstructedPatId; 2]>) -> Self {
        PatStack { pats: vec }
    }

    /// Check whether the current [PatStack] is empty
    pub fn is_empty(&self) -> bool {
        self.pats.is_empty()
    }

    /// Get the length of the [PatStack]
    pub fn len(&self) -> usize {
        self.pats.len()
    }

    /// Get the head of the current [PatStack]
    pub fn head(&self) -> DeconstructedPatId {
        self.pats[0]
    }

    /// Iterate over the items within the [PatStack].
    pub fn iter(&self) -> impl Iterator<Item = &DeconstructedPatId> {
        self.pats.iter()
    }
}

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
    pub fn heads<'a>(&'a self) -> impl Iterator<Item = DeconstructedPatId> + Clone + 'a {
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

#[derive(Debug)]
pub enum Usefulness {
    /// If we don't care about witnesses, simply remember if the pattern was
    /// useful.
    NoWitnesses { useful: bool },
    /// Carries a list of witnesses of non-exhaustiveness. If empty, indicates
    /// that the whole pattern is unreachable.
    WithWitnesses(Vec<Witness>),
}

impl Usefulness {
    /// Create a `useful` [Usefulness] report.
    pub fn new_useful(preference: MatchArmKind) -> Self {
        match preference {
            //            A single (empty) witness of reachability.
            MatchArmKind::ExhaustiveWildcard => Usefulness::WithWitnesses(vec![Witness(vec![])]),
            MatchArmKind::Real => Usefulness::NoWitnesses { useful: true },
        }
    }

    /// Create a `useless` [Usefulness] report.
    pub fn new_not_useful(preference: MatchArmKind) -> Self {
        match preference {
            MatchArmKind::ExhaustiveWildcard => Usefulness::WithWitnesses(vec![Witness(vec![])]),
            MatchArmKind::Real => Usefulness::NoWitnesses { useful: false },
        }
    }

    /// Check if the [Usefulness] report specifies that the pattern is  useful.
    pub fn is_useful(&self) -> bool {
        match self {
            Usefulness::NoWitnesses { useful } => *useful,
            Usefulness::WithWitnesses(witnesses) => !witnesses.is_empty(),
        }
    }

    /// Combine usefulnesses from two branches. This is an associative
    /// operation.
    pub fn extend(&mut self, other: Self) {
        match (&mut *self, other) {
            (Usefulness::WithWitnesses(_), Usefulness::WithWitnesses(o)) if o.is_empty() => {}
            (Usefulness::WithWitnesses(s), Usefulness::WithWitnesses(o)) if s.is_empty() => {
                *self = Usefulness::WithWitnesses(o)
            }
            (Usefulness::WithWitnesses(s), Usefulness::WithWitnesses(o)) => s.extend(o),
            (
                Usefulness::NoWitnesses { useful: s_useful },
                Usefulness::NoWitnesses { useful: o_useful },
            ) => *s_useful = *s_useful || o_useful,
            _ => unreachable!(),
        }
    }
}

/// Enum used to represent the kind of match arm that is being
/// checked for usefulness. This exists in order to be able to
/// inject a `dummy` match-arm to collect witnesses of patterns
/// that the branch will capture.
#[derive(Debug, Clone, Copy)]
pub enum MatchArmKind {
    /// This is used as a `dummy` kind of arm in order to
    /// detect any witnesses that haven't been picked up when
    /// walking through the the arms of a match block.
    ExhaustiveWildcard,
    /// Normal match arm, has no particular behaviour when
    /// checking the usefulness of the pattern.
    Real,
}

/// The arm of a match expression.
#[derive(Clone, Copy, Debug)]
pub(crate) struct MatchArm {
    /// The pattern must have been lowered through
    /// `check_match::MatchVisitor::lower_pattern`.
    pub(crate) pat: DeconstructedPatId,
    pub(crate) has_guard: bool,
}

/// Indicates whether or not a given arm is reachable.
#[derive(Clone, Debug)]
pub(crate) enum Reachability {
    /// The arm is reachable. This additionally carries a set of or-pattern
    /// branches that have been found to be unreachable despite the overall
    /// arm being reachable. Used only in the presence of or-patterns,
    /// otherwise it stays empty.
    Reachable(Vec<Span>),
    /// The arm is unreachable.
    Unreachable,
}

/// The output of checking a match for exhaustiveness and arm reachability.
pub(crate) struct UsefulnessReport {
    /// For each arm of the input, whether that arm is reachable after the arms
    /// above it.
    pub(crate) arm_usefulness: Vec<(MatchArm, Reachability)>,
    /// If the match is exhaustive, this is empty. If not, this contains
    /// witnesses for the lack of exhaustiveness.
    pub(crate) non_exhaustiveness_witnesses: Vec<DeconstructedPatId>,
}

