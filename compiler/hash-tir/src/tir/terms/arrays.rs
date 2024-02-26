use core::fmt;
use std::fmt::Display;

use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};

use super::Term;
use crate::tir::{NodeId, NodeOrigin, NodesId, Pat, Spread, TermId, TermListId};

/// A term that is used as an index into an array.
#[derive(Debug, Clone, Copy)]
pub struct IndexTerm {
    /// The subject array of the indexing operation.
    pub subject: TermId,
    /// The index of the indexing operation.
    pub index: TermId,
}

/// A list constructor
///
/// Contains a sequence of terms.
#[derive(Copy, Clone, Debug)]
pub enum ArrayTerm {
    /// When an array is written as a normal variant, i.e. `[x, y, z]`.
    Normal(TermListId),

    /// When an array is written as a repeated variant, i.e. `[x; 5]`. The
    /// second term must be a constant integer.
    Repeated(TermId, TermId),
}

impl ArrayTerm {
    /// Get an element of the array.
    ///
    /// N.B. For repeated arrays, this will return the repeated element
    /// regardless of the index.
    pub fn element_at(&self, index: usize) -> Option<TermId> {
        match self {
            ArrayTerm::Normal(elements) => elements.elements().at(index),
            ArrayTerm::Repeated(element, _) => Some(*element),
        }
    }

    /// Get the [NodeOrigin] of the elements of the array.
    ///
    /// - For [ArrayTerm::Normal], it is the term list.
    ///
    /// - For [ArrayTerm::Repeated], it is the subject of the repeat.
    pub fn elements_origin(&self) -> NodeOrigin {
        match self {
            ArrayTerm::Normal(elements) => elements.origin(),
            ArrayTerm::Repeated(element, _) => element.origin(),
        }
    }

    /// Get the [NodeOrigin] of the "computed" length of the array.
    ///
    /// - For [ArrayTerm::Normal], it is the term list.
    ///
    /// - For [ArrayTerm::Repeated], it is the repeated element.
    pub fn length_origin(&self) -> NodeOrigin {
        match self {
            ArrayTerm::Normal(elements) => elements.origin(),
            ArrayTerm::Repeated(_, repeat) => repeat.origin(),
        }
    }

    /// Get the first spread argument, if any.
    pub fn get_spread(&self) -> Option<Spread> {
        match self {
            ArrayTerm::Normal(array) => {
                for term in array.iter() {
                    if let Term::Pat(Pat::Spread(spread)) = term.value().data {
                        return Some(spread);
                    }
                }
                None
            }
            ArrayTerm::Repeated(_, _) => None,
        }
    }

    /// Get the length of the array.
    pub fn elements_or_repeated(&self) -> Option<TermListId> {
        match self {
            ArrayTerm::Normal(elements) => Some(*elements),
            ArrayTerm::Repeated(_, _) => None,
        }
    }
}

impl fmt::Display for IndexTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[{}]", self.subject, self.index)
    }
}

impl Display for ArrayTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArrayTerm::Normal(elements) => write!(f, "[{elements}]"),
            ArrayTerm::Repeated(subject, repeat) => write!(f, "[{subject}; {repeat}]"),
        }
    }
}
