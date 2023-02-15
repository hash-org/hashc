use core::fmt;
use std::fmt::Display;

use hash_utils::store::SequenceStore;

use crate::{
    environment::env::{AccessToEnv, WithEnv},
    pats::{PatId, PatListId, Spread},
    terms::{TermId, TermListId},
};

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
pub struct ArrayTerm {
    pub elements: TermListId,
}

/// A list pattern.
///
/// This is in the form `[x_1,...,x_n]`, with an optional spread `...(name?)` at
/// some position.
#[derive(Copy, Clone, Debug)]
pub struct ArrayPat {
    /// The sequence of patterns in the list pattern.
    pub pats: PatListId,
    /// The spread pattern, if any.
    pub spread: Option<Spread>,
}

impl ArrayPat {
    /// Split the pattern into the `prefix`, `suffix` and an optional;
    /// `rest` pattern.
    pub fn into_parts<T>(&self, tcx: &T) -> (Vec<PatId>, Vec<PatId>, Option<Spread>)
    where
        T: AccessToEnv,
    {
        let mut prefix = vec![];
        let mut suffix = vec![];

        tcx.stores().pat_list().map_fast(self.pats, |args| {
            if let Some(pos) = self.spread.map(|s| s.index) {
                prefix.extend(args[..pos].iter().copied().map(|p| p.assert_pat()));
                suffix.extend(args[pos..].iter().copied().map(|p| p.assert_pat()));
            } else {
                prefix.extend(args.iter().copied().map(|p| p.assert_pat()));
            }
        });

        (prefix, suffix, self.spread)
    }
}

impl fmt::Display for WithEnv<'_, &IndexTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[{}]", self.env().with(self.value.subject), self.env().with(self.value.index),)
    }
}

impl fmt::Display for WithEnv<'_, &ArrayPat> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        self.stores().pat_list().map_fast(self.value.pats, |pat_list| {
            let mut pat_args_formatted =
                pat_list.iter().map(|arg| self.env().with(*arg).to_string()).collect::<Vec<_>>();

            if let Some(spread) = self.value.spread {
                pat_args_formatted.insert(spread.index, self.env().with(spread).to_string());
            }

            for (i, pat_arg) in pat_args_formatted.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{pat_arg}")?;
            }
            Ok(())
        })?;
        write!(f, "]")
    }
}

impl Display for WithEnv<'_, &ArrayTerm> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.env().with(self.value.elements))
    }
}
