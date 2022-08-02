use crate::storage::primitives::{DeconstructedPatId, TermId};

#[derive(Debug, Clone)]
pub struct Fields {
    pub fields: Vec<DeconstructedPatId>,
}

impl Fields {
    pub fn empty() -> Self {
        Fields { fields: vec![] }
    }

    /// Returns the list of patterns.
    pub fn iter_patterns(&self) -> impl Iterator<Item = &DeconstructedPatId> {
        self.fields.iter()
    }

    pub fn from_iter(fields: impl IntoIterator<Item = DeconstructedPatId>) -> Self {
        // let fields: &[_] = cx.pattern_arena.alloc_from_iter(fields);
        // Fields { fields }
        todo!()
    }

    pub fn wildcards_from_tys(tys: impl IntoIterator<Item = TermId>) -> Self {
        // Fields::from_iter(tys.into_iter().map(DeconstructedPat::wildcard))
        todo!()
    }
}
