//! Stores [DeconstructedPat]s and [DeconstructedCtor]s.'
use hash_utils::index_vec::{define_index_type, IndexVec};

use crate::{
    construct::DeconstructedCtor, deconstruct::DeconstructedPat, ExhaustivenessChecker,
    ExhaustivenessEnv,
};

define_index_type! {
    /// Id of a [DeconstructedPat] in the [ExhaustivenessCtx].
    pub struct DeconstructedPatId = u32;

    MAX_INDEX = u32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

define_index_type! {
    /// Id of a [DeconstructedCtor] in the [ExhaustivenessCtx].
    pub struct DeconstructedCtorId = u32;

    MAX_INDEX = u32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

pub type DeconstructedPatStore = IndexVec<DeconstructedPatId, DeconstructedPat>;

pub type DeconstructedCtorStore = IndexVec<DeconstructedCtorId, DeconstructedCtor>;

/// The [ExhaustivenessStorage] holds data structures that are used during
/// exhaustiveness checking as intermediate representations of patterns.
#[derive(Debug, Default)]
pub(crate) struct ExhaustivenessCtx {
    /// The [crate::deconstruct::DeconstructedPat] store.
    pub(crate) dp: DeconstructedPatStore,

    /// The [crate::construct::DeconstructedCtor] store.
    pub(crate) dc: DeconstructedCtorStore,
}

impl ExhaustivenessCtx {
    /// Create a new [ExhaustivenessCtx].
    pub fn new() -> Self {
        Self { dc: IndexVec::new(), dp: IndexVec::new() }
    }
}

impl<'env, E: ExhaustivenessEnv> ExhaustivenessChecker<'env, E> {
    pub(crate) fn get_ctor(&self, id: DeconstructedCtorId) -> &DeconstructedCtor {
        &self.ecx.dc[id]
    }

    pub(crate) fn get_pat(&self, id: DeconstructedPatId) -> &DeconstructedPat {
        &self.ecx.dp[id]
    }

    pub(crate) fn get_pat_ctor(&self, id: DeconstructedPatId) -> &DeconstructedCtor {
        self.get_ctor(self.get_pat(id).ctor)
    }

    pub(crate) fn get_pat_mut(&mut self, id: DeconstructedPatId) -> &mut DeconstructedPat {
        &mut self.ecx.dp[id]
    }

    pub(crate) fn make_pat(&mut self, deconstructed_pat: DeconstructedPat) -> DeconstructedPatId {
        self.ecx.dp.push(deconstructed_pat)
    }

    pub(crate) fn make_ctor(
        &mut self,
        deconstructed_ctor: DeconstructedCtor,
    ) -> DeconstructedCtorId {
        self.ecx.dc.push(deconstructed_ctor)
    }
}
