//! This file contains the logic and the intermediate representation for the
//! deconstruction of patterns. Within [crate::exhaustiveness] there is a
//! defined pattern representation [crate::exhaustiveness::Pat], this  
//! file contains the [Constructor] and [DeconstructedPat] representations
//! that are further reduced representations of the patterns in
//! order to reduce the complexity of the usefulness/exhaustiveness
//! algorithms.
#![allow(unused)]

use std::{
    cell::Cell,
    cmp::{max, min},
    fmt,
    iter::{self, once},
    ops::RangeInclusive,
};

use hash_reporting::macros::panic_on_span;
use hash_source::{
    location::{SourceLocation, Span},
    string::Str,
};
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};

use crate::{
    diagnostics::macros::tc_panic,
    exhaustiveness::PatKind,
    ops::AccessToOps,
    storage::{
        primitives::{
            ConstructedTerm, Level0Term, Level1Term, LitTerm, NominalDef, StructFields, Term,
            TermId, TupleLit, TupleTy, DeconstructedPatId,
        },
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};

use super::{constant::Constant, FieldPat, Pat};

