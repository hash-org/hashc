//! Contains structures to track information about the current state of the typechecker while
//! traversing the AST.
use super::primitives::TermId;
use hash_source::SourceId;
use std::cell::Cell;

/// Keeps track of various information about the current state of the typechecker while traversing
/// and checking the AST.
///
/// @@Volatile: this will probably change a lot when the AST traversing is implemented, maybe it
/// should be in the traverse module?
#[derive(Debug)]
pub struct TcState {
    /// Whether the current function has returned explicitly at least once.
    pub ret_once: Cell<bool>,
    /// The return type of the function being currently checked (if any).
    pub func_ret_ty: Cell<Option<TermId>>,
    /// The current source being typechecked.
    pub current_source: Cell<SourceId>,
    /// A hint about the type of the pattern in the let statement that is being checked.
    pub let_pattern_hint: Cell<Option<TermId>>,
}

impl TcState {
    /// Create an empty [TcState] for the given source.
    pub fn new(current_source: SourceId) -> Self {
        Self {
            ret_once: Cell::new(false),
            func_ret_ty: Cell::new(None),
            current_source: Cell::new(current_source),
            let_pattern_hint: Cell::new(None),
        }
    }
}
