//! Contains structures to track information about the current state of the typecheker while
//! traversing the AST.
use super::primitives::KindId;
use hash_source::SourceId;
use std::cell::Cell;

/// Keeps track of various information about the current state of the typecheker while traversing
/// and checking the AST.
#[derive(Debug)]
pub struct TypecheckState {
    /// Whether or not the typecheker is in a `loop` AST block.
    pub in_loop: Cell<bool>,
    /// Whether the current function has returned explicitly at least once.
    pub ret_once: Cell<bool>,
    /// The return kind of the function being currently checked (if any).
    pub func_ret_kind: Cell<Option<KindId>>,
    /// The current source being typechecked.
    pub current_source: Cell<SourceId>,
    /// A hint about the kind of the pattern in the let statement that is being checked.
    pub let_pattern_hint: Cell<Option<KindId>>,
}

impl TypecheckState {
    /// Create an empty [TypecheckState] for the given source.
    pub fn new(current_source: SourceId) -> Self {
        Self {
            in_loop: Cell::new(false),
            ret_once: Cell::new(false),
            func_ret_kind: Cell::new(None),
            current_source: Cell::new(current_source),
            let_pattern_hint: Cell::new(None),
        }
    }
}
