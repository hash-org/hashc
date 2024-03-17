//! Definitions related to arguments to data structures, functions,
//! etc.
use core::fmt;
use std::{fmt::Debug, option::Option};

use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    CloneStore, SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_utils::itertools::Itertools;

use super::{Pat, Spread};
use crate::{
    stores::tir_stores,
    tir::{HasAstNodeId, Node, NodeId, NodeOrigin, NodesId, ParamIndex, ParamsId, Term, TermId},
    tir_node_sequence_store_direct,
};

/// An argument to a parameter.
///
/// This might be used for arguments in constructor calls `C(...)`, function
/// calls `f(...)` or `f<...>`, or type arguments.
#[derive(Debug, Clone, Copy)]
pub struct Arg {
    /// Argument target (named or positional), if known.
    pub target: ParamIndex,
    /// The term that is the value of the argument.
    pub value: TermId,
}

pub type PatArgId = ArgId;
pub type PatArgsId = ArgsId;

tir_node_sequence_store_direct!(Arg);

impl Arg {
    /// From the given parameters, create arguments that directly refer to the
    /// parameters using `Term::Var`.
    ///
    /// Example:
    /// ```notrust
    /// X := datatype <A: Type, B: Type, C: Type> { foo: () -> X<A, B, C> }
    ///                                                         ^^^^^^^^^ this is what this function creates
    /// ```
    ///
    /// This will use the origin of the arguments.
    pub fn seq_from_param_names_as_vars(params_id: ParamsId) -> ArgsId {
        Node::create_at(
            // For each parameter, create an argument referring to it
            Node::seq(
                params_id
                    .value()
                    .iter()
                    .enumerate()
                    .map(|(i, param)| {
                        Node::at(
                            Arg {
                                target: ParamIndex::pos(i),
                                value: Term::var(param.value().name),
                            },
                            param.origin(),
                        )
                    })
                    .collect_vec(),
            ),
            params_id.origin(),
        )
    }

    /// Create definition arguments for the given data definition
    ///
    /// Each argument will be a positional argument. Note that the outer
    /// iterator is for the argument groups, and the inner iterator is for
    /// the arguments in each group.
    pub fn seq_positional(args: impl IntoIterator<Item = TermId>, origin: NodeOrigin) -> ArgsId {
        Node::create_at(
            Node::seq(
                args.into_iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        Node::at(Arg { target: ParamIndex::pos(i), value: arg }, arg.origin())
                    })
                    .collect_vec(),
            ),
            origin,
        )
    }
}

impl ArgsId {
    /// Get the first spread argument, if any.
    pub fn get_spread(&self) -> Option<Spread> {
        for arg in self.iter() {
            if let Term::Pat(Pat::Spread(spread)) = arg.value().data.value.value().data {
                return Some(spread);
            }
        }
        None
    }

    /// Get the index of the first spread argument, if any.
    pub fn get_spread_idx(&self) -> Option<usize> {
        for (i, arg) in self.iter().enumerate() {
            if let Term::Pat(Pat::Spread(_)) = arg.value().data.value.value().data {
                return Some(i);
            }
        }
        None
    }

    /// Given that this `ArgsId` represents a pattern, separate the pattern list
    /// into the `prefix`, `suffix` and an optional; `rest` pattern.
    pub fn into_pat_parts(&self) -> (Vec<TermId>, Vec<TermId>, Option<Spread>) {
        let mut prefix = vec![];
        let mut suffix = vec![];
        let mut spread = None;

        for arg in self.iter() {
            let pat = arg.borrow().data.value;
            match (pat.borrow().data, spread.is_some()) {
                (Term::Pat(Pat::Spread(s)), false) => {
                    spread = Some(s);
                }
                (Term::Pat(Pat::Spread(_)), true) => {
                    panic!("Multiple spreads in a pattern list")
                }
                (_, false) => {
                    prefix.push(pat);
                }
                (_, true) => {
                    suffix.push(pat);
                }
            }
        }

        (prefix, suffix, spread)
    }
}

impl fmt::Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.target {
            ParamIndex::Name(name) => {
                write!(f, "{} = {}", name, self.value)
            }
            ParamIndex::Position(_) => write!(f, "{}", self.value),
        }
    }
}

impl fmt::Display for ArgId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", *self.value())
    }
}

impl fmt::Display for ArgsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, arg) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        Ok(())
    }
}
