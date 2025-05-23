//! Definitions related to arguments to data structures, functions,
//! etc.
use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_storage::store::{
    SequenceStoreKey, TrivialSequenceStoreKey,
    statics::{SequenceStoreValue, StoreId},
};
use hash_utils::itertools::Itertools;

use crate::{
    stores::tir_stores,
    tir::{
        HasAstNodeId, Node, NodeId, NodeOrigin, NodesId, ParamIndex, ParamsId, PatId, SymbolId,
        Term, TermId,
    },
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

    /// Instantiate the given parameters with holes for each argument.
    ///
    /// This will use the origin of the parameters wrapped in
    /// [`NodeOrigin::InferredFrom`].
    pub fn seq_from_params_as_holes(params_id: ParamsId) -> ArgsId {
        Node::create_at(
            Node::seq(
                params_id
                    .value()
                    .iter()
                    .enumerate()
                    .map(|(i, param)| {
                        Node::at(
                            Arg {
                                target: ParamIndex::pos(i),
                                value: Term::hole(param.origin().inferred()),
                            },
                            param.origin().inferred(),
                        )
                    })
                    .collect_vec(),
            ),
            params_id.origin().inferred(),
        )
    }
}

/// A pattern or a capture.
///
/// A capture exists in pattern lists and pattern arguments, and is used to
/// indicate that this field is captured by a spread pattern in the aggregate.
///
/// Initially, no pattern arguments are captures, instead the `spread` member in
/// pattern lists denotes where the spread is located. Then, the list is
/// reordered to match the target parameter list, which involves making some
/// slots into `PatOrCapture::Capture` to indicate that the corresponding
/// parameter is captured by the spread. After that point the spread is no
/// longer needed (other than for errors).
#[derive(Debug, Clone, Copy, From, PartialEq, Eq)]
pub enum PatOrCapture {
    /// A pattern.
    Pat(PatId),
    /// A capture.
    Capture(Node<()>),
}

impl PatOrCapture {
    /// Used for or-patterns which use a `PatListId` but contain no captures.
    pub fn assert_pat(self) -> PatId {
        match self {
            PatOrCapture::Pat(pat) => pat,
            PatOrCapture::Capture(_) => panic!("Expected a pattern, got a capture"),
        }
    }
}

/// A pattern argument to a parameter
///
/// This might be used for constructor patterns like `C(true, x)`.
#[derive(Debug, Clone, Copy)]
pub struct PatArg {
    /// Argument target (named or positional).
    pub target: ParamIndex,
    /// The pattern in place for this argument.
    pub pat: PatOrCapture,
}

tir_node_sequence_store_direct!(PatArg);

impl PatArgsId {
    /// Use the patterns in this argument list as terms, if possible.
    ///
    /// This invokes [`Pat::try_use_as_term`] on each pattern in the list.
    pub fn try_use_as_term_args(&self) -> Option<ArgsId> {
        let mut args = Vec::new();
        for pat_arg in self.iter() {
            let pat_arg = pat_arg.value();
            match pat_arg.pat {
                PatOrCapture::Pat(pat) => {
                    let term = pat.try_use_as_term()?;
                    args.push(Node::at(
                        Arg { target: pat_arg.target, value: term },
                        pat_arg.origin,
                    ));
                }
                PatOrCapture::Capture(_) => return None,
            }
        }
        Some(Node::create_at(Node::<Arg>::seq(args), self.origin()))
    }
}

/// Some kind of arguments, either [`PatArgsId`] or [`ArgsId`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum SomeArgsId {
    PatArgs(PatArgsId),
    Args(ArgsId),
}

impl SomeArgsId {
    pub fn origin(self) -> NodeOrigin {
        match self {
            SomeArgsId::PatArgs(id) => id.origin(),
            SomeArgsId::Args(id) => id.origin(),
        }
    }
}

/// An index into a `SomeArgsId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum SomeArgId {
    PatArg(PatArgId),
    Arg(ArgId),
}

impl SomeArgId {
    pub fn origin(self) -> NodeOrigin {
        match self {
            SomeArgId::PatArg(id) => id.origin(),
            SomeArgId::Arg(id) => id.origin(),
        }
    }

    pub fn into_name(&self, origin: NodeOrigin) -> SymbolId {
        self.target().into_symbol(origin)
    }

    // Get the actual numerical parameter index from a given [ParamsId] and
    // [ParamIndex].
    pub fn target(&self) -> ParamIndex {
        match self {
            SomeArgId::PatArg(id) => id.value().target,
            SomeArgId::Arg(id) => id.value().target,
        }
    }
}

impl SequenceStoreKey for SomeArgsId {
    type ElementKey = SomeArgId;

    fn to_index_and_len(self) -> (usize, usize) {
        match self {
            SomeArgsId::PatArgs(id) => id.elements().to_index_and_len(),
            SomeArgsId::Args(id) => id.elements().to_index_and_len(),
        }
    }

    unsafe fn from_raw_parts(_: usize, _: usize) -> Self {
        panic!("Creating SomeArgsId is not allowed")
    }
}

impl From<(SomeArgsId, usize)> for SomeArgId {
    fn from(value: (SomeArgsId, usize)) -> Self {
        match value.0 {
            SomeArgsId::PatArgs(id) => SomeArgId::PatArg(PatArgId::new(id.elements(), value.1)),
            SomeArgsId::Args(id) => SomeArgId::Arg(ArgId::new(id.elements(), value.1)),
        }
    }
}

impl HasAstNodeId for SomeArgsId {
    fn node_id(&self) -> Option<hash_ast::ast::AstNodeId> {
        match self {
            SomeArgsId::PatArgs(id) => id.node_id(),
            SomeArgsId::Args(id) => id.node_id(),
        }
    }
}

impl HasAstNodeId for SomeArgId {
    fn node_id(&self) -> Option<hash_ast::ast::AstNodeId> {
        match self {
            SomeArgId::PatArg(id) => id.node_id(),
            SomeArgId::Arg(id) => id.node_id(),
        }
    }
}

impl fmt::Display for SomeArgsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SomeArgsId::Args(id) => write!(f, "{}", id),
            SomeArgsId::PatArgs(id) => write!(f, "{}", id),
        }
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

impl fmt::Display for PatOrCapture {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatOrCapture::Pat(pat) => {
                write!(f, "{}", pat)
            }
            PatOrCapture::Capture(_) => {
                write!(f, "_")
            }
        }
    }
}

impl fmt::Display for PatArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.target {
            ParamIndex::Name(name) => {
                write!(f, "{} = {}", name, self.pat)
            }
            ParamIndex::Position(_) => write!(f, "{}", self.pat),
        }
    }
}

impl fmt::Display for PatArgId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", *self.value())
    }
}

impl fmt::Display for PatArgsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, pat_arg) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", pat_arg)?;
        }
        Ok(())
    }
}
