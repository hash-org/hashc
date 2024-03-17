//! Resolution of item paths in the AST.
//!
//! An item path is something that follows the grammar:
//!
//! ```notrust
//! path ::= path_component ( "::" path_component )
//! path_component ::= identifier ( ( "<" args ">" ) | ( "(" args ")" ) )*
//! ```
//! where `args` are type args, expr args, or pattern args.
//!
//! Paths in the AST can be resolved to a number of different things:
//! - Types: Data types, function calls
//! - Terms: Functions, function calls, constructors
//! - Patterns: Constructors
//!
//! This module contains the [`AstPath`] type, which is used to represent paths
//! in the AST before they are resolved. The [`ResolvedAstPathComponent`] type
//! is used to represent a path or path component after it has been resolved.
//! This can then be used to create a term, type, or pattern, with appropriate
//! restrictions on the arguments and item kind.

use std::fmt;

use hash_ast::ast::{self, AstNodeId};
use hash_source::{identifier::Identifier, location::Span};
use hash_storage::store::statics::{SequenceStoreValue, StoreId};
use hash_tir::{
    intrinsics::definitions::Intrinsic,
    tir::{
        Arg, ArgsId, CallTerm, CtorTerm, DataDefId, FnDefId, ModDefId, ModMemberValue, Node,
        NodeId, NodeOrigin, SymbolId, Term, VarTerm,
    },
};

use super::{
    params::{AstArgGroup, ResolvedArgs},
    scoping::{BindingKind, ContextKind},
    ResolutionPass,
};
use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
};

/// A path component in the AST.
///
/// A path is a sequence of path components, separated by `::`.
/// A path component is either a name, or a name followed by a list of
/// argument groups, each of which is a [`AstArgGroup`].
///
/// For example: `Foo::Bar::Baz<T, U>(a, b, c)::Bin(3)`.
#[derive(Clone, Debug)]
pub struct AstPathComponent<'a> {
    pub name: Identifier,
    pub name_node_id: AstNodeId,
    pub args: Node<Vec<AstArgGroup<'a>>>,
    pub node_id: ast::AstNodeId,
}

/// A path in the AST.
///
/// For example, `Foo::Bar`.
pub type AstPath<'a> = Vec<AstPathComponent<'a>>;

impl AstPathComponent<'_> {
    /// Get the origin of this path component.
    pub fn origin(&self) -> NodeOrigin {
        NodeOrigin::Given(self.node_id)
    }

    /// Get the span of this path component.
    pub fn span(&self) -> Span {
        let span = self.name_node_id.span();
        if let Some(last_arg) = self.args.last() {
            span.join(last_arg.span())
        } else {
            span
        }
    }
}

/// A non-terminal resolved path component in the AST.
///
/// This is a path component that has been resolved to a non-terminal item,
/// which means that it can be accessed further through `::`.
#[derive(Clone, Copy, Debug)]
pub enum NonTerminalResolvedPathComponent {
    /// A data definition with some arguments.
    Data(DataDefId, ArgsId),
    /// A module definition.
    Mod(ModDefId),
}

/// Each non-terminal resolved path component is a module member.
impl From<NonTerminalResolvedPathComponent> for ModMemberValue {
    fn from(value: NonTerminalResolvedPathComponent) -> Self {
        match value {
            NonTerminalResolvedPathComponent::Data(data_def_id, _) => {
                ModMemberValue::Data(data_def_id)
            }
            NonTerminalResolvedPathComponent::Mod(mod_def_id) => ModMemberValue::Mod(mod_def_id),
        }
    }
}

impl fmt::Display for NonTerminalResolvedPathComponent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match ModMemberValue::from(*self).name() {
            Some(name) => write!(f, "{}", name),
            None => write!(f, "{{unnamed}}"),
        }
    }
}

/// A terminal resolved path component in the AST.
///
/// This is a path component that has been resolved to a terminal item,
/// which means that it cannot be accessed further through `::`.
#[derive(Clone, Copy, Debug)]
pub enum TerminalResolvedPathComponent {
    /// A function reference.
    FnDef(FnDefId),
    /// An intrinsic.
    Intrinsic(Intrinsic),
    /// A data constructor pattern.
    CtorPat(Node<CtorTerm>),
    /// A data constructor term.
    CtorTerm(Node<CtorTerm>),
    /// A function call term.
    FnCall(Node<CallTerm>),
    /// A variable bound in the current context.
    Var(SymbolId),
}

impl TerminalResolvedPathComponent {
    pub fn origin(&self) -> NodeOrigin {
        match self {
            TerminalResolvedPathComponent::FnDef(f) => f.origin(),
            TerminalResolvedPathComponent::CtorPat(c) => c.origin,
            TerminalResolvedPathComponent::CtorTerm(c) => c.origin,
            TerminalResolvedPathComponent::FnCall(f) => f.origin,
            TerminalResolvedPathComponent::Var(v) => v.origin(),
            TerminalResolvedPathComponent::Intrinsic(_) => NodeOrigin::Generated,
        }
    }
}

/// The result of resolving a path component.
///
/// This is either a non-terminal resolved path component, or a terminal
/// resolved path component.
#[derive(Clone, Copy, Debug)]
pub enum ResolvedAstPathComponent {
    NonTerminal(NonTerminalResolvedPathComponent),
    Terminal(TerminalResolvedPathComponent),
}

/// This block performs resolution of AST paths.
impl<E: SemanticEnv> ResolutionPass<'_, E> {
    /// Resolve a name starting from the given [`ModMemberValue`], or the
    /// current context if no such value is given.
    ///
    /// Returns the binding that the name resolves to.
    fn resolve_ast_name(
        &self,
        name: Identifier,
        name_node_id: AstNodeId,
        starting_from: Option<(NonTerminalResolvedPathComponent, Span)>,
    ) -> SemanticResult<(SymbolId, BindingKind)> {
        match starting_from {
            Some((member_value, _span)) => match member_value {
                // If we are starting from a module or data type, we need to enter their scopes.
                NonTerminalResolvedPathComponent::Data(data_def_id, _def_args_id) => self
                    .scoping()
                    .enter_scope(ContextKind::Access(member_value, data_def_id.origin()), || {
                        self.scoping().add_data_params_and_ctors(data_def_id);
                        self.resolve_ast_name(name, name_node_id, None)
                    }),
                NonTerminalResolvedPathComponent::Mod(mod_def_id) => self.scoping().enter_scope(
                    ContextKind::Access(member_value, mod_def_id.origin()),
                    || {
                        self.scoping().add_mod_members(mod_def_id);
                        self.resolve_ast_name(name, name_node_id, None)
                    },
                ),
            },
            None => {
                // If there is no start point, try to lookup the variable in the current scope.
                self.scoping().lookup_symbol_by_name_or_error(
                    name,
                    name_node_id,
                    self.scoping().get_current_context_kind(),
                )
            }
        }
    }

    /// Resolve a path component, starting from the given
    /// [`NonTerminalResolvedPathComponent`] if present, or the current
    /// context if not.
    ///
    /// Returns a [`ResolvedAstPathComponent`] which might or might not support
    /// further accessing depending on the variant.
    fn resolve_ast_path_component(
        &self,
        component: &AstPathComponent<'_>,
        starting_from: Option<(NonTerminalResolvedPathComponent, Span)>,
    ) -> SemanticResult<ResolvedAstPathComponent> {
        let (_binding, binding_kind) =
            self.resolve_ast_name(component.name, component.node_id, starting_from)?;

        match binding_kind {
            BindingKind::ModMember(_, mod_member_id) => {
                let mod_member = mod_member_id.value();
                match mod_member.value {
                    ModMemberValue::Data(data_def_id) => {
                        let data_def_single_ctor = data_def_id.borrow().get_single_ctor();

                        let (data_args, ctor_args): (ResolvedArgs, Option<ResolvedArgs>) =
                            match &component.args[..] {
                                [] => (
                                    ResolvedArgs::Term(Node::create_at(
                                        Node::<Arg>::empty_seq(),
                                        component.args.origin,
                                    )),
                                    None,
                                ),
                                [arg_group] if arg_group.is_implicit() => {
                                    (self.make_args_from_ast_arg_group(arg_group)?, None)
                                }
                                [arg_group] => {
                                    assert!(!arg_group.is_implicit());
                                    (
                                        ResolvedArgs::Term(Node::create_at(
                                            Node::<Arg>::empty_seq(),
                                            component.args.origin,
                                        )),
                                        Some(self.make_args_from_ast_arg_group(arg_group)?),
                                    )
                                }
                                [data_arg_group, ctor_arg_group]
                                    if data_arg_group.is_implicit()
                                        && !ctor_arg_group.is_implicit() =>
                                {
                                    (
                                        (self.make_args_from_ast_arg_group(data_arg_group)?),
                                        Some(self.make_args_from_ast_arg_group(ctor_arg_group)?),
                                    )
                                }
                                [first, second, _rest @ ..] => {
                                    return Err(SemanticError::UnexpectedArguments {
                                        location: first.span().join(second.span()),
                                    });
                                }
                            };

                        match (data_args, ctor_args) {
                            (ResolvedArgs::Term(args), None) => {
                                Ok(ResolvedAstPathComponent::NonTerminal(
                                    NonTerminalResolvedPathComponent::Data(data_def_id, args),
                                ))
                            }
                            // @@Todo: remove this kind of code from here...
                            // Should be done in TC!
                            (
                                ResolvedArgs::Term(_data_args),
                                Some(ResolvedArgs::Pat(ctor_args)),
                            ) => match data_def_single_ctor {
                                Some(ctor) => Ok(ResolvedAstPathComponent::Terminal(
                                    TerminalResolvedPathComponent::CtorPat(Node::at(
                                        CtorTerm { ctor, ctor_args },
                                        component.origin(),
                                    )),
                                )),
                                None => Err(SemanticError::DataDefIsNotSingleton {
                                    location: component.name_node_id.span(),
                                }),
                            },
                            (
                                ResolvedArgs::Term(_data_args),
                                Some(ResolvedArgs::Term(ctor_args)),
                            ) => match data_def_single_ctor {
                                Some(ctor) => Ok(ResolvedAstPathComponent::Terminal(
                                    TerminalResolvedPathComponent::CtorTerm(Node::at(
                                        CtorTerm { ctor, ctor_args },
                                        component.origin(),
                                    )),
                                )),
                                None => Err(SemanticError::DataDefIsNotSingleton {
                                    location: component.name_node_id.span(),
                                }),
                            },
                            (ResolvedArgs::Pat(_), _) => {
                                Err(SemanticError::CannotUseDataTypeInPatternPosition {
                                    location: component.name_node_id.span(),
                                })
                            }
                        }
                    }
                    ModMemberValue::Mod(mod_def_id) => Ok(ResolvedAstPathComponent::NonTerminal(
                        NonTerminalResolvedPathComponent::Mod(mod_def_id),
                    )),
                    ModMemberValue::Fn(fn_def_id) => match &component.args[..] {
                        [] => Ok(ResolvedAstPathComponent::Terminal(
                            TerminalResolvedPathComponent::FnDef(fn_def_id),
                        )),
                        args => {
                            let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                                Term::from(Term::Fn(fn_def_id), component.origin()),
                                args,
                                component.node_id,
                            )?;
                            Ok(ResolvedAstPathComponent::Terminal(
                                TerminalResolvedPathComponent::FnCall(Node::at(
                                    resultant_term,
                                    component.origin(),
                                )),
                            ))
                        }
                    },
                    ModMemberValue::Intrinsic(intrinsic) => match &component.args[..] {
                        [] => Ok(ResolvedAstPathComponent::Terminal(
                            TerminalResolvedPathComponent::Intrinsic(intrinsic),
                        )),
                        args => {
                            let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                                Term::from(Term::Intrinsic(intrinsic), component.origin()),
                                args,
                                component.node_id,
                            )?;
                            Ok(ResolvedAstPathComponent::Terminal(
                                TerminalResolvedPathComponent::FnCall(Node::at(
                                    resultant_term,
                                    component.origin(),
                                )),
                            ))
                        }
                    },
                }
            }
            BindingKind::Ctor(data_def_id, ctor_def_id) => {
                let _ctor_def = ctor_def_id.value();
                let applied_args = match &component.args[..] {
                    [] => ResolvedArgs::Term(Node::create_at(
                        Node::<Arg>::empty_seq(),
                        component.args.origin,
                    )),
                    [arg_group] => self.make_args_from_ast_arg_group(arg_group)?,
                    [_first, second, _rest @ ..] => {
                        return Err(SemanticError::UnexpectedArguments { location: second.span() });
                    }
                };

                match starting_from {
                    Some((starting_from, _)) => match starting_from {
                        NonTerminalResolvedPathComponent::Data(
                            starting_from_data_def_id,
                            _data_args,
                        ) => {
                            assert!(starting_from_data_def_id == data_def_id);
                            match applied_args {
                                ResolvedArgs::Term(ctor_args) => {
                                    Ok(ResolvedAstPathComponent::Terminal(
                                        TerminalResolvedPathComponent::CtorTerm(Node::at(
                                            CtorTerm { ctor: ctor_def_id, ctor_args },
                                            component.origin(),
                                        )),
                                    ))
                                }
                                ResolvedArgs::Pat(ctor_args) => {
                                    Ok(ResolvedAstPathComponent::Terminal(
                                        TerminalResolvedPathComponent::CtorPat(Node::at(
                                            CtorTerm { ctor: ctor_def_id, ctor_args },
                                            component.origin(),
                                        )),
                                    ))
                                }
                            }
                        }

                        NonTerminalResolvedPathComponent::Mod(_) => {
                            unreachable!("Can never have a constructor starting from a module")
                        }
                    },
                    None => unreachable!(),
                }
            }
            BindingKind::Sym(decl) => {
                // If the subject has no args, it is a variable, otherwise it is a
                // function call.
                match &component.args[..] {
                    [] => Ok(ResolvedAstPathComponent::Terminal(
                        TerminalResolvedPathComponent::Var(decl),
                    )),
                    args => {
                        let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                            Term::from(Term::Var(VarTerm { symbol: decl }), component.origin()),
                            args,
                            component.node_id,
                        )?;
                        Ok(ResolvedAstPathComponent::Terminal(
                            TerminalResolvedPathComponent::FnCall(Node::at(
                                resultant_term,
                                component.origin(),
                            )),
                        ))
                    }
                }
            }
        }
    }

    /// Resolve a path in the current context, returning a
    /// [`ResolvedAstPathComponent`] if successful.
    pub fn resolve_ast_path(&self, path: &AstPath) -> SemanticResult<ResolvedAstPathComponent> {
        debug_assert!(!path.is_empty());

        let mut resolved_path = self.resolve_ast_path_component(&path[0], None)?;

        for (index, component) in path.iter().enumerate().skip(1) {
            // For each component, we need to resolve it, and then namespace
            // further if possible.
            match resolved_path {
                ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                    NonTerminalResolvedPathComponent::Data(data_def_id, args) => {
                        // Namespace further if it is a data member.
                        resolved_path = self.resolve_ast_path_component(
                            component,
                            Some((
                                NonTerminalResolvedPathComponent::Data(data_def_id, args),
                                component.span(),
                            )),
                        )?;
                    }
                    NonTerminalResolvedPathComponent::Mod(mod_def_id) => {
                        // Namespace further if it is a mod member.
                        resolved_path = self.resolve_ast_path_component(
                            component,
                            Some((
                                NonTerminalResolvedPathComponent::Mod(mod_def_id),
                                component.span(),
                            )),
                        )?;
                    }
                },
                ResolvedAstPathComponent::Terminal(_) => {
                    // Cannot namespace further
                    return Err(SemanticError::InvalidNamespaceSubject {
                        location: path[..index]
                            .iter()
                            .map(|c| c.span())
                            .reduce(|a, b| a.join(b))
                            .unwrap(),
                    });
                }
            };
        }

        Ok(resolved_path)
    }
}
