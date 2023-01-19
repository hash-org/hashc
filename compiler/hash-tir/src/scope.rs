//! Contains structures that store information about the scopes in a given
//! module, as well as the symbols in each scope.
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt,
};

use hash_source::identifier::Identifier;
use hash_utils::{new_store, new_store_key, store::Store};

use crate::{
    fmt::{ForFormatting, PrepareForFormatting, TcFormatOpts},
    location::LocationTarget,
    terms::TermId,
};

/// The visibility of a member of a const scope.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

/// The mutability of a variable in a scope.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

/// A bound member, basically type function parameters.
///
/// Should be part of a [ScopeKind::Bound] and can be set by a
/// [ScopeKind::SetBound].
///
/// The value of a bound member should always be None.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoundMember {
    /// The name of the member.
    pub name: Identifier,
    /// The type of the bound member.
    pub ty: TermId,
}

/// A set bound member.
///
/// Should be part of a [ScopeKind::SetBound].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetBoundMember {
    /// The name of the member.
    pub name: Identifier,
    /// The type of the bound member.
    pub ty: TermId,
    /// The type of the associated value with this member, this is essentially
    /// wrapped in `Rt(..)`
    pub value: TermId,
}

/// A variable scope member.
///
/// Should be part of a [ScopeKind::Variable].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VariableMember {
    pub name: Identifier,
    pub mutability: Mutability,
    pub ty: TermId,
    pub value: TermId,
}

/// A constant scope member.
///
/// Should be part of a constant [ScopeKind] or [ScopeKind::Variable].
///
/// Has a flag as to whether the member is closed (can be substituted by its
/// value -- think referential transparency).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConstantMember {
    pub name: Identifier,
    pub visibility: Visibility,
    pub ty: TermId,
    /// If this field is `None` or `Some((_, false))`, the member is open. If it
    /// is `Some(_, true)` then the member is closed.
    pub value_and_is_closed: Option<(TermId, bool)>,
}

impl ConstantMember {
    /// Get the value of the constant member
    pub fn value(&self) -> Option<TermId> {
        self.value_and_is_closed.map(|(value, _)| value)
    }

    /// Get the given property of the constant member if it is closed
    pub fn if_closed<T>(&self, f: impl FnOnce(TermId) -> Option<T>) -> Option<T> {
        match self.value_and_is_closed {
            Some((value, true)) => f(value),
            _ => None,
        }
    }

    /// Set the value of the constant member
    pub fn set_value(&mut self, new_value: TermId) {
        let _ = self.value_and_is_closed.insert((new_value, false));
    }

    /// Whether the constant member is closed.
    pub fn is_closed(&self) -> bool {
        matches!(self.value_and_is_closed, Some((_, true)))
    }
}

/// A member of a scope.
#[derive(Debug, Clone, Copy)]
pub enum Member {
    Bound(BoundMember),
    SetBound(SetBoundMember),
    Variable(VariableMember),
    Constant(ConstantMember),
}

impl Member {
    /// Get the name of the member
    pub fn name(&self) -> Identifier {
        match self {
            Member::Bound(BoundMember { name, .. })
            | Member::SetBound(SetBoundMember { name, .. })
            | Member::Variable(VariableMember { name, .. })
            | Member::Constant(ConstantMember { name, .. }) => *name,
        }
    }

    /// Get the mutability of the particular member, if any.
    pub fn mutability(&self) -> Mutability {
        match self {
            Member::Variable(VariableMember { mutability, .. }) => *mutability,
            _ => Mutability::Immutable,
        }
    }

    /// Get [LocationTarget]s referencing to the
    /// value of the declaration.
    pub fn location(&self) -> LocationTarget {
        self.value_or_ty().into()
    }

    /// Get the type of the member
    pub fn ty(&self) -> TermId {
        match self {
            Member::Bound(BoundMember { ty, .. })
            | Member::SetBound(SetBoundMember { ty, .. })
            | Member::Variable(VariableMember { ty, .. })
            | Member::Constant(ConstantMember { ty, .. }) => *ty,
        }
    }

    /// Get the value of the member
    pub fn value(&self) -> Option<TermId> {
        match self {
            Member::Bound(_) => None,
            Member::SetBound(SetBoundMember { value, .. })
            | Member::Variable(VariableMember { value, .. }) => Some(*value),
            Member::Constant(ConstantMember { value_and_is_closed, .. }) => {
                value_and_is_closed.map(|(value, _)| value)
            }
        }
    }

    /// Get the `value` [Term] of the [Member], if it doesn't exist then
    /// we fallback to getting the `ty` of the [Member].
    pub fn value_or_ty(&self) -> TermId {
        self.value().unwrap_or_else(|| self.ty())
    }

    /// Create a closed constant member with the given data and visibility.
    pub fn closed_constant(
        name: impl Into<Identifier>,
        visibility: Visibility,
        ty: TermId,
        value: TermId,
    ) -> Self {
        Member::Constant(ConstantMember {
            name: name.into(),
            ty,
            value_and_is_closed: Some((value, true)),
            visibility,
        })
    }

    /// Create an open constant member with the given data and visibility.
    pub fn open_constant(
        name: impl Into<Identifier>,
        visibility: Visibility,
        ty: TermId,
        value: TermId,
    ) -> Self {
        Member::Constant(ConstantMember {
            name: name.into(),
            ty,
            value_and_is_closed: Some((value, false)),
            visibility,
        })
    }

    /// Create an uninitialised (open) constant member with the given data and
    /// visibility.
    pub fn uninitialised_constant(
        name: impl Into<Identifier>,
        visibility: Visibility,
        ty: TermId,
    ) -> Self {
        Member::Constant(ConstantMember {
            name: name.into(),
            ty,
            value_and_is_closed: None,
            visibility,
        })
    }

    /// Create a variable member with the given data and mutability.
    pub fn variable(
        name: impl Into<Identifier>,
        mutability: Mutability,
        ty: TermId,
        value: TermId,
    ) -> Self {
        Member::Variable(VariableMember { name: name.into(), ty, mutability, value })
    }

    /// Create a bound member with the given data.
    pub fn bound(name: impl Into<Identifier>, ty: TermId) -> Self {
        Member::Bound(BoundMember { name: name.into(), ty })
    }

    /// Create a set bound member with the given data.
    pub fn set_bound(name: impl Into<Identifier>, ty: TermId, value: TermId) -> Self {
        Member::SetBound(SetBoundMember { name: name.into(), value, ty })
    }

    /// Create a new member with the given `ty` and `value`, but of the same
    /// kind as `self`.
    ///
    /// This assumes that `ty` and `value` were acquired from a member of the
    /// same kind as self, and thus value is appropriately set to `Some(_)` or
    /// `None`. Might panic otherwise.
    #[must_use]
    pub fn with_ty_and_value(&self, ty: TermId, value: Option<TermId>) -> Self {
        match *self {
            Member::Bound(bound_member) => Member::Bound(BoundMember { ty, ..bound_member }),
            Member::SetBound(set_bound) => {
                Member::SetBound(SetBoundMember { ty, value: value.unwrap(), ..set_bound })
            }
            Member::Variable(variable) => {
                Member::Variable(VariableMember { ty, value: value.unwrap(), ..variable })
            }
            Member::Constant(constant) => Member::Constant(ConstantMember {
                ty,
                value_and_is_closed: value.map(|value| (value, constant.is_closed())),
                ..constant
            }),
        }
    }
}

/// A member of a scope, i.e. a variable or a type definition, along with its
/// originating scope.
#[derive(Debug, Clone, Copy)]
pub struct ScopeMember {
    /// The represented member of this [ScopeMember]
    pub member: Member,

    /// The index of this member within the scope.
    pub index: usize,

    /// The [ScopeId] of this member.
    pub scope_id: ScopeId,
}

/// The kind of a scope.
///
/// Examples of variable scopes are:
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    /// A variable scope.
    ///
    /// Can be:
    /// - Block expression scope
    /// - Function parameter scope
    Variable,

    /// Module scope is a constant scope.
    ///
    /// Could be:
    /// - The root scope
    /// - Module block scope
    Mod,

    /// An `impl` scope kind.
    Impl,

    /// A trait scope is a constant scope,
    Trait,

    /// A bound scope.
    ///
    /// Can be:
    /// - Type function parameter scope.
    Bound,
    /// A scope that sets some bounds.
    ///
    /// Can be:
    /// - Type function "argument" scope.
    SetBound,
}

impl ScopeKind {
    pub fn is_constant(&self) -> bool {
        matches!(self, ScopeKind::Mod | ScopeKind::Trait | ScopeKind::Impl)
    }
}

/// Stores a list of members, indexed by the members' names.
///
/// Keeps insertion order.
#[derive(Debug)]
pub struct Scope {
    /// The kind of scope that is being represented.
    pub kind: ScopeKind,

    /// All defined members within the scope.
    pub members: Vec<Member>,

    /// Members names are defined within the scope.
    pub member_names: HashMap<Identifier, usize>,
}

impl Scope {
    /// Create an empty [Scope].
    pub fn empty(kind: ScopeKind) -> Self {
        Self { kind, members: Vec::new(), member_names: HashMap::new() }
    }

    /// Create a new [Scope] from the given members.
    pub fn new(kind: ScopeKind, members: impl IntoIterator<Item = Member>) -> Self {
        let members: Vec<_> = members.into_iter().collect();
        let member_names =
            members.iter().enumerate().map(|(i, member)| (member.name(), i)).collect();
        Self { kind, members, member_names }
    }

    /// Add a member to the scope, overwriting any existing member with the same
    /// name.
    pub fn add(&mut self, member: Member) -> usize {
        self.members.push(member);
        let index = self.members.len() - 1;
        self.member_names.insert(member.name(), index);
        index
    }

    /// Get a [Member] by name, returning the the [Member] and the index
    /// of the [Member] in the scope.
    pub fn get(&self, name: Identifier) -> Option<(Member, usize)> {
        let index = self.member_names.get(&name).copied()?;
        Some((self.members[index], index))
    }

    /// Whether the scope contains a member with the given name.
    pub fn contains(&self, name: Identifier) -> bool {
        self.member_names.contains_key(&name)
    }

    /// Get a member by index, asserting that it exists.
    pub fn get_by_index(&self, index: usize) -> Member {
        self.members[index]
    }

    /// Get a member by index, mutably, asserting that it exists.
    pub fn get_mut_by_index(&mut self, index: usize) -> &mut Member {
        &mut self.members[index]
    }

    /// Iterate through all the members in insertion order (oldest first).
    pub fn iter(&self) -> impl Iterator<Item = Member> + '_ {
        self.members.iter().copied()
    }

    /// Iterate through all the distinct names in the scope.
    pub fn iter_names(&self) -> impl Iterator<Item = Identifier> + '_ {
        self.member_names.keys().copied()
    }

    /// Create a copy of this scope, with the same members.
    ///
    /// This will not be kept in sync with the original scope.
    pub fn duplicate(&self) -> Self {
        Self {
            kind: self.kind,
            members: self.members.clone(),
            member_names: self.member_names.clone(),
        }
    }
}

/// A variable, which is just a name.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct Var {
    pub name: Identifier,
}

/// A bound variable, originating from some bound.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct BoundVar {
    pub name: Identifier,
}

/// A scope variable, identified by a `ScopeId` and `usize` index.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ScopeVar {
    pub name: Identifier,
    pub scope: ScopeId,
    pub index: usize,
}

/// A term with a set of bounds being assigned to specific values. The bound
/// variables should be present in the inner term
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SetBound {
    pub term: TermId,
    /// Must be [ScopeKind::SetBound]
    pub scope: ScopeId,
}

/// A set of variables which are bound in some scope.
///
/// Used to keep track of bound variables in definitions.
pub type BoundVars = HashSet<Var>;

new_store_key!(pub ScopeId);
new_store!(pub ScopeStore<ScopeId, Scope>);

/// Stores a collection of scopes, used from within
/// [LocalStorage](crate::storage::LocalStorage).
#[derive(Debug, PartialEq, Eq)]
pub struct ScopeStack {
    scopes: RefCell<Vec<ScopeId>>,
}

impl ScopeStack {
    /// Create a [ScopeStack] from a single scope.
    pub fn singular(scope_id: ScopeId) -> Self {
        Self { scopes: RefCell::new(vec![scope_id]) }
    }

    /// Create a [ScopeStack] from a collection of scopes.
    pub fn many(scopes: impl IntoIterator<Item = ScopeId>) -> Self {
        Self { scopes: RefCell::new(scopes.into_iter().collect()) }
    }

    /// Append a scope to the stack.
    pub fn append(&self, scope_id: ScopeId) {
        self.scopes.borrow_mut().push(scope_id);
    }

    /// Get the current scope ID.
    pub fn current_scope(&self) -> ScopeId {
        *self.scopes.borrow().last().unwrap()
    }

    /// Iterate up the scopes in the stack.
    ///
    /// *Warning*: It is not safe to modify the scope stack by popping scopes
    /// while iterating!
    pub fn iter_up(&self) -> impl Iterator<Item = ScopeId> + DoubleEndedIterator + '_ {
        let len = self.scopes.borrow().len();
        (0..len).rev().map(move |index| *self.scopes.borrow().get(index).unwrap())
    }

    /// Pop the current scope.
    pub fn pop_scope(&self) -> ScopeId {
        let mut scopes = self.scopes.borrow_mut();
        // Don't include the first element (root scope).
        if scopes.len() <= 1 {
            drop(scopes);
            panic!("Cannot pop root scope")
        } else {
            scopes.pop().unwrap()
        }
    }

    /// Pop the given scope.
    ///
    /// Panics if the last scope is not the same as the given ID.
    pub fn pop_the_scope(&self, expected_id: ScopeId) -> ScopeId {
        let popped = self.pop_scope();
        assert!(popped == expected_id, "Expected scope ID {expected_id:?} but got {popped:?}");
        popped
    }
}

impl PrepareForFormatting for Member {}
impl PrepareForFormatting for ScopeId {}

impl fmt::Display for ForFormatting<'_, Member> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let member = self.t;

        let mutability = match member {
            Member::Variable(var) if var.mutability == Mutability::Mutable => "mut ",
            _ => "",
        };
        let visibility = match member {
            Member::Constant(constant_member)
                if constant_member.visibility == Visibility::Public =>
            {
                "pub "
            }
            Member::Constant(constant_member)
                if constant_member.visibility == Visibility::Private =>
            {
                "priv "
            }
            _ => "",
        };
        let name = member.name();

        match (member.ty(), member.value()) {
            (ty, None) => {
                write!(
                    f,
                    "{}{}{}: {}",
                    mutability,
                    visibility,
                    name,
                    ty.for_formatting(self.global_storage)
                )?;
            }
            (ty, Some(value)) => {
                write!(
                    f,
                    "{}{}{}: {} = {}",
                    mutability,
                    visibility,
                    name,
                    ty.for_formatting(self.global_storage),
                    value.for_formatting_with_opts(
                        self.global_storage,
                        TcFormatOpts { expand: true }
                    ),
                )?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for ForFormatting<'_, ScopeId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let scope_id = self.t;

        self.global_storage.scope_store.map_fast(scope_id, |scope| {
            for member in scope.iter() {
                writeln!(f, "{};", member.for_formatting(self.global_storage))?;
            }
            Ok(())
        })
    }
}
