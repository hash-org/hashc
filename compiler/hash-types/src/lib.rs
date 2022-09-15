//! Contains type definitions that the rest of the storage and the general
//! typechecker use.
#![feature(option_result_contains, let_chains)]

pub mod arguments;
pub(crate) mod bootstrap;
pub mod builder;
pub mod fmt;
pub mod location;
pub mod mods;
pub mod nodes;
pub mod nominals;
pub mod param_list;
pub mod params;
pub mod pats;
pub mod scope;
pub mod storage;
pub mod terms;
pub mod trts;

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt::Display,
};

use hash_ast::ast::{IntLit, IntLitKind, IntTy, ParamOrigin, RangeEnd};
use hash_source::{
    constant::{InternedStr, CONSTANT_MAP},
    identifier::Identifier,
    SourceId,
};
use num_bigint::BigInt;

use crate::{
    arguments::ArgsId,
    location::LocationTarget,
    mods::ModDefId,
    nominals::NominalDefId,
    params::ParamsId,
    pats::{PatArgsId, PatId},
    scope::ScopeId,
    terms::{TermId, TermListId},
    trts::TrtDefId,
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
    pub name: Identifier,
    pub ty: TermId,
}

/// A set bound member.
///
/// Should be part of a [ScopeKind::SetBound].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetBoundMember {
    pub name: Identifier,
    pub ty: TermId,
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
/// Should be part of a [ScopeKind::Constant] or [ScopeKind::Variable].
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
    /// A constant scope.
    ///
    /// Can be:
    /// - The root scope
    /// - Module block scope
    /// - Trait block scope
    /// - Impl block scope
    Constant,
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

/// Trait to be implemented by primitives which contain a `name` field that is
/// an optional identifier.
pub trait GetNameOpt {
    /// Get the name of [Self], which should be an [Option<Identifier>].
    fn get_name_opt(&self) -> Option<Identifier>;
}

/// A borrowed or owned list of parameters, generic over the parameter type.
#[derive(Debug, Clone)]
pub struct ParamList<'p, ParamType: Clone> {
    params: Cow<'p, [ParamType]>,
    origin: ParamOrigin,
}

impl<ParamType: GetNameOpt + Clone> ParamList<'static, ParamType> {
    /// Create a new [ParamList] from the given vec of parameters and origin.
    pub fn new_owned(params: Vec<ParamType>, origin: ParamOrigin) -> Self {
        Self { params: Cow::Owned(params), origin }
    }
}

impl<'p, ParamType: GetNameOpt + Clone> ParamList<'p, ParamType> {
    /// Create a new [ParamList] from the given slice of parameters.
    pub fn new(params: &'p [ParamType], origin: ParamOrigin) -> Self {
        Self { params: Cow::Borrowed(params), origin }
    }

    /// Get the parameters as a positional slice
    pub fn positional(&self) -> &[ParamType] {
        self.params.as_ref()
    }

    /// Get the length of the parameters.
    pub fn len(&self) -> usize {
        self.params.len()
    }

    /// Borrow the parameters as a borrowed type.
    pub fn borrowed<'s: 'p>(&'s self) -> ParamList<'s, ParamType> {
        Self::new(self.params.as_ref(), self.origin)
    }

    /// Check if the [ParamList] is empty
    pub fn is_empty(&self) -> bool {
        self.params.is_empty()
    }

    /// Get the origin of the parameters.
    pub fn origin(&self) -> ParamOrigin {
        self.origin
    }

    /// Turn [Self] into the parameters as a positional vector.
    pub fn into_positional(self) -> Vec<ParamType> {
        self.params.into_owned()
    }

    /// Get a parameter by name.
    pub fn get_by_name(&self, name: Identifier) -> Option<(usize, &ParamType)> {
        self.params.iter().enumerate().find_map(|(i, param)| {
            if param.get_name_opt().contains(&name) {
                Some((i, param))
            } else {
                None
            }
        })
    }

    /// Get all the names of the fields within the [ParamList
    pub fn names(&self) -> HashSet<Identifier> {
        HashSet::from_iter(self.params.iter().flat_map(|param| param.get_name_opt()))
    }
}

/// An argument to a parameter.
#[derive(Debug, Clone, Hash, Copy)]
pub struct Arg {
    pub name: Option<Identifier>,
    pub value: TermId,
}

impl GetNameOpt for Arg {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A list of arguments.
pub type Args<'p> = ParamList<'p, Arg>;

/// A parameter, declaring a potentially named variable with a given type and
/// default value.
#[derive(Debug, Clone, Hash, Copy)]
pub struct Param {
    pub name: Option<Identifier>,
    pub ty: TermId,
    pub default_value: Option<TermId>,
}

impl GetNameOpt for Param {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A list of parameters.
pub type Params<'p> = ParamList<'p, Param>;

/// A set of variables which are bound in some scope.
///
/// Used to keep track of bound variables in definitions.
pub type BoundVars = HashSet<Var>;

/// The origin of a module: was it defined in a `mod` block, an anonymous `impl`
/// block, or an `impl Trait` block?
#[derive(Debug, Clone, Copy, Hash)]
pub enum ModDefOrigin {
    /// Defined as a trait implementation (for the given term that should
    /// resolve to a trait value).
    TrtImpl(TermId),
    /// Defined as an anonymous implementation.
    AnonImpl,
    /// Defined as a module (`mod` block).
    Mod,
    /// Defined as a file module or interactive.
    Source(SourceId),
}

/// A module definition, which is of a given origin, has a binding name, and
/// contains some constant members.
#[derive(Debug, Clone)]
pub struct ModDef {
    pub name: Option<Identifier>,
    pub origin: ModDefOrigin,
    pub members: ScopeId,
}

/// The fields of a struct.
#[derive(Debug, Clone, Copy)]
pub enum StructFields {
    /// An explicit set of fields, as a set of parameters.
    Explicit(ParamsId),
    /// The struct does not have any accessible parameters.
    ///
    /// This is used for core language definitions that will be filled in later
    /// in the compiler pipeline.
    Opaque,
}

/// A struct definition, containing a binding name and a set of fields.
#[derive(Debug, Clone, Copy)]
pub struct StructDef {
    pub name: Option<Identifier>,
    pub fields: StructFields,
}

/// An enum variant, containing a variant name and a set of fields.
///
/// Structurally the same as a struct.
#[derive(Debug, Clone, Copy)]
pub struct EnumVariant {
    pub name: Identifier,
    pub fields: Option<ParamsId>,
}

/// An enum definition, containing a binding name and a set of variants.
#[derive(Debug, Clone)]
pub struct EnumDef {
    /// The name of the `EnumDef`, useful for error reporting
    pub name: Option<Identifier>,
    /// All of the defined variants that occur within the [EnumDef].
    pub variants: HashMap<Identifier, EnumVariant>,
}

/// A trait definition, containing a binding name and a set of constant members.
#[derive(Debug, Clone, Copy)]
pub struct TrtDef {
    pub name: Option<Identifier>,
    pub members: ScopeId,
}

/// A unit definition.
///
/// This is a nominal type with a single constant constructor.
#[derive(Debug, Clone, Copy)]
pub struct UnitDef {
    pub name: Option<Identifier>,
}

/// A nominal definition, which for now is either a struct, an enum, or a unit.
#[derive(Debug, Clone)]
pub enum NominalDef {
    /// A struct definition.
    Struct(StructDef),
    /// @@Todo: delete
    Enum(EnumDef),
    /// A unit definition.
    Unit(UnitDef),
}

impl NominalDef {
    /// Get the name of the [NominalDef], if any.
    pub fn name(&self) -> Option<Identifier> {
        match self {
            NominalDef::Struct(def) => def.name,
            NominalDef::Enum(def) => def.name,
            NominalDef::Unit(def) => def.name,
        }
    }
}

/// A tuple type, containing parameters as members.
#[derive(Debug, Clone, Copy)]
pub struct TupleTy {
    pub members: ParamsId,
}

/// A function type, with a set of input parameters and a return type.
///
/// All the parameter types and return type must be level 0
#[derive(Debug, Clone, Copy)]
pub struct FnTy {
    pub params: ParamsId,
    pub return_ty: TermId,
}

/// A type function type.
///
/// A type function is a compile-time function that works on types. Type
/// function return values can be level 0, level 1 or level 2. It has a general
/// set of "base" parameters and return type.
///
/// These are refined in the `cases` field, which provides conditional values
/// for the return value of the function, based on what the arguments are.
///
/// For example, consider:
///
/// ```ignore
/// Dog := <T> => struct(foo: T);
///
/// Dog ~= <T: Hash> => impl Hash {
///     hash = (self) => self.foo.hash();
/// };
///
/// Dog ~= <T: Hash ~ Eq> => impl FindInHashMap {
///     ...
/// };
/// ```
///
/// Then, the definition of the type function `Dog` would look something like:
///
/// ```ignore
/// TyFnTy {
///     general_params = (T: Term::Level2(Ty)),
///     general_return_ty = Term::Level2(Ty),
///     cases = {
///         (T: Term::Level2(Ty)) -> Term::Level2(Ty) => Term::NominalDef(DogStructDef),
///         (T: Term::Level2(Ty)(HashTraitDef)) -> Term::Level2(Ty)(HashTraitDef) => Term::Merge([
///             Term::NominalDef(DogStructDef),
///             Term::Mod(
///                 origin=TraitImpl(Term::Trt(HashTraitDef)),
///                 members=..
///             ),
///         ]),
///         (T: Ty::Merge([Term::Level2(Ty)(HashTraitDef), Term::Level2(Ty)(EqTraitDef)]))
///             -> Term::Level2(Ty)(FindInHashMapTraitDef) =>
///             => Term::Merge([
///                 Term::NominalDef(DogStructDef),
///                 Term::Mod(
///                     origin=TraitImpl(Term::Trt(FindInHashMapTraitDef)),
///                     members=..
///                 ),
///             ])
///     }
/// }
/// ```
///
/// At any point, the resolved type of `Dog<T>` is the merged type of the return
/// type of each case which matches `T`. In other words, cases are not
/// short-circuiting; they are all evaluated and then combined.
///
/// The `general_return_ty` field is always a supertype of the return type of
/// each case.
#[derive(Debug, Clone)]
pub struct TyFn {
    /// An optional name for the type function, if it is directly assigned to a
    /// binding.
    pub name: Option<Identifier>,
    pub general_params: ParamsId,
    pub general_return_ty: TermId,
    pub cases: Vec<TyFnCase>,
}

/// Represents a case in a type function, for some subset of its
/// `general_params`, to some specific return type and refined return value.
///
/// The `value` property of each [Param] in the `params` field represents types
/// which have been set, for example:
///
/// ```ignore
/// Dog<str> ~= impl Conv<str> {
///     conv = (self) => "Dog with foo=" + conv(self.foo);
/// };
/// ```
///
/// This translates to a case:
/// ```ignore
/// (T: Term::Level2(Ty) = Term::Level1(NominalDef(strDefId)))
///     -> Term::TyFnCall(ConvValue (a type fn), [Term::Level1(NominalDef(strDefId))])
///     => Term::Merge([
///         Term::TyFnCall(DogValue (a type fn), [Term::Level1(NominalDef(strDefId))]),
///         Term::ModDef(
///             origin=TraitImpl(Term::TyFnCall(ConvValue (a type fn),
///             [Term::Level1(NominalDef(strDefId))])),
///             members=...
///         )
///     ])
/// ```
///
/// The case's `return_ty` must always be able to unify with the target
/// `general_return_ty`, and the type parameters should be able to each unify
/// with the target `general_params`, of the parent [TyFn].
#[derive(Debug, Clone)]
pub struct TyFnCase {
    pub params: ParamsId,
    pub return_ty: TermId,
    pub return_value: TermId,
}

/// Not yet resolved.
///
/// The resolution ID is incremented for each new unresolved term.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct UnresolvedTerm {
    pub resolution_id: ResolutionId,
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

/// The action of applying a set of arguments to a type function.
///
/// This essentially creates a lambda calculus within the Hash type system,
/// which allows it to express arbitrary programs.
///
/// When this type is unified with another type, the function is applied by
/// first instantiating its return value over its type parameters, and then
/// unifying the instantiated type parameters with the given type arguments of
/// the function (the `args` field).
#[derive(Debug, Clone)]
pub struct TyFnCall {
    pub subject: TermId,
    pub args: ArgsId,
}

/// The type of a type function, for example:
///
/// ```ignore
/// T: <X: Type> -> Type
/// ```
///
/// would be
///
/// ```ignore
/// name: "T",
/// ty: Term::TyFnTy(params = [(name="X", ty=Term::Level2(Ty))], return_ty=Term::Level2(Ty))
/// value: Term::Unset,
/// ```
#[derive(Debug, Clone)]
pub struct TyFnTy {
    pub params: ParamsId,
    pub return_ty: TermId,
}

/// An enum variant value, consisting of a [NominalDefId] pointing to an enum,
/// as well as the variant of the enum in the form of an [Identifier].
///
/// Has a level 0 type.
#[derive(Debug, Clone, Copy)]
pub struct EnumVariantValue {
    pub enum_def_id: NominalDefId,
    pub variant_name: Identifier,
}

/// The operator used to perform a member access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessOp {
    /// The `::` accessor (namespace operator).
    ///
    /// Works for modules, traits, enums.
    Namespace,
    /// The `.` accessor (property operator).
    ///
    /// Works for structs, tuples.
    Property,
}

impl Display for AccessOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccessOp::Namespace => write!(f, "namespace member"),
            AccessOp::Property => write!(f, "property"),
        }
    }
}

/// Represents which kind of field is being accessed
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Field {
    Named(Identifier),
    Numeric(usize),
}

impl Display for Field {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Field::Named(name) => write!(f, "{name}"),
            Field::Numeric(index) => write!(f, "{index}"),
        }
    }
}

impl From<&str> for Field {
    fn from(index: &str) -> Self {
        Field::Named(index.into())
    }
}

impl From<Identifier> for Field {
    fn from(index: Identifier) -> Self {
        Field::Named(index)
    }
}

impl From<usize> for Field {
    fn from(ident: usize) -> Self {
        Field::Numeric(ident)
    }
}

/// An access term, which is of the form X::Y, where X is a term and Y is an
/// identifier.
///
/// Has level N where N is the level of the Y property of X.
#[derive(Debug, Clone, Copy)]
pub struct AccessTerm {
    pub subject: TermId,
    pub name: Field,
    pub op: AccessOp,
}

/// A literal term, which is level 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LitTerm {
    Str(InternedStr),
    Int { value: BigInt, kind: IntTy },
    Char(char),
}

impl From<&str> for LitTerm {
    fn from(s: &str) -> Self {
        LitTerm::Str(s.into())
    }
}

impl From<String> for LitTerm {
    fn from(s: String) -> Self {
        LitTerm::Str(s.into())
    }
}

impl From<IntLit> for LitTerm {
    fn from(lit: IntLit) -> Self {
        let value = CONSTANT_MAP.lookup_int_constant(lit.value);

        match lit.kind {
            IntLitKind::Suffixed(kind) => LitTerm::Int { value: value.to_big_int(), kind },
            IntLitKind::Unsuffixed => LitTerm::Int { value: value.to_big_int(), kind: IntTy::I32 },
        }
    }
}

impl From<char> for LitTerm {
    fn from(s: char) -> Self {
        LitTerm::Char(s)
    }
}

/// A level 3 term.
///
/// Type of: traits, for example: `trait(..)`.
/// Value of: nothing.
#[derive(Debug, Clone)]
pub enum Level3Term {
    /// The type that traits have
    TrtKind,
}

/// A level 2 term.
///
/// Type of: types, for example: `struct(..)`, `enum(..)`, `mod {..}`, `impl
/// {..}`. Value of: traits, for example `trait(..)`.
#[derive(Debug, Clone)]
pub enum Level2Term {
    // ---- Level 2 ---- the term that is a return term of trait(..)
    /// A trait term.
    Trt(TrtDefId),
    /// A type that is runtime instantiable, i.e. sized.
    SizedTy,
    /// Basically a trait term that all types implement, i.e. the trait that is
    /// a supertrait to all other traits.
    AnyTy,
}

/// A level 1 term.
///
/// Type of: values, for example: `3`, `"test"`, `[1, 2, 3]`, `Dog(name="Bob")`.
/// Value of: types, for example `struct(..)`, `enum(..)`, `mod {..}`, `(a: A)
/// -> B` etc.
#[derive(Debug, Clone)]
pub enum Level1Term {
    /// Modules or impl blocks.
    ///
    /// Modules and trait implementations, as well as anonymous implementations,
    /// are treated as types, but do not have instance values.
    ///
    /// Information about the origin of each module definition can be found in
    /// its corresponding [ModDef] struct.
    ModDef(ModDefId),

    /// A nominal type definition, either a struct or an enum.
    NominalDef(NominalDefId),

    /// Tuple type.
    Tuple(TupleTy),

    /// Function type.
    Fn(FnTy),
}

// Represents a function call, with a level 0 subject and level 0 arguments.
//
// The subject must be either a `Rt(Fn(..))`, or an `FnLit(..)`.
#[derive(Debug, Clone, Copy)]
pub struct FnCall {
    pub subject: TermId,
    pub args: ArgsId,
}

/// Represents a function literal, with a function type, as well as a return
/// value.
#[derive(Debug, Clone, Copy)]
pub struct FnLit {
    pub fn_ty: TermId,
    pub return_value: TermId,
}

/// A tuple literal, containing arguments as members.
#[derive(Debug, Clone, Copy)]
pub struct TupleLit {
    pub members: ArgsId,
}

/// A constructed term represents a constructed value that is some constructed
/// value which originated as being a struct.
#[derive(Debug, Clone, Copy)]
pub struct ConstructedTerm {
    /// The term of the subject within the constructed term
    pub subject: TermId,
    /// The constructor arguments
    pub members: ArgsId,
}

/// A level 0 term.
///
/// Type of: nothing.
/// Value of: values, for example `3`, `Result::Ok(3)`, etc.
#[derive(Debug, Clone)]
pub enum Level0Term {
    /// A runtime value, has some Level 1 term as type (the inner data).
    Rt(TermId),

    /// A function call.
    FnCall(FnCall),

    /// A function literal.
    FnLit(FnLit),

    /// An enum variant, which is either a constant term or a function value.
    EnumVariant(EnumVariantValue),

    /// A unit value, of the given unit type definition (inner `NominalDefId`
    /// should point to a unit).
    Unit(NominalDefId),

    /// Tuple literal.
    Tuple(TupleLit),

    /// A literal term
    Lit(LitTerm),

    /// A constructed term
    Constructed(ConstructedTerm),
}

/// The subject of a substitution: an unresolved term.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum SubVar {
    Unresolved(UnresolvedTerm),
}

impl From<UnresolvedTerm> for SubVar {
    fn from(unresolved: UnresolvedTerm) -> Self {
        SubVar::Unresolved(unresolved)
    }
}

impl From<SubVar> for Term {
    fn from(subject: SubVar) -> Self {
        match subject {
            SubVar::Unresolved(unresolved) => Term::Unresolved(unresolved),
        }
    }
}

/// A substitution containing pairs of `(SubSubject, TermId)` to be applied to a
/// term.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Sub {
    data: HashMap<SubVar, TermId>,
}

impl Sub {
    /// Create an empty substitution.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Create a substitution from a [HashMap<SubSubject, TermId>].
    pub fn from_map(map: HashMap<SubVar, TermId>) -> Self {
        Self { data: map }
    }

    /// Create a substitution from pairs of `(SubSubject, TermId)`.
    pub fn from_pairs(pairs: impl IntoIterator<Item = (impl Into<SubVar>, TermId)>) -> Self {
        Self { data: pairs.into_iter().map(|(from, to)| (from.into(), to)).collect() }
    }

    /// Get the substitution for the given [SubVar], if any.
    pub fn get_sub_for(&self, subject: SubVar) -> Option<TermId> {
        self.data.get(&subject).copied()
    }

    /// Check whether the substitution is empty
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Get all the subjects (i.e. the domain) of the substitution as an
    /// iterator.
    pub fn domain(&self) -> impl Iterator<Item = SubVar> + '_ {
        self.data.keys().copied()
    }

    /// Get all the targets (i.e. the range) of the substitution as an iterator.
    pub fn range(&self) -> impl Iterator<Item = TermId> + '_ {
        self.data.values().copied()
    }

    /// Get the pairs `(SubSubject, TermId)` of the substitution as an iterator.
    pub fn pairs(&self) -> impl Iterator<Item = (SubVar, TermId)> + '_ {
        self.data.iter().map(|(&subject, &term)| (subject, term))
    }

    /// Get the pairs `(SubSubject, TermId)` of the substitution as a map.
    pub fn map(&self) -> &HashMap<SubVar, TermId> {
        &self.data
    }

    /// Add the given pair `subject -> term` to the substitution.
    pub fn add_pair(&mut self, subject: SubVar, term: TermId) {
        self.data.insert(subject, term);
    }

    /// Extend the substitution with pairs from the given one, consuming self.
    pub fn with_extension(mut self, other: &Sub) -> Self {
        self.extend(other);
        self
    }

    /// Extend the substitution with pairs from the given one.
    ///
    /// This is a naive implementation which does not perform any unification.
    /// For substitution unification, see the `crate::ops::unify` module.
    pub fn extend(&mut self, other: &Sub) {
        self.data.extend(other.pairs());
    }
}

/// A term as well as a substitution to apply to it.
#[derive(Debug, Clone)]
pub struct AppSub {
    pub sub: Sub,
    pub term: TermId,
}

/// The basic data structure of a compile-time term.
#[derive(Debug, Clone)]
pub enum Term {
    // ---- Derived ----
    /// Access a member of a term.
    ///
    /// Is level N, where N is the level of the resultant access.
    Access(AccessTerm),

    /// A variable, referencing either a scope variable or a bound variable.
    ///
    /// Is level N-1, where N is the level of the type of the variable in the
    /// context
    Var(Var),

    /// A variable that corresponds to some scope member.
    ///
    /// Is level N-1, where N is the level of the type of the variable in the
    /// context
    ScopeVar(ScopeVar),

    /// A bound variable.
    ///
    /// Is level N-1, where N is the level of the type of the variable in the
    /// context
    BoundVar(BoundVar),

    /// Merge of multiple terms.
    ///
    /// Inner types must have the same level. Merging is also idempotent,
    /// associative, and commutative.
    ///
    /// Is level N, where N is the level of the inner types.
    Merge(TermListId),

    /// Union of multiple types.
    ///
    /// Inner types must have the same level. Union is also idempotent,
    /// associative, and commutative.
    ///
    /// Is level N, where N is the level of the inner types.
    Union(TermListId),

    /// A type function term.
    ///
    /// Is level N, where N is the level of the return term of the function.
    TyFn(TyFn),

    /// Type function type.
    ///
    /// Is level N, where N is the level of the return term of the function.
    TyFnTy(TyFnTy),

    /// A type function application.
    ///
    /// Is level N, where N is the level of the resultant application.
    TyFnCall(TyFnCall),

    /// Setting some bounds of an inner term.
    ///
    /// Is level N, where N is the level of the inner term after the
    /// substitution has been applied.
    SetBound(SetBound),

    /// Type of a term
    ///
    /// Simplifies to calling `ty_of_term` on the inner term.
    TyOf(TermId),

    /// Not yet resolved.
    ///
    /// Unknown level (but not 0), to be determined by unification.
    Unresolved(UnresolvedTerm),

    /// A level 3 term.
    Level3(Level3Term),

    /// A level 2 term.
    Level2(Level2Term),

    /// A level 1 term.
    Level1(Level1Term),

    /// A level 0 term.
    Level0(Level0Term),

    /// The only level 4 term, which is the "endpoint" of the typing hierarchy.
    /// This is the type of "TraitKind" and "TyFnTy".
    Root,
}

/// A binding pattern, which is essentially a declaration left-hand side.
#[derive(Clone, Debug, Copy)]
pub struct BindingPat {
    pub name: Identifier,
    pub mutability: Mutability,
    pub visibility: Visibility,
}

/// An access pattern is the equivalent of an access expression which denotes
/// accessing symbols within some namespace. The `property` that is accessed
/// from the subject.
#[derive(Clone, Debug, Copy)]
pub struct AccessPat {
    /// The subject that is to be accessed
    pub subject: PatId,
    /// The property that is accessed from the `subject`
    pub property: Identifier,
}

/// A constant pattern is essentially a bind pattern that can be resolved within
/// the current scope of the pattern. This used to support [Pat::Access] working
/// the resolution machinery.
#[derive(Clone, Debug, Copy)]
pub struct ConstPat {
    /// The resolved term of the constant.
    pub term: TermId,
}

/// A pattern of a parameter, used for tuple patterns and constructor patterns.
#[derive(Clone, Debug, Copy)]
pub struct PatArg {
    pub name: Option<Identifier>,
    pub pat: PatId,
}

impl GetNameOpt for PatArg {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A pattern of parameters.
pub type PatArgs<'p> = ParamList<'p, PatArg>;

/// A constructor pattern, used for enum variants and structs.
#[derive(Clone, Debug, Copy)]
pub struct ConstructorPat {
    pub subject: TermId,
    /// If `params` is `None`, it means that the constructor has no parameters;
    /// it is a unit.
    pub args: PatArgsId,
}

/// A list pattern
#[derive(Clone, Debug, Copy)]
pub struct ListPat {
    /// The element type of the list
    pub list_element_ty: TermId,
    /// Patterns for the list elements
    pub element_pats: PatArgsId,
}

/// Spread pattern
#[derive(Clone, Debug, Copy)]
pub struct SpreadPat {
    /// Associated bind to the spread
    pub name: Option<Identifier>,
}

/// A conditional pattern, containing a pattern and an condition.
#[derive(Clone, Debug, Copy)]
pub struct IfPat {
    pub pat: PatId,
    pub condition: TermId,
}

/// A module pattern, containing a list of patterns to be used to match module
/// members.
#[derive(Clone, Debug, Copy)]
pub struct ModPat {
    pub members: PatArgsId,
}

/// A range pattern containing two terms `lo` and `hi`, and
/// an `end` kind which specifies if the [RangePat] is a
/// closed range or not.
///
/// The `lo` and `hi` values must be `Term::Level0(Level0Term::Lit)`.
#[derive(Clone, Debug, Copy)]
pub struct RangePat {
    /// Start value of the range, must be a literal term.
    pub lo: TermId,
    /// End value of the range, must be a literal term.
    pub hi: TermId,
    /// If the range is closed or not.
    pub end: RangeEnd,
}

/// Represents a pattern at the typechecking stage.
#[derive(Clone, Debug)]
pub enum Pat {
    /// Binding pattern.
    Binding(BindingPat),
    /// Access pattern.
    Access(AccessPat),
    /// Resolved binding pattern.
    Const(ConstPat),
    /// A range pattern `2..5
    Range(RangePat),
    /// Literal pattern, of the given term.
    ///
    /// The inner term must be `Term::Level0(Level0Term::Lit)`.
    Lit(TermId),
    /// Tuple pattern.
    Tuple(PatArgsId),
    /// Module pattern.
    Mod(ModPat),
    /// Constructor pattern.
    Constructor(ConstructorPat),
    /// List pattern
    List(ListPat),
    /// Spread pattern, which represents a pattern that captures a range of
    /// items within a list pattern
    Spread(SpreadPat),
    /// A set of patterns that are OR-ed together. If any one of them matches
    /// then the whole pattern matches.
    Or(Vec<PatId>),
    /// A conditional pattern.
    If(IfPat),
    /// A wildcard pattern, ignoring the subject and always matching.
    Wild,
}

impl Pat {
    /// Check if the pattern is of the [Pat::Spread] variant.
    pub fn is_spread(&self) -> bool {
        matches!(self, Pat::Spread(_))
    }

    /// Check if the pattern is of the [Pat::Spread] variant.
    pub fn is_bind(&self) -> bool {
        matches!(self, Pat::Binding(_))
    }
}

/// The ID of a [UnresolvedTerm], separate from its [TermId], stored in
/// [terms::TermStore].
///
/// This needs to be separate from [TermId] so that if a type is copied (and new
/// IDs are generated for its members) the identity of the unknown variables
/// remains the same as in the original type.
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct ResolutionId(pub usize);

impl Display for ResolutionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}