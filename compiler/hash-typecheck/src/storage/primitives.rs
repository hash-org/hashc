//! Contains type definitions that the rest of the storage and the general
//! typechecker use.
use hash_ast::ast::ParamOrigin;
use hash_source::{identifier::Identifier, SourceId};
use num_bigint::BigInt;
use slotmap::new_key_type;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
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

/// A member declaration either containing only a type, only a value, or both.
#[derive(Copy, Clone, Debug)]
pub enum MemberData {
    Uninitialised { ty: TermId },
    InitialisedWithTy { ty: TermId, value: TermId },
    InitialisedWithInferredTy { value: TermId },
}

impl MemberData {
    /// Get the type of the member, if it exists.
    pub fn ty(&self) -> Option<TermId> {
        match self {
            MemberData::Uninitialised { ty } => Some(*ty),
            MemberData::InitialisedWithTy { ty, .. } => Some(*ty),
            MemberData::InitialisedWithInferredTy { .. } => None,
        }
    }

    /// Get the value of the member, if it exists.
    pub fn value(&self) -> Option<TermId> {
        match self {
            MemberData::Uninitialised { .. } => None,
            MemberData::InitialisedWithTy { value, .. } => Some(*value),
            MemberData::InitialisedWithInferredTy { value } => Some(*value),
        }
    }

    /// Turn the given type and value into a [MemberData].
    pub fn from_ty_and_value(ty: Option<TermId>, value: Option<TermId>) -> Self {
        match (ty, value) {
            (Some(ty), Some(value)) => MemberData::InitialisedWithTy { ty, value },
            (Some(ty), None) => MemberData::Uninitialised { ty },
            (None, Some(value)) => MemberData::InitialisedWithInferredTy { value },
            (None, None) => panic!("Got None for both ty and value when creating MemberData"),
        }
    }
}

/// The kind of a member: either a bound member or a stack member.
/// @@Todo: distinction between actual stack and "constant stack"
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemberKind {
    /// A bound member, basically type function parameters.
    Bound,
    /// A stack member (basically all declared variables).
    Stack {
        /// The amount of assignments are left until the member has finished
        /// initialising (== closed).
        assignments_until_closed: usize,
    },
}

/// A member of a scope, i.e. a variable or a type definition.
#[derive(Debug, Clone, Copy)]
pub struct Member {
    pub name: Identifier,
    pub data: MemberData,
    pub visibility: Visibility,
    pub mutability: Mutability,
    pub kind: MemberKind,
}

impl Member {
    /// Create a closed stack member with the given data.
    pub fn closed_stack(
        name: Identifier,
        visibility: Visibility,
        mutability: Mutability,
        data: MemberData,
    ) -> Self {
        Member {
            name,
            data,
            visibility,
            mutability,
            kind: MemberKind::Stack { assignments_until_closed: 0 },
        }
    }

    /// Create a bound member with the given data.
    pub fn bound(
        name: Identifier,
        visibility: Visibility,
        mutability: Mutability,
        data: MemberData,
    ) -> Self {
        Member { name, data, visibility, mutability, kind: MemberKind::Bound }
    }

    /// Whether the member is closed (no assignments remaining) and not a bound
    /// member.
    pub fn is_closed_and_non_bound(&self) -> bool {
        matches!(self.kind, MemberKind::Stack { assignments_until_closed: 0 })
    }
}

/// A member of a scope, i.e. a variable or a type definition.
#[derive(Debug, Clone, Copy)]
pub struct ScopeMember {
    pub member: Member,
    pub index: usize,
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
#[derive(Debug, Clone)]
pub struct Scope {
    pub kind: ScopeKind,
    pub members: Vec<Member>,
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
        let member_names = members.iter().enumerate().map(|(i, member)| (member.name, i)).collect();
        Self { kind, members, member_names }
    }

    /// Add a member to the scope, overwriting any existing member with the same
    /// name.
    pub fn add(&mut self, member: Member) -> usize {
        self.members.push(member);
        let index = self.members.len() - 1;

        self.member_names.insert(member.name, index);
        index
    }

    /// Get a member by name.
    pub fn get(&self, member_name: Identifier) -> Option<(Member, usize)> {
        let index = self.member_names.get(&member_name).copied()?;

        Some((self.members[index], index))
    }

    /// Whether the scope contains a member with the given name.
    pub fn contains(&self, member_name: Identifier) -> bool {
        self.member_names.contains_key(&member_name)
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
}

/// Trait to be implemented by primitives which contain a `name` field that is
/// an optional identifier.
pub trait GetNameOpt {
    /// Get the name of [Self], which should be an [Option<Identifier>].
    fn get_name_opt(&self) -> Option<Identifier>;
}

/// A list of parameters, generic over the parameter type.
///
/// Provides ways to store and get a parameter by its name or index.
#[derive(Debug, Clone)]
pub struct ParamList<ParamType: Clone> {
    params: Vec<ParamType>,
    name_map: HashMap<Identifier, usize>,
    origin: ParamOrigin,
}

impl<ParamType: GetNameOpt + Clone> ParamList<ParamType> {
    /// Create a new [ParamList] from the given list of parameters.
    pub fn new(params: Vec<ParamType>, origin: ParamOrigin) -> Self {
        let name_map = params
            .iter()
            .enumerate()
            .filter_map(|(i, param)| Some((param.get_name_opt()?, i)))
            .collect();

        Self { params, name_map, origin }
    }

    /// Get the parameters as a positional slice
    pub fn positional(&self) -> &[ParamType] {
        &self.params
    }

    /// Get the origin of the parameters.
    pub fn origin(&self) -> ParamOrigin {
        self.origin
    }

    /// Get the length of the parameters.
    pub fn len(&self) -> usize {
        self.params.len()
    }

    /// Check if the [ParamList] is empty
    pub fn is_empty(&self) -> bool {
        self.params.is_empty()
    }

    /// Turn [Self] into the parameters as a positional vector.
    pub fn into_positional(self) -> Vec<ParamType> {
        self.params
    }

    /// Get a parameter by name.
    pub fn get_by_name(&self, name: Identifier) -> Option<(usize, &ParamType)> {
        let param_index = *self.name_map.get(&name)?;
        Some((param_index, self.positional().get(param_index)?))
    }

    /// Get all the names of the fields within the [ParamList
    pub fn names(&self) -> HashSet<Identifier> {
        self.name_map.keys().cloned().collect::<HashSet<_>>()
    }
}

/// Build a [ParamList] from an iterator of [ParamType].
impl<ParamType: GetNameOpt + Clone> FromIterator<ParamType> for ParamList<ParamType> {
    fn from_iter<T: IntoIterator<Item = ParamType>>(iter: T) -> Self {
        Self::new(iter.into_iter().collect(), ParamOrigin::Unknown)
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
pub type Args = ParamList<Arg>;

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
pub type Params = ParamList<Param>;

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
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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
    pub fields: ParamsId,
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
#[derive(Debug, Clone)]
pub struct TrtDef {
    pub name: Option<Identifier>,
    pub members: ScopeId,
}

/// A nominal definition, which for now is either a struct or an enum.
#[derive(Debug, Clone)]
pub enum NominalDef {
    Struct(StructDef),
    Enum(EnumDef),
}

impl NominalDef {
    /// Get the name of the [NominalDef], if any.
    pub fn name(&self) -> Option<Identifier> {
        match self {
            NominalDef::Struct(def) => def.name,
            NominalDef::Enum(def) => def.name,
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
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ScopeVar {
    pub name: Identifier,
    pub scope: ScopeId,
    pub index: usize,
}

/// A term with a set of bounds being assigned to specific values. The bound
/// variables should be present in the inner term
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
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

/// An access term, which is of the form X::Y, where X is a term and Y is an
/// identifier.
///
/// Has level N where N is the level of the Y property of X.
#[derive(Debug, Clone)]
pub struct AccessTerm {
    pub subject: TermId,
    pub name: Identifier,
    pub op: AccessOp,
}

/// A literal term, which is level 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LitTerm {
    Str(String),
    Int(BigInt),
    Char(char),
}

impl From<&str> for LitTerm {
    fn from(s: &str) -> Self {
        LitTerm::Str(s.to_owned())
    }
}

impl From<String> for LitTerm {
    fn from(s: String) -> Self {
        LitTerm::Str(s)
    }
}

impl From<u64> for LitTerm {
    fn from(s: u64) -> Self {
        LitTerm::Int(s.into())
    }
}

impl From<i64> for LitTerm {
    fn from(s: i64) -> Self {
        LitTerm::Int(s.into())
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

    /// Get the substitution for the given [SubSubject], if any.
    pub fn get_sub_for(&self, subject: SubVar) -> Option<TermId> {
        self.data.get(&subject).copied()
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
    Merge(Vec<TermId>),

    /// Union of multiple types.
    ///
    /// Inner types must have the same level. Union is also idempotent,
    /// associative, and commutative.
    ///
    /// Is level N, where N is the level of the inner types.
    Union(Vec<TermId>),

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
pub struct PatParam {
    pub name: Option<Identifier>,
    pub pat: PatId,
}

impl GetNameOpt for PatParam {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A pattern of parameters.
pub type PatParams = ParamList<PatParam>;

/// A constructor pattern, used for enum variants and structs.
#[derive(Clone, Debug, Copy)]
pub struct ConstructorPat {
    pub subject: TermId,
    /// If `params` is `None`, it means that the constructor has no parameters;
    /// it is a unit.
    pub params: PatParamsId,
}

/// A list pattern
#[derive(Clone, Debug, Copy)]
pub struct ListPat {
    /// The inner term of the list.
    pub term: TermId,
    /// Inner list of patterns
    pub inner: PatParamsId,
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
    pub members: PatParamsId,
}

/// Represents a pattern in the language.
#[derive(Clone, Debug)]
pub enum Pat {
    /// Binding pattern.
    Binding(BindingPat),
    /// Access pattern.
    Access(AccessPat),
    /// Resolved binding pattern.
    Const(ConstPat),
    /// Literal pattern, of the given term.
    ///
    /// The inner term must be `Term::Level0(Level0Term::Lit)`.
    Lit(TermId),
    /// Tuple pattern.
    Tuple(PatParamsId),
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
    Ignore,
}

// IDs for all the primitives to be stored on mapped storage.

new_key_type! {
    /// The ID of a [TrtDef] stored in [super::trts::TrtDefStore].
    pub struct TrtDefId;
}

new_key_type! {
    /// The ID of a [NominalDef] stored in [super::nominals::NominalDefStore].
    pub struct NominalDefId;
}

new_key_type! {
    /// The ID of a [ModDef] stored in [super::mods::ModDefStore].
    pub struct ModDefId;
}

new_key_type! {
    /// The ID of a [Term] stored in [super::values::TermStore].
    pub struct TermId;
}

new_key_type! {
    /// The ID of a [Scope] stored in [super::values::ScopeStore].
    pub struct ScopeId;
}

new_key_type! {
    /// The Id of a [Args]
    pub struct ArgsId;
}

new_key_type! {
    /// The ID of a [Params]
    pub struct ParamsId;
}

new_key_type! {
    /// The ID of a [Pat]
    pub struct PatId;
}

new_key_type! {
    /// The ID of a [ParamsPat]
    pub struct PatParamsId;
}

/// The ID of a [UnresolvedTerm], separate from its [TermId], stored in
/// [super::terms::TermStore].
///
/// This needs to be separate from [TermId] so that if a type is copied (and new
/// IDs are generated for its members) the identity of the unknown variables
/// remains the same as in the original type.
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct ResolutionId(pub(super) usize);

impl Display for ResolutionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
