//! Contains structures to keep track of terms and information relevant to them.
use std::{
    cell::Cell,
    collections::HashMap,
    fmt::{self, Display},
};

use hash_ast::ast::{IntLit, IntLitKind, IntTy};
use hash_source::{
    constant::{InternedStr, CONSTANT_MAP},
    identifier::Identifier,
};
use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{
        CloneStore, DefaultSequenceStore, DefaultStore, SequenceStore, SequenceStoreKey, Store,
    },
};
use num_bigint::BigInt;

use crate::{
    arguments::ArgsId,
    fmt::{fmt_as_single, ForFormatting, PrepareForFormatting},
    mods::ModDefId,
    nominals::{EnumVariantValue, NominalDefId},
    params::{AccessOp, Field, ParamsId},
    scope::{BoundVar, ScopeVar, SetBound, Var},
    trts::TrtDefIdOld,
};

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

/// Not yet resolved.
///
/// The resolution ID is incremented for each new unresolved term.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct UnresolvedTerm {
    pub resolution_id: ResolutionId,
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

new_store_key!(pub TermId);

/// Stores all the terms within a typechecking cycle.
///
/// terms are accessed by an ID, of type [TermId].
#[derive(Debug, Default)]
pub struct TermStore {
    data: DefaultStore<TermId, Term>,
    /// Keeps track of the last ID used for unresolved terms.
    /// This will be incremented every time a [Term::Unresolved] is created.
    ///
    /// @@Future: In the future, resolution IDs can be used to implement a
    /// pointer-based unknown term resolution, where substitutions
    /// correspond to mutating terms rather than creating whole new ones.
    /// This could greatly improve performance.
    last_resolution_id: Cell<usize>,
}

impl Store<TermId, Term> for TermStore {
    fn internal_data(&self) -> &std::cell::RefCell<Vec<Term>> {
        self.data.internal_data()
    }
}

impl TermStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get a new [ResolutionId] for a new [Term::Unresolved].
    ///
    /// This shouldn't be directly used in inference code, rather call the
    /// appropriate [PrimitiveBuilder](crate::builder::PrimitiveBuilder)
    /// function.
    pub fn new_resolution_id(&self) -> ResolutionId {
        let new_id = self.last_resolution_id.get() + 1;
        self.last_resolution_id.set(new_id);
        ResolutionId(new_id)
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
    Trt(TrtDefIdOld),
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
    /// A name associated with this function literal.
    pub name: Option<Identifier>,

    /// The type of the function.
    pub fn_ty: TermId,

    /// The type of the return value.
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

impl Term {
    /// Compute the level of the term. This is a primitive computation
    /// and does not attempt to compute the true level of the [Term]
    /// by looking at the inner children of the [Term].
    pub fn get_term_level(&self, _store: &TermStore) -> TermLevel {
        // @@Todo(feds01): implement the other variants by recursing into them.
        // This should be done on a struct with access to storage
        match self {
            Term::Access(_)
            | Term::Var(_)
            | Term::Merge(_)
            | Term::TyFn(_)
            | Term::TyOf(_)
            | Term::Union(_)
            | Term::SetBound(_)
            | Term::ScopeVar(_)
            | Term::BoundVar(_)
            | Term::TyFnTy(_)
            | Term::TyFnCall(_) => TermLevel::Unknown,
            Term::Unresolved(_) => TermLevel::Unknown,
            Term::Root => TermLevel::Level4,
            Term::Level3(_) => TermLevel::Level3,
            Term::Level2(_) => TermLevel::Level2,
            Term::Level1(_) => TermLevel::Level1,
            Term::Level0(_) => TermLevel::Level0,
        }
    }
}

/// Represents the level of a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A enumeration of the level kinds that terms can be.
pub enum TermLevel {
    /// Couldn't be determined and thus labelled as unknown
    Unknown,
    /// Level 0 terms
    Level0,
    /// Level 1 terms
    Level1,
    /// Level 2 terms
    Level2,
    /// Level 3 terms
    Level3,
    /// Level 4 terms, specifically [Term::Root]
    Level4,
}

impl Display for TermLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TermLevel::Unknown => write!(f, "unknown"),
            TermLevel::Level0 => write!(f, "level-0"),
            TermLevel::Level1 => write!(f, "level-1"),
            TermLevel::Level2 => write!(f, "level-2"),
            TermLevel::Level3 => write!(f, "level-3"),
            TermLevel::Level4 => write!(f, "level-4"),
        }
    }
}

new_sequence_store_key!(pub TermListId);

/// Define the [TermListStore], which is a sequence of [Term]s associated
/// with a [TermListId].
pub type TermListStore = DefaultSequenceStore<TermListId, TermId>;

impl PrepareForFormatting for &Sub {}
impl PrepareForFormatting for &UnresolvedTerm {}
impl PrepareForFormatting for &Level0Term {}
impl PrepareForFormatting for &Level1Term {}
impl PrepareForFormatting for &Level2Term {}
impl PrepareForFormatting for &Level3Term {}
impl PrepareForFormatting for TermId {}
impl PrepareForFormatting for (&'static str, TermListId) {}

impl fmt::Display for ForFormatting<'_, &Sub> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sub = self.t;

        for (i, (subject, target)) in sub.pairs().enumerate() {
            fmt_as_single!(f, target.for_formatting(self.global_storage).fmt(f)?);
            write!(f, "/")?;

            match subject {
                SubVar::Unresolved(unresolved) => {
                    write!(f, "{}", unresolved.for_formatting(self.global_storage))?;
                }
            };
            if i != sub.map().len() - 1 {
                write!(f, ", ")?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for ForFormatting<'_, &UnresolvedTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "U_{}", self.t.resolution_id)
    }
}

impl fmt::Display for ForFormatting<'_, &Level0Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let term = self.t;

        match term {
            Level0Term::Rt(ty_id) => {
                write!(f, "{{value {}}}", ty_id.for_formatting(self.global_storage))
            }
            Level0Term::FnLit(fn_lit) => {
                if let Some(name) = fn_lit.name {
                    write!(f, "{name}")?;
                }

                write!(
                    f,
                    "{} => {}",
                    fn_lit.fn_ty.for_formatting(self.global_storage),
                    fn_lit.return_value.for_formatting(self.global_storage),
                )
            }
            Level0Term::EnumVariant(enum_variant) => {
                write!(
                    f,
                    "{}::{}",
                    enum_variant.enum_def_id.for_formatting(self.global_storage),
                    enum_variant.variant_name,
                )
            }
            Level0Term::FnCall(fn_call) => {
                fn_call.subject.for_formatting(self.global_storage).fmt(f)?;

                write!(f, "({})", fn_call.args.for_formatting(self.global_storage))?;
                Ok(())
            }
            Level0Term::Lit(lit_term) => {
                match lit_term {
                    LitTerm::Str(str) => {
                        write!(f, "\"{str}\"")
                    }
                    LitTerm::Int { value, kind } => {
                        // It's often the case that users don't include the range of the entire
                        // integer and so we will write `-2147483648..x` and
                        // same for max, what we want to do is write `MIN`
                        // and `MAX for these situations since it is easier for the
                        // user to understand the problem
                        if let Some(min) = kind.min() && min == *value {
                            write!(f, "{kind}::MIN")
                        } else if let Some(max) = kind.max() && max == *value {
                            write!(f, "{kind}::MAX")
                        } else {
                            write!(f, "{value}_{kind}")
                        }
                    }
                    LitTerm::Char(char) => {
                        // Use debug implementation since we want to display the `literal` value
                        // rather than the actual glyph
                        write!(f, "{char:?}")
                    }
                }
            }
            Level0Term::Tuple(tuple_lit) => {
                write!(f, "({})", tuple_lit.members.for_formatting(self.global_storage))
            }
            Level0Term::Constructed(ConstructedTerm { subject, members }) => {
                write!(
                    f,
                    "{}({})",
                    subject.for_formatting(self.global_storage),
                    members.for_formatting(self.global_storage)
                )
            }
            Level0Term::Unit(def_id) => {
                write!(f, "{}", def_id.for_formatting(self.global_storage),)
            }
        }
    }
}

impl fmt::Display for ForFormatting<'_, &Level1Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.t {
            Level1Term::ModDef(mod_def_id) => {
                mod_def_id.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Level1Term::NominalDef(nominal_def_id) => {
                nominal_def_id.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Level1Term::Tuple(tuple) => {
                write!(f, "(")?;
                tuple.members.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)?;
                write!(f, ")")
            }
            Level1Term::Fn(fn_term) => {
                write!(f, "(")?;
                fn_term.params.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)?;
                write!(f, ") -> ")?;
                fn_term.return_ty.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
        }
    }
}

impl fmt::Display for ForFormatting<'_, &Level2Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.t {
            Level2Term::Trt(trt_def_id) => {
                trt_def_id.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Level2Term::AnyTy => {
                write!(f, "AnyType")
            }
            Level2Term::SizedTy => {
                write!(f, "Type")
            }
        }
    }
}

impl fmt::Display for ForFormatting<'_, &Level3Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.t {
            Level3Term::TrtKind => write!(f, "Trait"),
        }
    }
}

impl fmt::Display for ForFormatting<'_, TermId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.global_storage.term_store.get(self.t) {
            Term::Access(access_term) => {
                access_term.subject.for_formatting(self.global_storage).fmt(f)?;

                let op = match access_term.op {
                    AccessOp::Namespace => "::",
                    AccessOp::Property => ".",
                };
                write!(f, "{op}{}", access_term.name)?;
                Ok(())
            }
            Term::Var(Var { name })
            | Term::BoundVar(BoundVar { name })
            | Term::ScopeVar(ScopeVar { name, .. }) => {
                write!(f, "{name}")
            }
            Term::Merge(terms) => {
                ("~", terms).for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Term::Union(terms) => {
                if terms.is_empty() {
                    write!(f, "never")
                } else {
                    ("|", terms).for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
                }
            }
            Term::TyFn(ty_fn) => {
                match ty_fn.name {
                    Some(name) if !self.opts.expand => {
                        write!(f, "{name}")?;
                        Ok(())
                    }
                    _ => {
                        write!(f, "<")?;
                        ty_fn
                            .general_params
                            .for_formatting_with_opts(self.global_storage, self.opts)
                            .fmt(f)?;
                        write!(f, "> -> ")?;
                        ty_fn
                            .general_return_ty
                            .for_formatting_with_opts(self.global_storage, self.opts)
                            .fmt(f)?;

                        if let Some(case) = ty_fn.cases.first() {
                            write!(f, " => ")?;
                            case.return_value
                                .for_formatting_with_opts(self.global_storage, self.opts)
                                .fmt(f)?;
                        }

                        // We assume only the first case is the base one
                        // @@TODO: refine this to show all cases
                        Ok(())
                    }
                }
            }
            Term::TyFnTy(ty_fn_ty) => {
                write!(f, "<")?;
                ty_fn_ty.params.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)?;
                write!(f, "> -> ")?;
                ty_fn_ty
                    .return_ty
                    .for_formatting_with_opts(self.global_storage, self.opts)
                    .fmt(f)?;
                Ok(())
            }
            Term::TyFnCall(app_ty_fn) => {
                write!(
                    f,
                    "{}<{}>",
                    app_ty_fn.subject.for_formatting(self.global_storage),
                    app_ty_fn.args.for_formatting_with_opts(self.global_storage, self.opts)
                )?;
                Ok(())
            }
            Term::Unresolved(unresolved_term) => {
                unresolved_term.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Term::SetBound(set_bound) => {
                write!(f, "({})", set_bound.term.for_formatting(self.global_storage))?;

                self.global_storage.scope_store.map_fast(set_bound.scope, |scope| {
                    let members = &scope.members;
                    write!(f, " where ")?;
                    for (i, member) in members.iter().enumerate() {
                        write!(
                            f,
                            "{} = {}",
                            member.name(),
                            member.value().unwrap().for_formatting(self.global_storage)
                        )?;

                        if i != members.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    Ok(())
                })
            }
            Term::Level3(term) => {
                term.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Term::Level2(term) => {
                term.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Term::Level1(term) => {
                term.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Term::Level0(term) => {
                term.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Term::Root => {
                write!(f, "Root")
            }
            Term::TyOf(term) => {
                write!(
                    f,
                    "typeof({})",
                    term.for_formatting_with_opts(self.global_storage, self.opts)
                )
            }
        }
    }
}

impl fmt::Debug for ForFormatting<'_, TermId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.global_storage.term_store.get(self.t))
    }
}

impl fmt::Display for ForFormatting<'_, (&'static str, TermListId)> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (separator, terms) = self.t;

        for idx in terms.to_index_range() {
            let term = self.global_storage.term_list_store.get_at_index(terms, idx);
            write!(f, "{}", term.for_formatting_with_opts(self.global_storage, self.opts))?;

            if idx != terms.len() - 1 {
                write!(f, " {separator} ")?;
            }
        }

        Ok(())
    }
}
