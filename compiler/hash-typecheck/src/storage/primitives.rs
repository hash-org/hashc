//! Contains type definitions that the rest of the storage and the general typechecker use.
use hash_source::{identifier::Identifier, SourceId};
use slotmap::new_key_type;
use std::collections::HashMap;

/// The visibility of a member of a const scope.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

/// The mutability of a variable in a scope.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

/// A member of a scope, i.e. a variable or a type definition.
#[derive(Debug, Clone)]
pub struct Member {
    pub name: Identifier,
    pub ty: TyId,
    pub value: ValueId,
    pub visibility: Visibility,
    pub mutability: Mutability,
}

/// A scope is either a variable scope or a constant scope.
///
/// Examples of variable scopes are:
/// - Block expression scope
/// - Function parameter scope
///
/// Examples of const scopes are:
/// - The root scope
/// - Module block scope
/// - Trait block scope
/// - Impl block scope
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    Variable,
    Constant,
}

/// Stores a list of members, indexed by the members' names.
#[derive(Debug, Clone)]
pub struct Scope {
    pub kind: ScopeKind,
    pub members: HashMap<Identifier, Member>,
}

impl Scope {
    /// Create an empty [Scope].
    pub fn empty(kind: ScopeKind) -> Self {
        Self {
            kind,
            members: HashMap::new(),
        }
    }

    /// Create a new [Scope] from the given members.
    pub fn new(kind: ScopeKind, members: impl IntoIterator<Item = Member>) -> Self {
        Self {
            kind,
            members: members
                .into_iter()
                .map(|member| (member.name, member))
                .collect(),
        }
    }

    /// Add a member by name.
    pub fn add(&mut self, member: Member) {
        self.members.insert(member.name, member);
    }

    /// Get a member by name.
    pub fn get(&self, member_name: Identifier) -> Option<&Member> {
        self.members.get(&member_name)
    }

    /// Get a member by name, mutably.
    pub fn get_mut(&mut self, member_name: Identifier) -> Option<&mut Member> {
        self.members.get_mut(&member_name)
    }
}

/// Trait to be implemented by primitives which contain a `name` field that is an
/// optional identifier.
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
}

impl<ParamType: GetNameOpt + Clone> ParamList<ParamType> {
    /// Create a new [ParamList] from the given list of parameters.
    pub fn new(params: Vec<ParamType>) -> Self {
        let name_map = params
            .iter()
            .enumerate()
            .filter_map(|(i, param)| Some((param.get_name_opt()?, i)))
            .collect();

        Self { params, name_map }
    }

    /// Get the parameters as a positional slice
    pub fn positional(&self) -> &[ParamType] {
        &self.params
    }

    /// Get a parameter by name.
    pub fn get_by_name(&self, name: Identifier) -> Option<(usize, &ParamType)> {
        let param_index = *self.name_map.get(&name)?;
        Some((param_index, self.positional().get(param_index)?))
    }
}

/// An argument
#[derive(Debug, Clone, Hash)]
pub struct Arg {
    pub name: Option<Identifier>,
    pub value: ValueId,
}

impl GetNameOpt for Arg {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A list of arguments.
pub type Args = ParamList<Arg>;

/// A parameter, declaring a potentially named variable with a given type and default value.
#[derive(Debug, Clone, Hash)]
pub struct Param {
    pub name: Option<Identifier>,
    pub ty: TyId,
    pub value: ValueId, // Could be Value::Unset
}

impl GetNameOpt for Param {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A list of parameters.
pub type Params = ParamList<Param>;

/// The origin of a module: was it defined in a `mod` block, an anonymous `impl` block, or an `impl
/// Trait` block?
#[derive(Debug, Clone, Hash)]
pub enum ModDefOrigin {
    /// Defined as a trait implementation (for the given trait value).
    TrtImpl(ValueId),
    /// Defined as an anonymous implementation.
    AnonImpl,
    /// Defined as a module (`mod` block).
    Mod,
    /// Defined as a file module or interactive.
    Source(SourceId),
}

/// A module definition, which is of a given origin, has a binding name, and contains some constant
/// members.
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
    Explicit(Params),
    /// The struct does not have any accessible parameters.
    ///
    /// This is used for core language definitions that will be filled in later in the compiler
    /// pipeline.
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
#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: Identifier,
    pub fields: Params,
}

/// An enum definition, containing a binding name and a set of variants.
#[derive(Debug, Clone)]
pub struct EnumDef {
    pub name: Option<Identifier>,
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

/// A tuple type, containg parameters as members.
#[derive(Debug, Clone)]
pub struct TupleTy {
    pub members: Params,
}

/// A function type, with a set of input parameters and a return type.
///
/// All the parameter types and return type must be level 0
#[derive(Debug, Clone)]
pub struct FnTy {
    pub params: Params,
    pub return_ty: TyId,
}

/// A type function type.
///
/// A type function is a compile-time function that works on types. Type function return types can
/// be level 0, level 1 or level 2. It has a general set of "base" parameters and return type.
///
/// These are refined in the `cases` field, which provides conditional values for the return value
/// of the function, based on what the arguments are.
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
///     general_params = (T: Ty::Ty = Value::Unset),
///     general_return_ty = Ty::Ty,
///     cases = {
///         (T: Ty::Ty) -> Ty::Ty => Value::NominalDef(DogStructDef),
///         (T: Ty::Ty(HashTraitDef)) -> Ty::Ty(HashTraitDef) => Value::Merge([
///             Value::NominalDef(DogStructDef),
///             Value::Mod(
///                 origin=TraitImpl(Value::Trt(HashTraitDef)),
///                 members=..
///             ),
///         ]),
///         (T: Ty::Merge([Ty::Ty(HashTraitDef), Ty::Ty(EqTraitDef)]))
///             -> Ty::Ty(FindInHashMapTraitDef) =>
///             => Value::Merge([
///                 Value::NominalDef(DogStructDef),
///                 Value::Mod(
///                     origin=TraitImpl(Value::Trt(FindInHashMapTraitDef)),
///                     members=..
///                 ),
///             ])
///     }
/// }
/// ```
///
/// At any point, the resolved type of `Dog<T>` is the merged type of the return type of each case
/// which matches `T`. In other words, cases are not short-circuiting; they are all evaluated and
/// then combined.
///
/// The `general_return_ty` field is always a supertype of the return type of each case.
#[derive(Debug, Clone)]
pub struct TyFnValue {
    /// An optional name for the type function, if it is directly assigned to a binding.
    pub name: Option<Identifier>,
    pub general_params: Params,
    pub general_return_ty: TyId,
    pub cases: Vec<TyFnCase>,
}

/// Represents a case in a type function, for some subset of its `general_params`, to some specific
/// return type and refined return value.
///
/// The `value` property of each [Param] in the `params` field represents types which have been
/// set, for example:
///
/// ```ignore
/// Dog<str> ~= impl Conv<str> {
///     conv = (self) => "Dog with foo=" + conv(self.foo);
/// };
/// ```
///
/// This translates to a case:
/// ```ignore
/// (T: Ty::Ty = Value::NominalDef(strDefId))
///     -> Ty::AppTyFn(ConvValue (a type fn), [Value::NominalDef(strDefId)])
///     => Value::Merge([
///         Value::AppTyFn(DogValue (a type fn), [strDefId]),
///         Value::Ty(Ty::Mod(
///             origin=TraitImpl(Value::AppTyFn(ConvValue (a type fn), [strDefId])),
///             members=...
///         ))
///     ])
/// ```
///
/// The case's `return_ty` must always be able to unify with the target `general_return_ty`,
/// and the type parameters should be able to each unify with the target `general_params`, of the
/// parent [TyFnValue].
#[derive(Debug, Clone)]
pub struct TyFnCase {
    pub params: Params,
    pub return_ty: TyId,
    pub return_value: ValueId,
}

/// Not yet resolved.
///
/// The resolution ID is incremented for each new unresolved type.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub struct UnresolvedTy {
    pub resolution_id: ResolutionId,
}

/// A type variable, which is just a name or collection of names (namespace operator accessed).
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Var {
    pub names: Vec<Identifier>,
}

impl Var {
    /// Create a type variable with a single name.
    pub fn single(name: impl Into<Identifier>) -> Self {
        Self {
            names: vec![name.into()],
        }
    }

    /// Create a type variable with N multiple names (the first N-1 of which refer to modules).
    pub fn compound(names: impl IntoIterator<Item = impl Into<Identifier>>) -> Self {
        Self {
            names: names.into_iter().map(|x| x.into()).collect(),
        }
    }
}

/// The action of applying a set of arguments to a type function.
///
/// This essentially creates a lambda calculus within the Hash type system, which allows it to
/// express arbitrary programs.
///
/// When this type is unified with another type, the function is applied by first instantiating its
/// return value over its type parameters, and then unifying the instantiated type parameters with
/// the given type arguments of the function (the `ty_args` field).
#[derive(Debug, Clone)]
pub struct AppTyFn {
    pub ty_fn_value: ValueId,
    // @@Reconsider(kontheocharis): should this be something like `TyArgs`? Aren't only types
    // allowed here? Unclear with type functions.
    pub args: Args,
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
/// ty: Ty::TyFn(params = [(name="X", ty=Ty::Ty)], return_ty=Ty::Ty)
/// value: Value::Unset,
/// ```
#[derive(Debug, Clone)]
pub struct TyFnTy {
    pub params: Params,
    pub return_ty: TyId,
}

/// The basic data structure of a compile-time value, or [Value::Rt] if the value is run-time.
#[derive(Debug, Clone)]
pub enum Value {
    /// A trait value.
    ///
    /// Has a level 2 type.
    Trt(TrtDefId),
    /// A value returned by the `type` keyword.
    ///
    /// Has a level 1 type.
    Ty(TyId),
    /// A runtime value of a given type.
    ///
    /// Has a level 0 type.
    Rt(TyId),
    /// A type function value.
    ///
    /// Has a level N type, where N is the level of the return value of the function.
    TyFn(TyFnValue),
    /// A type function application.
    ///
    /// Has a level N type, where N is the level of the resultant application.
    AppTyFn(AppTyFn),
    /// Modules or impls.
    ///
    /// Modules and trait implementations, as well as anonymous implementations, are treated as
    /// types.
    ///
    /// Information about the origin of each instance of [Value::ModDef] can be found in its
    /// corresponding [ModDef].
    ///
    /// Has a level 1 type.
    ModDef(ModDefId),
    /// A nominal type definition, either a struct or an enum.
    ///
    /// Has a level 1 type.
    NominalDef(NominalDefId),
    /// A type-level variable, with some type that is stored in the current scope.
    ///
    /// Has a level N type, where N is the level of the type of the variable in the context
    Var(Var),
    /// Merge of multiple values.
    ///
    /// Inner types must have the same level.
    ///
    /// Has a level N type, where N is the level of the inner types.
    Merge(Vec<ValueId>),
    /// Unset value, which should be of a given type.
    Unset(TyId),
}

/// The basic data structure of a type.
#[derive(Debug, Clone)]
pub enum Ty {
    /// A type function
    ///
    /// Level N, where N is the level of the return type of the type function.
    TyFn(TyFnTy),
    /// A type function application.
    ///
    /// Level N, where N is the level of the return type of the type function applied to these args.
    AppTyFn(AppTyFn),
    /// The type of a trait
    ///
    /// Level 2
    Trt,
    /// A type, possibly with a trait bound
    ///
    /// Level 1
    Ty(Option<TrtDefId>),
    /// A nominal type definition, either a struct or an enum.
    ///
    /// Level 0
    NominalDef(NominalDefId),
    /// A module
    ModDef(ModDefId),
    /// Tuple type.
    ///
    /// Level 0
    Tuple(TupleTy),
    /// Function type.
    ///
    /// Level 0
    Fn(FnTy),
    /// A type-level variable, with some type that is stored in the current scope.
    ///
    /// Level N - 1, where N is the level of the type of the variable in the context
    Var(Var),
    /// Merge of multiple types.
    ///
    /// Inner types must have the same level.
    ///
    /// Level N, where N is the level of the inner types.
    Merge(Vec<TyId>),
    /// Not yet resolved.
    ///
    /// Unknown level.
    ///
    /// @@TODO: Maybe unknown types should keep track of their levels and any additional inferred
    /// info.
    Unresolved(UnresolvedTy),
}

// IDs for all the primitives to be stored on mapped storage.

new_key_type! {
    /// The ID of a [Ty] stored in [super::tys::TyStore].
    pub struct TyId;
}

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
    /// The ID of a [Value] stored in [super::values::ValueStore].
    pub struct ValueId;
}

new_key_type! {
    /// The ID of a [Scope] stored in [super::values::ScopeStore].
    pub struct ScopeId;
}

/// The ID of a [UnresolvedTy], separate from its [TyId], stored in [super::tys::TyStore].
///
/// This needs to be separate from [TyId] so that if a type is copied (and new IDs are generated
/// for its members) the identity of the unknown variables remains the same as in the original
/// type.
#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct ResolutionId(pub(super) usize);
