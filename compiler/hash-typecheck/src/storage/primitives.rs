//! Contains type definitions that the rest of the storage and the general typechecker use.
use hash_ast::ident::Identifier;
use hash_source::SourceId;
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
    pub kind: KindId,
    pub value: ValueId,
    pub visibility: Visibility,
    pub mutability: Mutability,
}

/// Stores a list of members, indexed by the members' names.
#[derive(Debug, Clone)]
pub struct Members {
    members: HashMap<Identifier, Member>,
}

impl Members {
    /// Create an empty [Members].
    pub fn empty() -> Self {
        Self {
            members: HashMap::new(),
        }
    }

    /// Create a new [Members] from the given members.
    pub fn new(members: impl IntoIterator<Item = Member>) -> Self {
        Self {
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

    /// Get a parameter by position.
    pub fn positional(&self) -> &[ParamType] {
        &self.params
    }

    /// Get a parameter by name.
    pub fn get_by_name(&self, name: Identifier) -> Option<&ParamType> {
        self.positional().get(*self.name_map.get(&name)?)
    }
}

/// An argument
#[derive(Debug, Clone, Hash)]
pub struct Arg {
    pub name: Option<Identifier>,
    pub value: ValueId,
}

/// A list of arguments.
pub type Args = ParamList<Arg>;

/// A parameter, declaring a potentially named variable with a given kind and default value.
#[derive(Debug, Clone, Hash)]
pub struct Param {
    pub name: Option<Identifier>,
    pub kind: KindId,
    pub value: ValueId, // Could be Value::Unset
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
    pub name: Identifier,
    pub origin: ModDefOrigin,
    pub members: Members,
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
    pub name: Identifier,
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
    pub name: Identifier,
    pub variants: HashMap<Identifier, EnumVariant>,
}

/// A trait definition, containing a binding name and a set of constant members.
#[derive(Debug, Clone)]
pub struct TrtDef {
    pub name: Identifier,
    pub members: Members,
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
/// All the parameter types and return type must be (or evaluate to) of kind `Kind::Rt(..)`.
#[derive(Debug, Clone)]
pub struct FnTy {
    pub params: Params,
    pub return_ty: KindId,
}

/// A type function type.
///
/// A type function is a compile-time function that works on types.
/// It has a general set of "base" parameters and return kind.
///
/// These are refined in the `cases` field, which provides conditional values for the return value
/// of the function, based on what the arguments are.
///
/// For example, consider:
///
/// ```
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
/// ```
/// TyFnTy {
///     general_params = (T: Kind::Ty = Value::Unset),
///     general_return_ty = Kind::Ty,
///     cases = {
///         (T: Kind::Ty) -> Kind::Ty => Value::Ty(Ty::NominalDef(DogStructDef)),
///         (T: Kind::Ty(HashTraitDef)) -> Kind::Ty(HashTraitDef) => Value::Merge([
///             Value::Ty(Ty::NominalDef(DogStructDef)),
///             Value::Ty(Ty::Mod(
///                 origin=TraitImpl(Value::Trt(HashTraitDef)),
///                 members=..
///             )),
///         ]),
///         (T: Kind::Ty(Merge([HashTraitDef, EqTraitDef])))
///             -> Kind::Ty(FindInHashMapTraitDef) =>
///             => Value::Merge([
///                 Value::Ty(Ty::NominalDef(DogStructDef)),
///                 Value::Ty(Ty::Mod(
///                     origin=TraitImpl(Value::Trt(FindInHashMapTraitDef)),
///                     members=..
///                 )),
///             ])
///     }
/// }
/// ```
///
/// At any point, the resolved kind of `Dog<T>` is the merged kind of the return kind of each case
/// which matches `T`. In other words, cases are not short-circuiting; they are all evaluated and
/// then combined.
///
/// The `general_return_kind` field is always a superkind of the return type of each case. Also
/// note that `general_return_kind` never changes---a type cannot become more general than it
/// already is; however, it can become more refined.
#[derive(Debug, Clone)]
pub struct TyFnValue {
    pub general_params: Params,
    pub general_return_kind: KindId,
    pub cases: Vec<TyFnCase>,
}

/// Represents a case in a type function, for some subset of its `general_params`, to some specific
/// return type and refined return value.
///
/// The `value` property of each [Param] in the `params` field represents types which have been
/// set, for example:
///
/// ```
/// Dog<str> ~= impl Conv<str> {
///     conv = (self) => "Dog with foo=" + conv(self.foo);
/// };
/// ```
///
/// This translates to a case:
/// ```
/// (T: Kind::Ty = Value::Ty(strDefId))
///     -> Kind::AppTyFn(ConvValue (a type fn), [strDefId])
///     => Value::Merge([
///         Value::AppTyFn(DogValue (a type fn), [strDefId]),
///         Value::Ty(Ty::Mod(
///             origin=TraitImpl(Value::AppTyFn(ConvValue (a type fn), [strDefId])),
///             members=...
///         ))
///     ])
/// ```
///
/// The case's `return_kind` must always be able to unify with the target `general_return_kind`,
/// and the type parameters should be able to each unify with the target `general_params`, of the
/// parent [TyFnValue].
#[derive(Debug, Clone)]
pub struct TyFnCase {
    pub params: Params,
    pub return_kind: KindId,
    pub return_value: ValueId,
}

/// Not yet resolved.
///
/// Might contain a bound which is progressively resolved as more information about the usage of
/// the value is known during inference.
///
/// The resolution ID is incremented for each new unresolved kind.
#[derive(Debug, Clone, Hash)]
pub struct UnresolvedKind {
    pub resolution_id: ResolutionId,
    pub bound: KindId,
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
    pub args: Args,
}

/// The kind of a type function, for example:
///
/// ```
/// T: <X: Type> -> Type
/// ```
///
/// would be
///
/// ```
/// name: "T",
/// kind: Kind::TyFn(params = [(name="X", kind=Kind::Ty)], return_kind=Kind::Ty)
/// value: Value::Unset,
/// ```
#[derive(Debug, Clone)]
pub struct TyFnKind {
    params: Params,
    return_kind: KindId,
}

#[derive(Debug, Clone)]
pub enum Kind {
    /// A trait kind.
    Trt,
    /// A type kind, with some optional trait bound.
    Ty(Option<TrtDefId>),
    /// A runtime kind, with some type bound.
    Rt(TyId),
    /// A type function, with some return kind.
    TyFn(TyFnKind),
    /// A type function application.
    AppTyFn(AppTyFn),
    /// Merge of multiple kinds.
    Merge(Vec<KindId>),
    /// Not yet resolved.
    Unresolved(UnresolvedKind),
}

#[derive(Debug, Clone)]
pub enum Value {
    /// A trait value.
    Trt(TrtDefId),
    /// A type value.
    Ty(TyId),
    /// A runtime value.
    Rt,
    /// A type function value, returning any kind of value.
    TyFn(TyFnValue),
    /// A type function application.
    AppTyFn(AppTyFn),
    /// A type-level variable, with some kind that is stored in the current scope.
    Var(Identifier),
    /// Merge of multiple values.
    Merge(Vec<ValueId>),
    /// Unset value.
    Unset,
}

#[derive(Debug, Clone)]
pub enum Ty {
    /// A nominal type definition, either a struct or an enum.
    NominalDef(NominalDefId),
    /// Modules or impls.
    ///
    /// Modules and trait implementations, as well as anonymous implementations, are treated as
    /// types, and they are all represented by [Ty::Mod], since they are all constant scopes.
    ///
    /// Information about the origin of each instance of [Ty::Mod] can be found in its
    /// corresponding [ModDef].
    Mod(ModDefId),
    /// Tuple type.
    Tuple(TupleTy),
    /// Function type.
    Fn(FnTy),
}

// IDs for all the primitives to be stored on mapped storage.

new_key_type! { pub struct TyId; }

new_key_type! { pub struct TrtDefId; }

new_key_type! { pub struct NominalDefId; }

new_key_type! { pub struct ImplGroupId; }

new_key_type! { pub struct ModDefId; }

new_key_type! {
    pub struct ValueId;
}

new_key_type! {
    pub struct KindId;
}

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Hash)]
pub struct ResolutionId(pub(super) usize);
