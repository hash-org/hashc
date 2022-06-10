//! Contains type definitions that the rest of the storage and the general typechecker use.
use hash_ast::ident::Identifier;
use slotmap::new_key_type;
use std::collections::HashMap;

/// The visibility of a member of a const scope.
#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

/// The mutability of a variable in a scope.
#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

/// A member of a scope, i.e. a variable or a type definition.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct ScopeMember {
    pub name: Identifier,
    pub ty: TyId,
    pub mutability: Mutability,
    pub initialised: bool,
}

/// A member of a const scope, i.e. an item in a module or impl.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct ConstMember {
    pub name: Identifier,
    pub ty: TyId,
    pub visibility: Visibility,
    pub initialised: bool,
}

/// Macro that helps with the construction of parameter and arguemnt types.
///
/// Provides ways to store and get an argument by its name or index.
macro_rules! params_list {
    ($(#[$met:meta])* $visibility:vis $Name:ident, ParamType = $Param:ty) => {
        $(#[$met])*
        #[derive(Debug, PartialEq, Eq)]
        $visibility struct $Name {
            pub params: Vec<$Param>,
            pub name_map: std::collections::HashMap<Identifier, usize>,
        }

        impl $Name {
            pub fn new(params: Vec<$Param>) -> Self {
                let name_map = params
                    .iter()
                    .enumerate()
                    .filter_map(|(i, param)| { Some((param.name?, i)) })
                    .collect();

                Self { params, name_map }
            }

            pub fn positional(&self) -> &[$Param] {
                &self.params
            }

            pub fn get_by_name(&self, name: Identifier) -> Option<&$Param> {
                self.positional().get(*self.name_map.get(&name)?)
            }
        }
    }
}

/// A type argument to a type parameter.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct TyArg {
    pub name: Option<Identifier>,
    pub value: TyId,
}

params_list!(
    #[doc="A list of type arguments to a type parameter list."]
    pub TyArgs,
    ParamType = TyArg
);

/// A type parameter, declaring a named type variable with a given type bound and optional default
/// value.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct TyParam {
    pub name: Option<Identifier>,
    pub bound: TyId,
    pub default: Option<TyId>,
}

params_list!(
    #[doc="A list of type parameters."]
    pub TyParams,
    ParamType = TyParam
);

/// A parameter, declaring a named variable with a given type and optional default value presence.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Param {
    pub name: Option<Identifier>,
    pub ty: TyId,
    pub has_default: bool,
}

params_list!(
    #[doc="A list of parameters."]
    pub Params,
    ParamType = Param
);

/// The origin of a pub module: was it defined in a `mod` block, an anonymous `impl` block, or an `impl
/// Trait` block?
#[derive(Debug, Hash, PartialEq, Eq)]
pub enum ModDefOrigin {
    /// Defined as a trait implementation (for the given trait).
    TrtImpl(TrtDefId),
    /// Defined as an anonymous implementation.
    AnonImpl,
    /// Defined as a module.
    Mod,
}

/// A module definition, which is of a given origin, has a binding name, and contains some constant
/// members.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct ModDef {
    pub name: Identifier,
    pub origin: ModDefOrigin,
    pub members: Vec<ConstMember>,
}

/// The fields of a struct.
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
pub struct StructDef {
    pub name: Identifier,
    pub fields: StructFields,
}

/// An enum variant, containing a variant name and a set of fields.
///
/// Structurally the same as a struct.
#[derive(Debug, PartialEq, Eq)]
pub struct EnumVariant {
    pub name: Identifier,
    pub fields: Params,
}

/// An enum definition, containing a binding name and a set of variants.
#[derive(Debug, PartialEq, Eq)]
pub struct EnumDef {
    pub name: Identifier,
    pub variants: HashMap<Identifier, EnumVariant>,
}

/// A trait definition, containing a binding name and a set of constant members.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct TrtDef {
    pub name: Identifier,
    pub members: Vec<ConstMember>,
}

/// A nominal definition, which for now is either a struct or an enum.
#[derive(Debug, PartialEq, Eq)]
pub enum NominalDef {
    Struct(StructDef),
    Enum(EnumDef),
}

/// A tuple type, containg parameters as members.
#[derive(Debug, PartialEq, Eq)]
pub struct TupleTy {
    pub members: Params,
}

/// A function type, with a set of input parameters and a return type.
///
/// All the parameter types and return type must be of shape `Instance<..>`.
#[derive(Debug, PartialEq, Eq)]
pub struct FnTy {
    pub params: Params,
    pub return_ty: TyId,
}

/// A type function type.
///
/// A type function is a compile-time function that works on types.
/// It has a general set of "base" parameters and return type.
///
/// These are refined in the `cases` field, which provides conditional values for the return type of
/// the function, based on what the arguments are.
///
/// These cases might contain nothing, in which case the type function does not return a type, but
/// a value. If cases, is empty, `general_return_ty` must be a type that is `Instance<..>`, for
/// example `Instance<Fn<..>>`.
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
///     general_params = (T: Impl<Any>),
///     general_return_ty = NominalDef<"Dog">,
///     cases = {
///         (T: ~) -> NominalDef<"Dog"> => ..,
///         (T: Impl<Hash>) -> NominalDef<"Dog"> ~ Impl<Hash> => ..,
///         (T: Impl<Hash> ~ Impl<Eq>) -> NominalDef<"Dog"> ~ Impl<FindInHashMap> => ..,
///     }
/// }
/// ```
///
/// At any point, the resolved type of `Dog<T>` is the merged type of the return type of each case
/// which matches `T`. In other words, cases are not short-circuiting; they are all evaluated and
/// then combined. If there are no cases, then `Dog<T>` cannot be used as a type, and is in fact a
/// variable (usually a function).
///
/// The `general_return_ty` field is always a supertype of the return type of each case.
/// Also note that `general_return_ty` never changes---a type cannot become more general than it
/// already is; however, it can become more refined.
#[derive(Debug, PartialEq, Eq)]
pub struct TyFnTy {
    pub general_params: TyParams,
    pub general_return_ty: TyId,
    pub cases: Vec<TyFnCase>,
}

/// Represents a case in a type function, for some subset of its `general_params`, to some specific
/// return type and refined return value.
///
/// The `default` property of each [TyParam] in the `params` field represents types which have been
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
/// (T: ~ = str) -> Impl<Conv<str>> => type Dog<str> ~ impl Conv<str> { ... };
/// ```
///
/// The case's `return_ty` must always be able to unify with the target `general_return_ty`,
/// and the type parameters should be able to each unify with the target `general_params`, of the
/// parent [TyFnTy].
#[derive(Debug, PartialEq, Eq)]
pub struct TyFnCase {
    pub params: TyParams,
    pub return_ty: TyId,
    pub return_value: TyId,
}

/// Not yet resolved.
///
/// Might contain a bound which is progressively resolved as more information about the usage of
/// the type is known during inference.
///
/// The resolution ID is incremented for each new unresolved type.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct UnresolvedTy {
    pub resolution_id: ResolutionId,
    pub bound: TyId, // @@TODO: doc on this and general ty bounds
}

/// The type of a type.
///
/// Contains the bound of the type. For representing any generic type, the bound
/// should be set to an empty `Ty::Merge`.
#[derive(Debug, PartialEq, Eq)]
pub struct TyOfTy {
    pub bound: TyId,
}

/// The action of applying a set of arguments to a type function.
///
/// This essentially creates a lambda calculus within the Hash type system, which allows it to
/// express arbitrary programs.
///
/// When this type is unified with another type, the function is applied by first instantiating its
/// return value over its type parameters, and then unifying the instantiated type parameters with
/// the given type arguments of the function (the `ty_args` field).
#[derive(Debug, PartialEq, Eq)]
pub struct AppTyFnTy {
    pub ty_fn_ty: TyId,
    pub ty_args: TyArgs,
}

/// Merge of multiple types.
///
/// This corresponds to the `~` operator in Hash. Might contain:
/// - One or zero [Ty::Nominal]
/// - Zero or more [Ty::Impls]
/// - Zero or more [Ty::Mod]
/// - Zero or more [Ty::Merge] types with the same restrictions.
///
/// `~` is commutative, idempotent, and associative.
///
/// Joining types is a core operation in Hash, and it is what allows for polymorphism. Within
/// the language, "Type" is a synonym for an empty merge, i.e. a type that can unify with any
/// other type (other than instance types).
///
/// `A ~ B ~ C` is assignable to `A`, `A ~ B`, `A ~ C` or any other combination of `A`, `B` and
/// `C`. In that sense, it is like an intersection type.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MergeTy {
    pub elements: Vec<TyId>,
}

/// Represents a type variable.
///
/// This is a variable that exists in some scope bound and is of some supertype. Any type that is
/// assignable to the supertype of a variable can be assigned to that variable.
///
/// For example, if `T: Hash`, then `T = str` is valid because `str: Hash` is true. Note, here `T:
/// Hash` actually translates to `Ty::Var("T")` unifies with `Ty::Impls(HashTraitID)`.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct VarTy {
    pub name: Identifier,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Ty {
    /// Modules or impls.
    ///
    /// Modules and trait implementations, as well as anonymous implementations, are treated as
    /// types, and they are all represented by [Ty::Mod], since they are all constant scopes.
    ///
    /// Information about the origin of each instance of [Ty::Mod] can be found in its
    /// corresponding [ModDef].
    Mod(ModDefId),
    /// Tuple type.
    ///
    /// Usually used within a [Ty::Instance].
    Tuple(TupleTy),
    /// The type of a trait.
    ///
    /// This is the return type of a `trait(..)` definition
    Trt(TrtDefId),
    /// Type that implements a trait.
    ///
    /// This unifies with appropriate [Ty::Mod], [Ty::Merge], i.e. a [Ty::Mod] that is an
    /// implementation of the [TrtDefId] stored in this variant, or a [Ty::Merge] containing at
    /// least one such [Ty::Mod].
    Impls(TrtDefId),
    /// A nominal type, either a struct or an enum.
    ///
    /// This unifies only with types that have the same nominal, at the very least.
    Nominal(NominalDefId),
    /// An instance of a type.
    ///
    /// The inner type must be a `Ty::Nominal` or a merge containing it (for now, until we get
    /// trait objects).
    ///
    /// If `X` is of type `Nominal ~ A ~ B`, then instantiating `X` yields type `Instance<Nominal ~
    /// A ~ B>`.
    ///
    /// All arguments of normal functions must be wrapped in `Instance`. Only type arguments are
    /// not wrapped in `Instance`.
    Instance(TyId),
    /// Merge type.
    Merge(MergeTy),
    /// Function type.
    Fn(FnTy),
    /// Type function type.
    TyFn(TyFnTy),
    /// Type function application
    AppTyFn(AppTyFnTy),
    /// Type variable
    Var(VarTy),
    /// Not yet resolved.
    Unresolved(UnresolvedTy),
}

// IDs for all the primitives to be stored on mapped storage.

new_key_type! { pub struct TyId; }

new_key_type! { pub struct TrtDefId; }

new_key_type! { pub struct NominalDefId; }

new_key_type! { pub struct ImplGroupId; }

new_key_type! { pub struct ModDefId; }

new_key_type! { pub struct ResolutionId; }
