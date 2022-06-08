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
/// a variable. If cases, is empty, `general_return_ty` must be a type that isn't `Type`, for
/// example `Fn`.
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
///     general_params = (T: Type),
///     general_return_ty = Type,
///     cases = {
///         (T: Type) -> Type => ..,
///         (T: Type<Hash>) -> Type<Hash> => ..,
///         (T: Type<Hash ~ Eq>) -> Type<FindInHashMap> => ..,
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
/// (T: Type = str) -> Type<Conv<str>> => Dog<str> ~ impl Conv<str> { ... };
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

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct UnresolvedTy {
    pub resolution_id: ResolutionId,
    pub bound: TyId, // either a trait type or merge type of traits, for now
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyOfTy {
    pub bound: TyId, // either a trait type or merge type of traits, for now
}

#[derive(Debug, PartialEq, Eq)]
pub struct AppTyFnTy {
    pub ty_fn_ty: TyId,
    pub ty_args: TyArgs,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MergeTy {
    pub elements: Vec<TyId>,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct VarTy {
    pub name: Identifier,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Ty {
    /// The type of a type
    Ty(TyOfTy),
    /// Modules or impls
    Mod(ModDefId),
    /// Tuple type.
    Tuple(TupleTy),
    /// The type of a trait
    Trt(TrtDefId),
    /// The nominal type
    Nominal(NominalDefId),
    /// Merge of multiple types, for now must be traits
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

new_key_type! { pub struct TyId; }
new_key_type! { pub struct TrtDefId; }
new_key_type! { pub struct NominalDefId; }
new_key_type! { pub struct ImplGroupId; }
new_key_type! { pub struct ModDefId; }
new_key_type! { pub struct ResolutionId; }
