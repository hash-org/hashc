use std::collections::HashMap;

use hash_ast::ident::Identifier;
use slotmap::new_key_type;

new_key_type! { pub struct TyId; }
new_key_type! { pub struct TrtDefId; }
new_key_type! { pub struct NominalDefId; }
new_key_type! { pub struct ImplGroupId; }
new_key_type! { pub struct ModDefId; }
new_key_type! { pub struct ResolutionId; }

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct ScopeMember {
    name: Identifier,
    ty: TyId,
    visibility: Visibility,
    mutability: Mutability,
    initialised: bool,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct ConstMember {
    name: Identifier,
    ty: TyId,
    visibility: Visibility,
    initialised: bool,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct TyArg {
    name: Option<Identifier>,
    value: TyId,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct TyArgs {
    data: Vec<TyArg>,
}

macro_rules! params_list {
            ($visibility:vis $Name:ident, ParamType = $Param:ty) => {
                #[derive(Debug, PartialEq, Eq)]
                $visibility struct $Name {
                params: Vec<$Param>,
                name_map: std::collections::HashMap<Identifier, usize>,
            }

            impl $Name {
                pub fn new(params: Vec<$Param>) -> Self {
                    let name_map = params
                        .iter()
                        .enumerate()
                        .map(|(i, param)| (param.name, i))
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

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct TyParam {
    name: Identifier,
    bound: TyId,
    default: Option<TyId>,
}

params_list!(pub TyParams, ParamType = TyParam);

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Param {
    name: Identifier,
    ty: TyId,
    has_default: bool,
}

params_list!(pub Params, ParamType = Param);

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum ModDefOrigin {
    TrtImpl(TrtDefId),
    AnonImpl,
    Mod,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct ModDef {
    name: Identifier,
    origin: ModDefOrigin,
    members: Vec<ConstMember>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum StructFields {
    Explicit(Params),
    Opaque,
}

#[derive(Debug, PartialEq, Eq)]
pub struct StructDef {
    name: Identifier,
    fields: StructFields,
}

#[derive(Debug, PartialEq, Eq)]
pub struct EnumVariant {
    name: Identifier,
    fields: Params,
}

#[derive(Debug, PartialEq, Eq)]
pub struct EnumDef {
    name: Identifier,
    variants: HashMap<Identifier, EnumVariant>,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct TrtDef {
    name: Identifier,
    members: Vec<ConstMember>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum NominalDef {
    Struct(StructDef),
    Enum(EnumDef),
}

#[derive(Debug, PartialEq, Eq)]
pub struct TupleTy {
    members: Params,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FnTy {
    params: Params,
    return_ty: TyId,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyFnTy {
    params: TyParams,
    return_ty: TyId,              // overarching "supertype" of all cases
    cases: Vec<(TyParams, TyId)>, // defaults indicate "type patterns"
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct UnresolvedTy {
    resolution_id: ResolutionId,
    bound: TyId, // either a trait type or merge type of traits, for now
}

#[derive(Debug, PartialEq, Eq)]
pub struct TyOfTy {
    bound: TyId, // either a trait type or merge type of traits, for now
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct AppTyFnTy {
    ty_fn_ty: TyId,
    ty_args: TyArgs,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MergeTy {
    elements: Vec<TyId>,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct VarTy {
    name: Identifier,
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
