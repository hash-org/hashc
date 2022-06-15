//! Contains helper structures to create complex types and values without having to manually call
//! the corresponding stores.
use crate::storage::{
    primitives::{
        AppTyFn, Arg, Args, EnumDef, EnumVariant, FnTy, Member, ModDefId, Mutability, NominalDef,
        NominalDefId, Param, ParamList, Scope, ScopeId, ScopeKind, StructDef, StructFields, TrtDef,
        TrtDefId, TupleTy, Ty, TyFnCase, TyFnTy, TyFnValue, TyId, Value, ValueId, Var, Visibility,
    },
    GlobalStorage,
};
use hash_source::identifier::Identifier;
use std::{
    cell::{Cell, RefCell},
    ops::Deref,
};

/// Helper to create various primitive constructions (from [crate::storage::primitives]).
///
/// Optionally adds the constructions to a scope, if given.
pub struct PrimitiveBuilder<'gs> {
    // Keep these in RefCells so that calls to [PrimitiveBuilder] can be nested without borrowing
    // issues.
    //
    // *Important*: Should ensure that each method starts and ends the borrow within itself and
    // doesn't call any other methods in between, otherwise it will cause a panic.
    gs: RefCell<&'gs mut GlobalStorage>,
    scope: Cell<Option<ScopeId>>,
}

impl<'gs> PrimitiveBuilder<'gs> {
    /// Create a new [PrimitiveBuilder] with a given scope.
    pub fn new(gs: &'gs mut GlobalStorage) -> Self {
        Self {
            gs: RefCell::new(gs),
            scope: Cell::new(None),
        }
    }

    /// Create a new [PrimitiveBuilder] with a given scope.
    ///
    /// This adds every constructed item into the scope with their given names (if any).
    pub fn new_with_scope(gs: &'gs mut GlobalStorage, scope: ScopeId) -> Self {
        Self {
            gs: RefCell::new(gs),
            scope: Cell::new(Some(scope)),
        }
    }

    /// Get an immutable reference to the inner global storage.
    pub fn global_storage(&self) -> impl Deref<Target = &mut GlobalStorage> {
        self.gs.borrow()
    }

    /// Create a type variable with the given name.
    pub fn create_var(&self, var_name: impl Into<Identifier>) -> Var {
        Var::single(var_name)
    }

    /// Create a type variable with the given name, in the form of a [Ty::Var].
    pub fn create_var_ty(&self, var_name: impl Into<Identifier>) -> TyId {
        let var = self.create_var(var_name);
        self.gs.borrow_mut().ty_store.create(Ty::Var(var))
    }

    /// Add the given nominal definition to the scope.
    fn add_nominal_def_to_scope(&self, name: Identifier, def_id: NominalDefId) {
        let def_ty = self.create_ty_of_ty();
        let def_value = self
            .gs
            .borrow_mut()
            .value_store
            .create(Value::NominalDef(def_id));
        self.add_pub_member_to_scope(name, def_ty, def_value);
    }

    /// Create a nameless struct with opaque fields.
    pub fn create_nameless_opaque_struct_def(&self) -> NominalDefId {
        let def_id = self
            .gs
            .borrow_mut()
            .nominal_def_store
            .create(NominalDef::Struct(StructDef {
                name: None,
                fields: StructFields::Opaque,
            }));
        def_id
    }

    /// Create a struct with the given name and opaque fields.
    ///
    /// This adds the name to the scope.
    pub fn create_opaque_struct_def(&self, struct_name: impl Into<Identifier>) -> NominalDefId {
        let name = struct_name.into();
        let def_id = self
            .gs
            .borrow_mut()
            .nominal_def_store
            .create(NominalDef::Struct(StructDef {
                name: Some(name),
                fields: StructFields::Opaque,
            }));
        self.add_nominal_def_to_scope(name, def_id);
        def_id
    }

    /// Create a struct with the given name and fields.
    ///
    /// This adds the name to the scope.
    pub fn create_struct_def(
        &self,
        struct_name: impl Into<Identifier>,
        fields: impl IntoIterator<Item = Param>,
    ) -> NominalDefId {
        let name = struct_name.into();
        let def_id = self
            .gs
            .borrow_mut()
            .nominal_def_store
            .create(NominalDef::Struct(StructDef {
                name: Some(name),
                fields: StructFields::Explicit(ParamList::new(fields.into_iter().collect())),
            }));
        self.add_nominal_def_to_scope(name, def_id);
        def_id
    }

    /// Create an enum variant.
    pub fn create_enum_variant(
        &self,
        name: impl Into<Identifier>,
        fields: impl IntoIterator<Item = Param>,
    ) -> EnumVariant {
        EnumVariant {
            name: name.into(),
            fields: ParamList::new(fields.into_iter().collect()),
        }
    }

    /// Create an enum with the given name and variants.
    ///
    /// This adds the name to the scope.
    pub fn create_enum_def(
        &self,
        enum_name: impl Into<Identifier>,
        variants: impl IntoIterator<Item = EnumVariant>,
    ) -> NominalDefId {
        let name = enum_name.into();
        let def_id = self
            .gs
            .borrow_mut()
            .nominal_def_store
            .create(NominalDef::Enum(EnumDef {
                name: Some(name),
                variants: variants
                    .into_iter()
                    .map(|variant| (variant.name, variant))
                    .collect(),
            }));
        self.add_nominal_def_to_scope(name, def_id);
        def_id
    }

    /// Add a member to the scope, marking it as public.
    ///
    /// All other methods call this one to actually add members to the scope.
    pub fn add_pub_member_to_scope(&self, name: impl Into<Identifier>, ty: TyId, value: ValueId) {
        let member = self.create_pub_member(name, ty, value);
        if let Some(scope) = self.scope.get() {
            self.gs.borrow_mut().scope_store.get_mut(scope).add(member);
        }
    }

    /// Create a public member with the given name, type and unset value.
    pub fn create_unset_pub_member(&self, name: impl Into<Identifier>, ty: TyId) -> Member {
        self.create_pub_member(name, ty, self.create_unset_value(ty))
    }

    /// Create a public member with the given name, type and value.
    pub fn create_pub_member(
        &self,
        name: impl Into<Identifier>,
        ty: TyId,
        value: ValueId,
    ) -> Member {
        Member {
            name: name.into(),
            ty,
            value,
            visibility: Visibility::Public,
            mutability: Mutability::Immutable,
        }
    }

    /// Create a value [Value::Ty(x)] where `x` is the given [TyId].
    pub fn create_ty_value(&self, ty_id: TyId) -> ValueId {
        self.gs.borrow_mut().value_store.create(Value::Ty(ty_id))
    }

    /// Create a value [Value::Trt].
    pub fn create_ty_of_trt(&self) -> TyId {
        self.gs.borrow_mut().ty_store.create(Ty::Trt)
    }

    /// Create a type [Ty::Ty] with no bound.
    pub fn create_ty_of_ty(&self) -> TyId {
        self.gs.borrow_mut().ty_store.create(Ty::Ty(None))
    }

    /// Create a type [Ty::Ty] with the given bound.
    pub fn create_ty_of_ty_with_bound(&self, bound: TrtDefId) -> TyId {
        self.gs.borrow_mut().ty_store.create(Ty::Ty(Some(bound)))
    }

    /// Create a type [Ty::Merge] with the given inner types.
    pub fn create_merge_ty(&self, tys: impl IntoIterator<Item = TyId>) -> TyId {
        self.gs
            .borrow_mut()
            .ty_store
            .create(Ty::Merge(tys.into_iter().collect()))
    }

    /// Create a value [Value::Merge] with the given inner values.
    pub fn create_merge_value(&self, values: impl IntoIterator<Item = ValueId>) -> ValueId {
        self.gs
            .borrow_mut()
            .value_store
            .create(Value::Merge(values.into_iter().collect()))
    }

    /// Create the void type: [Ty::Tuple] with no members.
    pub fn create_void_ty(&self) -> TyId {
        self.gs.borrow_mut().ty_store.create(Ty::Tuple(TupleTy {
            members: ParamList::new(vec![]),
        }))
    }

    /// Create a [Value::Rt] of the given type.
    pub fn create_rt_value(&self, ty_id: TyId) -> ValueId {
        self.gs.borrow_mut().value_store.create(Value::Rt(ty_id))
    }

    /// Create a [Value::Unset].
    pub fn create_unset_value(&self, ty_id: TyId) -> ValueId {
        self.gs.borrow_mut().value_store.create(Value::Unset(ty_id))
    }

    /// Create a parameter with the given name and type.
    pub fn create_param(&self, name: impl Into<Identifier>, ty: TyId) -> Param {
        let value = self.create_unset_value(ty);
        Param {
            name: Some(name.into()),
            ty,
            value,
        }
    }

    /// Create a type with the given type value.
    pub fn create_ty(&self, ty: Ty) -> TyId {
        self.gs.borrow_mut().ty_store.create(ty)
    }

    /// Create a [Ty::Fn] with the given parameters and return type.
    pub fn create_fn_ty(&self, params: impl IntoIterator<Item = Param>, return_ty: TyId) -> TyId {
        self.gs.borrow_mut().ty_store.create(Ty::Fn(FnTy {
            params: ParamList::new(params.into_iter().collect()),
            return_ty,
        }))
    }

    /// Create a [Ty::NominalDef] from the given [NominalDefId].
    pub fn create_nominal_ty(&self, nominal_def_id: NominalDefId) -> TyId {
        self.gs
            .borrow_mut()
            .ty_store
            .create(Ty::NominalDef(nominal_def_id))
    }

    /// Create a [Value::NominalDef] from the given [NominalDefId].
    pub fn create_nominal_value(&self, nominal_def_id: NominalDefId) -> ValueId {
        self.gs
            .borrow_mut()
            .value_store
            .create(Value::NominalDef(nominal_def_id))
    }

    /// Create a [Scope], returning a [ScopeId].
    pub fn create_scope(&self, scope: Scope) -> ScopeId {
        self.gs.borrow_mut().scope_store.create(scope)
    }

    /// Create a [Scope] of kind [ScopeKind::Constant] from the given members, returning a
    /// [ScopeId].
    pub fn create_constant_scope(&self, members: impl IntoIterator<Item = Member>) -> ScopeId {
        self.create_scope(Scope::new(ScopeKind::Constant, members))
    }

    /// Create a trait definition with no name, and the given members.
    pub fn create_nameless_trait_def(&self, members: impl Iterator<Item = Member>) -> TrtDefId {
        let trt_def_id = self.gs.borrow_mut().trt_def_store.create(TrtDef {
            name: None,
            members: self.create_constant_scope(members),
        });
        trt_def_id
    }

    /// Create a trait definition with the given name, and members.
    ///
    /// This adds the name to the scope.
    pub fn create_trait_def(
        &self,
        trait_name: impl Into<Identifier>,
        members: impl IntoIterator<Item = Member>,
    ) -> TrtDefId {
        let name = trait_name.into();
        let trt_def_id = self.gs.borrow_mut().trt_def_store.create(TrtDef {
            name: Some(name),
            members: self.create_constant_scope(members),
        });
        let trt_def_ty = self.create_ty_of_trt();
        let trt_def_value = self
            .gs
            .borrow_mut()
            .value_store
            .create(Value::Trt(trt_def_id));
        self.add_pub_member_to_scope(name, trt_def_ty, trt_def_value);
        trt_def_id
    }

    /// Create a type function type with the given name, parameters, and return type.
    pub fn create_mod_def_ty(&self, mod_def_id: ModDefId) -> TyId {
        self.gs.borrow_mut().ty_store.create(Ty::ModDef(mod_def_id))
    }

    /// Create a type function type with the given name, parameters, and return type.
    pub fn create_ty_fn_ty(
        &self,
        params: impl IntoIterator<Item = Param>,
        return_ty: TyId,
    ) -> TyId {
        let params = ParamList::new(params.into_iter().collect());
        let ty_fn = TyFnTy { params, return_ty };
        self.gs.borrow_mut().ty_store.create(Ty::TyFn(ty_fn))
    }

    /// Create a type function value with the given name, parameters, return type and value.
    ///
    /// This adds the name to the scope.
    pub fn create_ty_fn_value(
        &self,
        name: impl Into<Identifier>,
        params: impl IntoIterator<Item = Param>,
        return_ty: TyId,
        return_value: ValueId,
    ) -> ValueId {
        let name = name.into();
        let params = ParamList::new(params.into_iter().collect());
        let ty_fn = TyFnValue {
            name: Some(name),
            general_params: params.clone(),
            general_return_ty: return_ty,
            cases: vec![TyFnCase {
                params: params.clone(),
                return_ty,
                return_value,
            }],
        };
        let ty_fn_value_id = self.gs.borrow_mut().value_store.create(Value::TyFn(ty_fn));
        let ty_fn_ty_id = self
            .gs
            .borrow_mut()
            .ty_store
            .create(Ty::TyFn(TyFnTy { params, return_ty }));
        self.add_pub_member_to_scope(name, ty_fn_ty_id, ty_fn_value_id);

        ty_fn_value_id
    }

    /// Create a type function application, given type function value and arguments.
    ///
    /// The `args` must all have values [Value::Ty] or end in it (if they are type functions, for
    /// example).
    pub fn create_app_ty_fn(
        &self,
        ty_fn_value_id: ValueId,
        args: impl IntoIterator<Item = Arg>,
    ) -> AppTyFn {
        AppTyFn {
            args: Args::new(args.into_iter().collect()),
            ty_fn_value: ty_fn_value_id,
        }
    }

    /// Create an argument with the given name and value.
    pub fn create_arg(&self, name: impl Into<Identifier>, value: ValueId) -> Arg {
        Arg {
            name: Some(name.into()),
            value,
        }
    }

    /// Create a type function application type, given type function value and arguments.
    ///
    /// This calls [Self::create_app_ty_fn], so its conditions apply here.
    pub fn create_app_ty_fn_ty(
        &self,
        ty_fn_value_id: ValueId,
        args: impl IntoIterator<Item = Arg>,
    ) -> TyId {
        let app_ty_fn = self.create_app_ty_fn(ty_fn_value_id, args);
        self.gs.borrow_mut().ty_store.create(Ty::AppTyFn(app_ty_fn))
    }

    /// Release [Self], returning the original [GlobalStorage].
    pub fn release(self) -> &'gs mut GlobalStorage {
        self.gs.into_inner()
    }
}
