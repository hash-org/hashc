//! Contains helper structures to create complex types and values without having
//! to manually call the corresponding stores.
use crate::storage::{
    location::LocationTarget,
    primitives::{
        AccessOp, AccessTerm, AppSub, Arg, ArgsId, EnumDef, EnumVariant, EnumVariantValue, FnCall,
        FnLit, FnTy, Level0Term, Level1Term, Level2Term, Level3Term, Member, MemberData, ModDef,
        ModDefId, ModDefOrigin, Mutability, NominalDef, NominalDefId, Param, ParamList,
        ParamOrigin, ParamsId, Scope, ScopeId, ScopeKind, StructDef, StructFields, Sub, Term,
        TermId, TrtDef, TrtDefId, TupleTy, TyFn, TyFnCall, TyFnCase, TyFnTy, UnresolvedTerm, Var,
        Visibility,
    },
    GlobalStorage,
};
use hash_source::{identifier::Identifier, location::SourceLocation};
use std::cell::{Cell, RefCell};

/// Helper to create various primitive constructions (from
/// [crate::storage::primitives]).
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
        Self { gs: RefCell::new(gs), scope: Cell::new(None) }
    }

    /// Release [Self], returning the original [GlobalStorage].
    pub fn release(self) -> &'gs mut GlobalStorage {
        self.gs.into_inner()
    }

    /// Create a new [PrimitiveBuilder] with a given scope.
    ///
    /// This adds every constructed item into the scope with their given names
    /// (if any).
    pub fn new_with_scope(gs: &'gs mut GlobalStorage, scope: ScopeId) -> Self {
        Self { gs: RefCell::new(gs), scope: Cell::new(Some(scope)) }
    }

    /// Create a variable with the given name.
    pub fn create_var(&self, var_name: impl Into<Identifier>) -> Var {
        Var { name: var_name.into() }
    }

    /// Create a variable with the given name, in the form of a [Term::Var].
    pub fn create_var_term(&self, var_name: impl Into<Identifier>) -> TermId {
        let var = self.create_var(var_name);
        self.create_term(Term::Var(var))
    }

    /// Add the given nominal definition to the scope.
    fn add_nominal_def_to_scope(&self, name: Identifier, def_id: NominalDefId) {
        let def_ty = self.create_any_ty_term();
        let def_value = self.create_term(Term::Level1(Level1Term::NominalDef(def_id)));
        self.add_pub_member_to_scope(name, def_ty, def_value);
    }

    /// Add the given module definition to the scope.
    fn add_mod_def_to_scope(&self, name: Identifier, def_id: ModDefId, origin: ModDefOrigin) {
        let def_ty = match origin {
            ModDefOrigin::TrtImpl(trt_id) => trt_id,
            _ => self.create_any_ty_term(),
        };
        let def_value = self.create_term(Term::Level1(Level1Term::ModDef(def_id)));
        self.add_pub_member_to_scope(name, def_ty, def_value);
    }

    /// Create a named module definition with the given name, members, and
    /// origin.
    ///
    /// This adds the name to the scope.
    pub fn create_named_mod_def(
        &self,
        name: impl Into<Identifier>,
        origin: ModDefOrigin,
        members: ScopeId,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> ModDefId {
        self.create_mod_def(Some(name), origin, members, bound_vars)
    }

    /// Create a nameless module definition with the given members, and origin.
    pub fn create_nameless_mod_def(
        &self,
        origin: ModDefOrigin,
        members: ScopeId,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> ModDefId {
        self.create_mod_def(Option::<Identifier>::None, origin, members, bound_vars)
    }

    /// Create a module definition with the given optional name, members, and
    /// origin.
    pub fn create_mod_def(
        &self,
        name: Option<impl Into<Identifier>>,
        origin: ModDefOrigin,
        members: ScopeId,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> ModDefId {
        let name = name.map(Into::into);
        let def_id = self.gs.borrow_mut().mod_def_store.create(ModDef {
            name,
            members,
            origin,
            bound_vars: bound_vars.into_iter().collect(),
        });
        if let Some(name) = name {
            self.add_mod_def_to_scope(name, def_id, origin);
        }
        def_id
    }

    /// Create a nameless struct with opaque fields.
    pub fn create_nameless_opaque_struct_def(
        &self,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> NominalDefId {
        let def_id = self.gs.borrow_mut().nominal_def_store.create(NominalDef::Struct(StructDef {
            name: None,
            fields: StructFields::Opaque,
            bound_vars: bound_vars.into_iter().collect(),
        }));
        def_id
    }

    /// Create a struct with the given name and opaque fields.
    ///
    /// This adds the name to the scope.
    pub fn create_opaque_struct_def(
        &self,
        struct_name: impl Into<Identifier>,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> NominalDefId {
        let name = struct_name.into();
        let def_id = self.gs.borrow_mut().nominal_def_store.create(NominalDef::Struct(StructDef {
            name: Some(name),
            fields: StructFields::Opaque,
            bound_vars: bound_vars.into_iter().collect(),
        }));
        self.add_nominal_def_to_scope(name, def_id);
        def_id
    }

    /// Create a struct with the given name and fields.
    ///
    /// This adds the name to the scope.
    pub fn create_struct_def(
        &self,
        struct_name: Option<impl Into<Identifier>>,
        fields: ParamsId,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> NominalDefId {
        match struct_name {
            Some(name) => self.create_named_struct_def(name, fields, bound_vars),
            None => self.create_nameless_struct_def(fields, bound_vars),
        }
    }

    pub fn create_named_struct_def(
        &self,
        struct_name: impl Into<Identifier>,
        fields: ParamsId,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> NominalDefId {
        let name = struct_name.into();
        let def_id = self.gs.borrow_mut().nominal_def_store.create(NominalDef::Struct(StructDef {
            name: Some(name),
            fields: StructFields::Explicit(fields),
            bound_vars: bound_vars.into_iter().collect(),
        }));

        self.add_nominal_def_to_scope(name, def_id);
        def_id
    }

    pub fn create_nameless_struct_def(
        &self,
        fields: ParamsId,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> NominalDefId {
        let def_id = self.gs.borrow_mut().nominal_def_store.create(NominalDef::Struct(StructDef {
            name: None,
            fields: StructFields::Explicit(fields),
            bound_vars: bound_vars.into_iter().collect(),
        }));

        def_id
    }

    /// Create an enum variant value term ([Level0Term::EnumVariant]).
    pub fn create_enum_variant_value_term(
        &self,
        variant_name: impl Into<Identifier>,
        enum_def_id: NominalDefId,
    ) -> TermId {
        self.create_term(Term::Level0(Level0Term::EnumVariant(EnumVariantValue {
            variant_name: variant_name.into(),
            enum_def_id,
        })))
    }

    /// Create an enum variant.
    pub fn create_enum_variant(
        &self,
        name: impl Into<Identifier>,
        fields: ParamsId,
    ) -> EnumVariant {
        EnumVariant { name: name.into(), fields }
    }

    /// Create an enum with the given name and variants.
    ///
    /// This adds the name to the scope.
    pub fn create_enum_def(
        &self,
        enum_name: Option<impl Into<Identifier>>,
        variants: impl IntoIterator<Item = EnumVariant>,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> NominalDefId {
        let name = enum_name.map(|name| name.into());

        // let name = enum_name.into();
        let def_id = self.gs.borrow_mut().nominal_def_store.create(NominalDef::Enum(EnumDef {
            name,
            variants: variants.into_iter().map(|variant| (variant.name, variant)).collect(),
            bound_vars: bound_vars.into_iter().collect(),
        }));

        // Only add the enum def to the scope if it has a name...
        if let Some(name) = name {
            self.add_nominal_def_to_scope(name, def_id);
        }

        def_id
    }

    /// Add a member to the scope, marking it as public.
    ///
    /// All other methods call this one to actually add members to the scope.
    pub fn add_pub_member_to_scope(&self, name: impl Into<Identifier>, ty: TermId, value: TermId) {
        let member = self.create_constant_member(name, ty, value, Visibility::Public);
        if let Some(scope) = self.scope.get() {
            self.gs.borrow_mut().scope_store.get_mut(scope).add(member);
        }
    }

    /// Create a [Term::Access] with the given subject and name, and namespace
    /// operator.
    pub fn create_ns_access(&self, subject_id: TermId, name: impl Into<Identifier>) -> TermId {
        self.create_term(Term::Access(AccessTerm {
            subject: subject_id,
            name: name.into(),
            op: AccessOp::Namespace,
        }))
    }

    /// Create a [Term::Access] with the given subject and name, and property
    /// operator.
    pub fn create_prop_access(&self, subject_id: TermId, name: impl Into<Identifier>) -> TermId {
        self.create_term(Term::Access(AccessTerm {
            subject: subject_id,
            name: name.into(),
            op: AccessOp::Property,
        }))
    }

    /// Create a member of a variable scope (private and immutable), with the
    /// given name, type and value.
    pub fn create_variable_member(
        &self,
        name: impl Into<Identifier>,
        ty: TermId,
        value: TermId,
    ) -> Member {
        Member {
            name: name.into(),
            data: MemberData::InitialisedWithTy { ty, value },
            visibility: Visibility::Private,
            mutability: Mutability::Immutable,
        }
    }

    /// Create a public member with the given name, type and value.
    pub fn create_constant_member(
        &self,
        name: impl Into<Identifier>,
        ty: TermId,
        value: TermId,
        visibility: Visibility,
    ) -> Member {
        Member {
            name: name.into(),
            data: MemberData::InitialisedWithTy { ty, value },
            visibility,
            mutability: Mutability::Immutable,
        }
    }

    /// Create a public member with the given name, type and unset value.
    pub fn create_uninitialised_constant_member(
        &self,
        name: impl Into<Identifier>,
        ty: TermId,
        visibility: Visibility,
    ) -> Member {
        Member {
            name: name.into(),
            data: MemberData::Uninitialised { ty },
            visibility,
            mutability: Mutability::Immutable,
        }
    }

    /// Create a [Term::Root].
    pub fn create_root_term(&self) -> TermId {
        self.create_term(Term::Root)
    }

    /// Create a term [Level3Term::TrtKind].
    pub fn create_trt_kind_term(&self) -> TermId {
        self.create_term(Term::Level3(Level3Term::TrtKind))
    }

    /// Create a term [Level2Term::AnyTy].
    pub fn create_any_ty_term(&self) -> TermId {
        self.create_term(Term::Level2(Level2Term::AnyTy))
    }

    /// Create a term [Level2Term::Trt] with the given [TrtDefId].
    pub fn create_trt_term(&self, trt_def_id: TrtDefId) -> TermId {
        self.create_term(Term::Level2(Level2Term::Trt(trt_def_id)))
    }

    /// Create a term [Term::Merge] with the given inner terms.
    pub fn create_merge_term(&self, terms: impl IntoIterator<Item = TermId>) -> TermId {
        self.create_term(Term::Merge(terms.into_iter().collect()))
    }

    /// Create a term [Term::Union] with the given inner terms.
    pub fn create_union_term(&self, terms: impl IntoIterator<Item = TermId>) -> TermId {
        self.create_term(Term::Union(terms.into_iter().collect()))
    }

    /// Create the void type term: [Level1Term::Tuple] with no members.
    pub fn create_void_ty_term(&self) -> TermId {
        self.create_term(Term::Level1(Level1Term::Tuple(TupleTy {
            members: self.create_params([], ParamOrigin::Tuple),
        })))
    }

    /// Create the never term: [Term::Union] with no members.
    pub fn create_never_term(&self) -> TermId {
        self.create_term(Term::Union(vec![]))
    }

    /// Create a tuple type term [Level1Term::Tuple].
    pub fn create_tuple_ty_term(&self, members: ParamsId) -> TermId {
        self.create_term(Term::Level1(Level1Term::Tuple(TupleTy { members })))
    }

    /// Create a [Level0Term::Rt] of the given type.
    pub fn create_rt_term(&self, ty_term_id: TermId) -> TermId {
        self.create_term(Term::Level0(Level0Term::Rt(ty_term_id)))
    }

    /// Create a [Level0Term::FnLit] of the given function type and return
    /// value.
    pub fn create_fn_lit_term(&self, fn_ty: TermId, return_value: TermId) -> TermId {
        self.create_term(Term::Level0(Level0Term::FnLit(FnLit { fn_ty, return_value })))
    }

    /// Create a [Level0Term::FnCall] term with the given subject and arguments.
    pub fn create_fn_call_term(&self, subject: TermId, args: ArgsId) -> TermId {
        self.create_term(Term::Level0(Level0Term::FnCall(FnCall { subject, args })))
    }

    /// Create a parameter with the given name and type.
    pub fn create_param(&self, name: impl Into<Identifier>, ty: TermId) -> Param {
        Param { name: Some(name.into()), ty, default_value: None }
    }

    /// Create a term with the given term value.
    pub fn create_term(&self, term: Term) -> TermId {
        self.gs.borrow_mut().term_store.create(term)
    }

    /// Create a [Level1Term::Fn] term with the given parameters and return
    /// type.
    pub fn create_fn_ty_term(&self, params: ParamsId, return_ty: TermId) -> TermId {
        self.create_term(Term::Level1(Level1Term::Fn(FnTy { params, return_ty })))
    }

    /// Create a [Level1Term::NominalDef] from the given [NominalDefId].
    pub fn create_nominal_def_term(&self, nominal_def_id: NominalDefId) -> TermId {
        self.create_term(Term::Level1(Level1Term::NominalDef(nominal_def_id)))
    }

    /// Create a [Scope], returning a [ScopeId].
    pub fn create_scope(&self, scope: Scope) -> ScopeId {
        self.gs.borrow_mut().scope_store.create(scope)
    }

    /// Create a [Scope] of kind [ScopeKind::Variable] from the given members,
    /// returning a [ScopeId].
    pub fn create_variable_scope(&self, members: impl IntoIterator<Item = Member>) -> ScopeId {
        self.create_scope(Scope::new(ScopeKind::Variable, members))
    }

    /// Create a [Scope] of kind [ScopeKind::Constant] from the given members,
    /// returning a [ScopeId].
    pub fn create_constant_scope(&self, members: impl IntoIterator<Item = Member>) -> ScopeId {
        self.create_scope(Scope::new(ScopeKind::Constant, members))
    }

    /// Create a trait definition either being named or nameless.
    pub fn create_trt_def(
        &self,
        trait_name: Option<impl Into<Identifier>>,
        members: impl IntoIterator<Item = Member>,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> TrtDefId {
        let name = trait_name.map(|t| t.into());

        let trt_def_id = self.gs.borrow_mut().trt_def_store.create(TrtDef {
            name,
            members: self.create_constant_scope(members),
            bound_vars: bound_vars.into_iter().collect(),
        });
        let trt_def_ty = self.create_trt_kind_term();
        let trt_def_value = self.create_trt_term(trt_def_id);

        if let Some(name) = name {
            self.add_pub_member_to_scope(name, trt_def_ty, trt_def_value);
        }

        trt_def_id
    }

    /// Create a trait definition with no name, and the given members.
    pub fn create_nameless_trt_def(
        &self,
        members: impl Iterator<Item = Member>,
        bound_vars: impl IntoIterator<Item = Var>,
    ) -> TrtDefId {
        let trt_def_id = self.gs.borrow_mut().trt_def_store.create(TrtDef {
            name: None,
            members: self.create_constant_scope(members),
            bound_vars: bound_vars.into_iter().collect(),
        });
        trt_def_id
    }

    /// Create [Level1Term::ModDef] with the given [ModDefId].
    pub fn create_mod_def_term(&self, mod_def_id: ModDefId) -> TermId {
        self.create_term(Term::Level1(Level1Term::ModDef(mod_def_id)))
    }

    /// Create a type function type term with the given name, parameters, and
    /// return type.
    pub fn create_ty_fn_ty_term(&self, params: ParamsId, return_ty: TermId) -> TermId {
        let ty_fn = TyFnTy { params, return_ty };
        self.create_term(Term::TyFnTy(ty_fn))
    }

    /// Create a [ParamsId] from an iterator of [Param]. This function wil
    /// create a [Params], append it to the store and return  the created
    /// id.
    pub fn create_params(
        &self,
        params: impl IntoIterator<Item = Param>,
        origin: ParamOrigin,
    ) -> ParamsId {
        self.gs
            .borrow_mut()
            .params_store
            .create(ParamList::new(params.into_iter().collect(), origin))
    }

    /// Create a [ArgsId] from an iterator of [Arg]. This function wil create a
    /// [Args], append it to the store and return  the created id.
    pub fn create_args(&self, args: impl IntoIterator<Item = Arg>, origin: ParamOrigin) -> ArgsId {
        self.gs.borrow_mut().args_store.create(ParamList::new(args.into_iter().collect(), origin))
    }

    /// Create a nameless type function term with parameters, return type and
    /// value.
    ///
    /// This adds the name to the scope.
    pub fn create_nameless_ty_fn_term(
        &self,
        params: ParamsId,
        return_ty: TermId,
        return_value: TermId,
    ) -> TermId {
        self.create_ty_fn_term(Option::<Identifier>::None, params, return_ty, return_value)
    }

    /// Create a named type function term with parameters, return type and
    /// value.
    ///
    /// This adds the name to the scope.
    pub fn create_named_ty_fn_term(
        &self,
        name: impl Into<Identifier>,
        params: ParamsId,
        return_ty: TermId,
        return_value: TermId,
    ) -> TermId {
        self.create_ty_fn_term(Some(name), params, return_ty, return_value)
    }

    /// Create a type function term with the given optional name, parameters,
    /// return type and value.
    ///
    /// This adds the name to the scope.
    pub fn create_ty_fn_term(
        &self,
        name: Option<impl Into<Identifier>>,
        params: ParamsId,
        return_ty: TermId,
        return_value: TermId,
    ) -> TermId {
        let name = name.map(Into::into);
        let ty_fn = TyFn {
            name,
            general_params: params,
            general_return_ty: return_ty,
            cases: vec![TyFnCase { params, return_ty, return_value }],
        };
        let ty_fn_id = self.create_term(Term::TyFn(ty_fn));
        let ty_fn_ty_id = self.create_term(Term::TyFnTy(TyFnTy { params, return_ty }));
        if let Some(name) = name {
            self.add_pub_member_to_scope(name, ty_fn_ty_id, ty_fn_id);
        }
        ty_fn_id
    }

    /// Create a type function application, given type function value and
    /// arguments.
    pub fn create_app_ty_fn(&self, subject: TermId, args: ArgsId) -> TyFnCall {
        TyFnCall { args, subject }
    }

    /// Create a new unresolved term value, of type [Term::Unresolved].
    pub fn create_unresolved(&self) -> UnresolvedTerm {
        let resolution_id = self.gs.borrow().term_store.new_resolution_id();
        UnresolvedTerm { resolution_id }
    }

    /// Create a new unresolved term, of type [Term::Unresolved].
    pub fn create_unresolved_term(&self) -> TermId {
        self.create_term(Term::Unresolved(self.create_unresolved()))
    }

    /// Create a new unresolved term, of type [Term::Unresolved], if the given
    /// term is `None`.
    pub fn or_unresolved_term(&self, existing: Option<TermId>) -> TermId {
        existing.unwrap_or_else(|| self.create_unresolved_term())
    }

    /// Create a substitution application term, given a substitution and inner
    /// term.
    ///
    /// If no elements exist in the substitution, returns the term itself
    /// without wrapping it.
    pub fn create_app_sub_term(&self, sub: Sub, term: TermId) -> TermId {
        if sub.map().is_empty() {
            term
        } else {
            self.create_term(Term::AppSub(AppSub { sub, term }))
        }
    }

    /// Create an argument with the given name and value.
    pub fn create_arg(&self, name: impl Into<Identifier>, value: TermId) -> Arg {
        Arg { name: Some(name.into()), value }
    }

    /// Create a type function application type, given type function value and
    /// arguments.
    ///
    /// This calls [Self::create_app_ty_fn], so its conditions apply here.
    pub fn create_app_ty_fn_term(&self, subject: TermId, args: ArgsId) -> TermId {
        let app_ty_fn = self.create_app_ty_fn(subject, args);
        self.create_term(Term::TyFnCall(app_ty_fn))
    }

    /// Add a [SourceLocation] to a [LocationTarget].
    ///
    /// This is added so that locations can be added without having to destroy
    /// the current builder first (because it has mutable access to
    /// [GlobalStorage]).
    pub fn add_location_to_target(
        &self,
        target: impl Into<LocationTarget>,
        location: SourceLocation,
    ) {
        self.gs.borrow_mut().location_store.add_location_to_target(target, location);
    }
}
