//! Contains helper structures to create complex types and values without having to manually call
//! the corresponding stores.
use crate::storage::{
    primitives::{
        AccessTerm, AppTyFn, Arg, Args, EnumDef, EnumVariant, FnTy, GetNameOpt, Level0Term,
        Level1Term, Level2Term, Level3Term, Member, ModDefId, Mutability, NominalDef, NominalDefId,
        Param, ParamList, Scope, ScopeId, ScopeKind, StructDef, StructFields, Term, TermId, TrtDef,
        TrtDefId, TupleTy, TyFn, TyFnCase, TyFnTy, Var, Visibility,
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

    /// Create a variable with the given name.
    pub fn create_var(&self, var_name: impl Into<Identifier>) -> Var {
        Var {
            name: var_name.into(),
        }
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
    pub fn add_pub_member_to_scope(&self, name: impl Into<Identifier>, ty: TermId, value: TermId) {
        let member = self.create_pub_member(name, ty, value);
        if let Some(scope) = self.scope.get() {
            self.gs.borrow_mut().scope_store.get_mut(scope).add(member);
        }
    }

    /// Create a [Term::Access] with the given subject and name.
    pub fn create_access(&self, subject_id: TermId, name: impl Into<Identifier>) -> TermId {
        self.create_term(Term::Access(AccessTerm {
            subject_id,
            name: name.into(),
        }))
    }

    /// Create a public member with the given name, type and value.
    pub fn create_pub_member(
        &self,
        name: impl Into<Identifier>,
        ty: TermId,
        value: TermId,
    ) -> Member {
        Member {
            name: name.into(),
            ty,
            value: Some(value),
            visibility: Visibility::Public,
            mutability: Mutability::Immutable,
        }
    }

    /// Create a public member with the given name, type and unset value.
    pub fn create_unset_pub_member(&self, name: impl Into<Identifier>, ty: TermId) -> Member {
        Member {
            name: name.into(),
            ty,
            value: None,
            visibility: Visibility::Public,
            mutability: Mutability::Immutable,
        }
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

    /// Create the void type term: [Level1Term::Tuple] with no members.
    pub fn create_void_ty_term(&self) -> TermId {
        self.create_term(Term::Level1(Level1Term::Tuple(TupleTy {
            members: ParamList::new(vec![]),
        })))
    }

    /// Create a [Level0Term::Rt] of the given type.
    pub fn create_rt_term(&self, ty_term_id: TermId) -> TermId {
        self.create_term(Term::Level0(Level0Term::Rt(ty_term_id)))
    }

    /// Create a [ParamList<T>] from the given set of items.
    pub fn create_param_list<T: GetNameOpt + Clone>(
        &self,
        items: impl IntoIterator<Item = T>,
    ) -> ParamList<T> {
        ParamList::new(items.into_iter().collect())
    }

    /// Create a parameter with the given name and type.
    pub fn create_param(&self, name: impl Into<Identifier>, ty: TermId) -> Param {
        Param {
            name: Some(name.into()),
            ty,
            default_value: None,
        }
    }

    /// Create a term with the given term value.
    pub fn create_term(&self, term: Term) -> TermId {
        self.gs.borrow_mut().term_store.create(term)
    }

    /// Create a [Level1Term::Fn] term with the given parameters and return type.
    pub fn create_fn_ty_term(
        &self,
        params: impl IntoIterator<Item = Param>,
        return_ty: TermId,
    ) -> TermId {
        self.create_term(Term::Level1(Level1Term::Fn(FnTy {
            params: ParamList::new(params.into_iter().collect()),
            return_ty,
        })))
    }

    /// Create a [Level1Term::NominalDef] from the given [NominalDefId].
    pub fn create_nominal_def_term(&self, nominal_def_id: NominalDefId) -> TermId {
        self.create_term(Term::Level1(Level1Term::NominalDef(nominal_def_id)))
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
        let trt_def_ty = self.create_trt_kind_term();
        let trt_def_value = self.create_trt_term(trt_def_id);
        self.add_pub_member_to_scope(name, trt_def_ty, trt_def_value);
        trt_def_id
    }

    /// Create [Level1Term::ModDef] with the given [ModDefId].
    pub fn create_mod_def_term(&self, mod_def_id: ModDefId) -> TermId {
        self.create_term(Term::Level1(Level1Term::ModDef(mod_def_id)))
    }

    /// Create a type function type term with the given name, parameters, and return type.
    pub fn create_ty_fn_ty_term(
        &self,
        params: impl IntoIterator<Item = Param>,
        return_ty: TermId,
    ) -> TermId {
        let params = ParamList::new(params.into_iter().collect());
        let ty_fn = TyFnTy { params, return_ty };
        self.create_term(Term::TyFnTy(ty_fn))
    }

    /// Create a type function term with the given name, parameters, return type and value.
    ///
    /// This adds the name to the scope.
    pub fn create_ty_fn_term(
        &self,
        name: impl Into<Identifier>,
        params: impl IntoIterator<Item = Param>,
        return_ty: TermId,
        return_value: TermId,
    ) -> TermId {
        let name = name.into();
        let params = ParamList::new(params.into_iter().collect());
        let ty_fn = TyFn {
            name: Some(name),
            general_params: params.clone(),
            general_return_ty: return_ty,
            cases: vec![TyFnCase {
                params: params.clone(),
                return_ty,
                return_value,
            }],
        };
        let ty_fn_id = self.create_term(Term::TyFn(ty_fn));
        let ty_fn_ty_id = self.create_term(Term::TyFnTy(TyFnTy { params, return_ty }));
        self.add_pub_member_to_scope(name, ty_fn_ty_id, ty_fn_id);

        ty_fn_id
    }

    /// Create a type function application, given type function value and arguments.
    pub fn create_app_ty_fn(
        &self,
        ty_fn_value_id: TermId,
        args: impl IntoIterator<Item = Arg>,
    ) -> AppTyFn {
        AppTyFn {
            args: Args::new(args.into_iter().collect()),
            subject: ty_fn_value_id,
        }
    }

    /// Create an argument with the given name and value.
    pub fn create_arg(&self, name: impl Into<Identifier>, value: TermId) -> Arg {
        Arg {
            name: Some(name.into()),
            value,
        }
    }

    /// Create a type function application type, given type function value and arguments.
    ///
    /// This calls [Self::create_app_ty_fn], so its conditions apply here.
    pub fn create_app_ty_fn_term(
        &self,
        ty_fn_value_id: TermId,
        args: impl IntoIterator<Item = Arg>,
    ) -> TermId {
        let app_ty_fn = self.create_app_ty_fn(ty_fn_value_id, args);
        self.create_term(Term::AppTyFn(app_ty_fn))
    }

    /// Release [Self], returning the original [GlobalStorage].
    pub fn release(self) -> &'gs mut GlobalStorage {
        self.gs.into_inner()
    }
}
