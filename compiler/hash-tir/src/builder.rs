//! Contains helper structures to create complex types and values without having
//! to manually call the corresponding stores.
use std::cell::Cell;

use hash_ast::ast::ParamOrigin;
use hash_source::{identifier::Identifier, location::SourceLocation};
use hash_utils::store::{SequenceStore, Store};

use crate::{
    args::{Arg, ArgsId},
    location::LocationTarget,
    mods::{ModDef, ModDefId, ModDefOrigin},
    nominals::{
        EnumDef, EnumVariant, EnumVariantValue, NominalDef, NominalDefId, StructDef, StructFields,
        UnitDef,
    },
    params::{AccessOp, Field, Param, ParamsId},
    pats::{
        AccessPat, ArrayPat, BindingPat, ConstPat, ConstructorPat, IfPat, ModPat, Pat, PatArg,
        PatArgsId, PatId, RangePat,
    },
    scope::{
        BoundVar, Member, Mutability, Scope, ScopeId, ScopeKind, ScopeVar, SetBound, Var,
        Visibility,
    },
    storage::GlobalStorage,
    terms::{
        AccessTerm, ConstructedTerm, FnCall, FnLit, FnTy, Level0Term, Level1Term, Level2Term,
        Level3Term, LitTerm, Term, TermId, TupleLit, TupleTy, TyFn, TyFnCall, TyFnCase, TyFnTy,
        UnresolvedTerm,
    },
    trts::{TrtDef, TrtDefId},
};

/// Helper to create various primitive constructions (from [crate]).
///
/// Optionally adds the constructions to a scope, if given.
pub struct PrimitiveBuilder<'gs> {
    // Keep these in RefCells so that calls to [PrimitiveBuilder] can be nested without borrowing
    // issues.
    //
    // *Important*: Should ensure that each method starts and ends the borrow within itself and
    // doesn't call any other methods in between, otherwise it will cause a panic.
    gs: &'gs GlobalStorage,
    scope: Cell<Option<ScopeId>>,
}

impl<'gs> PrimitiveBuilder<'gs> {
    /// Create a new [PrimitiveBuilder] with a given scope.
    pub fn new(gs: &'gs GlobalStorage) -> Self {
        Self { gs, scope: Cell::new(None) }
    }

    /// Create a new [PrimitiveBuilder] with a given scope.
    ///
    /// This adds every constructed item into the scope with their given names
    /// (if any).
    pub fn new_with_scope(gs: &'gs GlobalStorage, scope: ScopeId) -> Self {
        Self { gs, scope: Cell::new(Some(scope)) }
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

    /// Create a bound variable with the given name.
    pub fn create_bound_var_term(&self, name: impl Into<Identifier>) -> TermId {
        self.create_term(Term::BoundVar(BoundVar { name: name.into() }))
    }

    /// Create a scope variable with the given name, scope and index.
    pub fn create_scope_var_term(
        &self,
        name: impl Into<Identifier>,
        scope: ScopeId,
        index: usize,
    ) -> TermId {
        self.create_term(Term::ScopeVar(ScopeVar { name: name.into(), scope, index }))
    }

    /// Add the given nominal definition to the scope.
    fn add_nominal_def_to_scope(&self, name: Identifier, def_id: NominalDefId) {
        let def_ty = self.create_sized_ty_term();
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
    ) -> ModDefId {
        self.create_mod_def(Some(name), origin, members)
    }

    /// Create a nameless module definition with the given members, and origin.
    pub fn create_nameless_mod_def(&self, origin: ModDefOrigin, members: ScopeId) -> ModDefId {
        self.create_mod_def(Option::<Identifier>::None, origin, members)
    }

    /// Create a unit definition with an optional name.
    pub fn create_unit_def(&self, name: Option<Identifier>) -> NominalDefId {
        let def_id = self.gs.nominal_def_store.create(NominalDef::Unit(UnitDef { name }));
        if let Some(name) = name {
            self.add_nominal_def_to_scope(name, def_id);
        }
        def_id
    }

    /// Create a named unit definition.
    pub fn create_named_unit_def(&self, name: impl Into<Identifier>) -> NominalDefId {
        self.create_unit_def(Some(name.into()))
    }

    /// Create a nameless unit definition.
    pub fn create_nameless_unit_def(&self) -> NominalDefId {
        self.create_unit_def(None)
    }

    /// Create a module definition with the given optional name, members, and
    /// origin.
    pub fn create_mod_def(
        &self,
        name: Option<impl Into<Identifier>>,
        origin: ModDefOrigin,
        members: ScopeId,
    ) -> ModDefId {
        let name = name.map(Into::into);
        let def_id = self.gs.mod_def_store.create(ModDef { name, members, origin });
        if let Some(name) = name {
            self.add_mod_def_to_scope(name, def_id, origin);
        }
        def_id
    }

    /// Create a nameless struct with opaque fields.
    pub fn create_nameless_opaque_struct_def(&self) -> NominalDefId {
        self.gs
            .nominal_def_store
            .create(NominalDef::Struct(StructDef { name: None, fields: StructFields::Opaque }))
    }

    /// Create a struct with the given name and opaque fields.
    ///
    /// This adds the name to the scope.
    pub fn create_opaque_struct_def(&self, struct_name: impl Into<Identifier>) -> NominalDefId {
        let name = struct_name.into();
        let def_id = self.gs.nominal_def_store.create(NominalDef::Struct(StructDef {
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
        struct_name: Option<impl Into<Identifier>>,
        fields: ParamsId,
    ) -> NominalDefId {
        match struct_name {
            Some(name) => self.create_named_struct_def(name, fields),
            None => self.create_nameless_struct_def(fields),
        }
    }

    pub fn create_named_struct_def(
        &self,
        struct_name: impl Into<Identifier>,
        fields: ParamsId,
    ) -> NominalDefId {
        let name = struct_name.into();
        let def_id = self.gs.nominal_def_store.create(NominalDef::Struct(StructDef {
            name: Some(name),
            fields: StructFields::Explicit(fields),
        }));

        self.add_nominal_def_to_scope(name, def_id);
        def_id
    }

    pub fn create_nameless_struct_def(&self, fields: ParamsId) -> NominalDefId {
        self.gs.nominal_def_store.create(NominalDef::Struct(StructDef {
            name: None,
            fields: StructFields::Explicit(fields),
        }))
    }

    /// Create an enum variant value term ([Level0Term::EnumVariant]).
    pub fn create_enum_variant_value_term(
        &self,
        variant_name: impl Into<Identifier>,
        enum_def_id: NominalDefId,
    ) -> TermId {
        self.create_term(Term::Level0(Level0Term::EnumVariant(EnumVariantValue {
            name: variant_name.into(),
            def_id: enum_def_id,
        })))
    }

    /// Create an enum variant with no fields.
    pub fn create_constant_enum_variant(&self, name: impl Into<Identifier>) -> EnumVariant {
        EnumVariant { name: name.into(), fields: None }
    }

    /// Create an enum variant.
    pub fn create_enum_variant(
        &self,
        name: impl Into<Identifier>,
        fields: ParamsId,
    ) -> EnumVariant {
        EnumVariant { name: name.into(), fields: Some(fields) }
    }

    /// Create an enum with the given name and variants.
    ///
    /// This adds the name to the scope.
    pub fn create_enum_def(
        &self,
        enum_name: Option<impl Into<Identifier>>,
        variants: impl IntoIterator<Item = EnumVariant>,
    ) -> NominalDefId {
        let name = enum_name.map(|name| name.into());
        let variants = variants.into_iter().map(|variant| (variant.name, variant)).collect();

        // let name = enum_name.into();
        let def_id = self.gs.nominal_def_store.create(NominalDef::Enum(EnumDef { name, variants }));

        // Only add the enum def to the scope if it has a name...
        if let Some(name) = name {
            self.add_nominal_def_to_scope(name, def_id);
        }

        def_id
    }

    /// Create a [Term::TyOf].
    pub fn create_ty_of_term(&self, inner: TermId) -> TermId {
        self.create_term(Term::TyOf(inner))
    }

    /// Add an closed member to the scope, marking it as public.
    ///
    /// All other methods call this one to actually add members to the scope.
    pub fn add_pub_member_to_scope(&self, name: impl Into<Identifier>, ty: TermId, value: TermId) {
        let member = Member::closed_constant(name.into(), Visibility::Public, ty, value);
        if let Some(scope) = self.scope.get() {
            self.gs.scope_store.modify_fast(scope, |scope| scope.add(member));
        }
    }

    /// Create a [Term::Access] with the given subject and name, and an access
    /// operator.
    pub fn create_access(
        &self,
        subject_id: TermId,
        name: impl Into<Field>,
        op: AccessOp,
    ) -> TermId {
        self.create_term(Term::Access(AccessTerm { subject: subject_id, name: name.into(), op }))
    }

    /// Create a [Term::Access] with the given subject and name, and namespace
    /// operator.
    pub fn create_ns_access(&self, subject_id: TermId, field: impl Into<Field>) -> TermId {
        self.create_term(Term::Access(AccessTerm {
            subject: subject_id,
            name: field.into(),
            op: AccessOp::Namespace,
        }))
    }

    /// Create a [Term::Access] with the given subject and name, and property
    /// operator.
    pub fn create_prop_access(&self, subject_id: TermId, field: impl Into<Field>) -> TermId {
        self.create_term(Term::Access(AccessTerm {
            subject: subject_id,
            name: field.into(),
            op: AccessOp::Property,
        }))
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

    /// Create a term [Level2Term::SizedTy].
    pub fn create_sized_ty_term(&self) -> TermId {
        self.create_term(Term::Level2(Level2Term::SizedTy))
    }

    /// Create a term [Level2Term::Trt] with the given [TrtDefId].
    pub fn create_trt_term(&self, trt_def_id: TrtDefId) -> TermId {
        self.create_term(Term::Level2(Level2Term::Trt(trt_def_id)))
    }

    /// Create a term [Term::Merge] with the given inner terms.
    pub fn create_merge_term(&self, terms: impl IntoIterator<Item = TermId>) -> TermId {
        let terms = self.gs.term_list_store.create_from_iter(terms);
        self.create_term(Term::Merge(terms))
    }

    /// Create a term [Term::Union] with the given inner terms.
    pub fn create_union_term(&self, terms: impl IntoIterator<Item = TermId>) -> TermId {
        let terms = self.gs.term_list_store.create_from_iter(terms);
        self.create_term(Term::Union(terms))
    }

    /// Create a term [Level0Term::Unit] from the given nominal definition ID.
    pub fn create_unit_term(&self, unit_id: NominalDefId) -> TermId {
        self.create_term(Term::Level0(Level0Term::Unit(unit_id)))
    }

    /// Create the void type term: [Level1Term::Tuple] with no members.
    pub fn create_void_ty_term(&self) -> TermId {
        self.create_term(Term::Level1(Level1Term::Tuple(TupleTy {
            members: self.create_params([], ParamOrigin::Tuple),
        })))
    }

    /// Create the void term: [Level0Term::Tuple] with no members.
    pub fn create_void_term(&self) -> TermId {
        self.create_term(Term::Level0(Level0Term::Tuple(TupleLit {
            members: self.create_args([], ParamOrigin::Tuple),
        })))
    }

    /// Create the never type: [Term::Union] with no members.
    pub fn create_never_ty(&self) -> TermId {
        let terms = self.gs.term_list_store.create_from_slice(&[]);
        self.create_term(Term::Union(terms))
    }

    /// Create a tuple type term [Level1Term::Tuple].
    pub fn create_tuple_ty_term(&self, members: ParamsId) -> TermId {
        self.create_term(Term::Level1(Level1Term::Tuple(TupleTy { members })))
    }

    /// Create a tuple literal term [Level0Term::Tuple].
    pub fn create_tuple_lit_term(&self, members: ArgsId) -> TermId {
        self.create_term(Term::Level0(Level0Term::Tuple(TupleLit { members })))
    }

    /// Create a tuple literal term [Level0Term::Constructed].
    pub fn create_constructed_term(&self, subject: TermId, members: ArgsId) -> TermId {
        self.create_term(Term::Level0(Level0Term::Constructed(ConstructedTerm {
            subject,
            members,
        })))
    }

    /// Create a [Level0Term::Rt] of the given type.
    pub fn create_rt_term(&self, ty_term_id: TermId) -> TermId {
        self.create_term(Term::Level0(Level0Term::Rt(ty_term_id)))
    }

    /// Create a [Level0Term::Lit] of the given value.
    pub fn create_lit_term(&self, lit: impl Into<LitTerm>) -> TermId {
        self.create_term(Term::Level0(Level0Term::Lit(lit.into())))
    }

    /// Create a [Level0Term::FnLit] of the given function type and return
    /// value.
    pub fn create_fn_lit_term(
        &self,
        name: Option<Identifier>,
        fn_ty: TermId,
        return_value: TermId,
    ) -> TermId {
        self.create_term(Term::Level0(Level0Term::FnLit(FnLit { name, fn_ty, return_value })))
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
        self.gs.term_store.create(term)
    }

    /// Create a pattern with the given pattern value.
    pub fn create_pat(&self, pat: Pat) -> PatId {
        self.gs.pat_store.create(pat)
    }

    /// Create a [Level1Term::Fn] term with the given parameters and return
    /// type.
    pub fn create_fn_ty_term(
        &self,
        name: Option<Identifier>,
        params: ParamsId,
        return_ty: TermId,
    ) -> TermId {
        self.create_term(Term::Level1(Level1Term::Fn(FnTy { name, params, return_ty })))
    }

    /// Create a [Level1Term::NominalDef] from the given [NominalDefId].
    pub fn create_nominal_def_term(&self, nominal_def_id: NominalDefId) -> TermId {
        self.create_term(Term::Level1(Level1Term::NominalDef(nominal_def_id)))
    }

    /// Create a [Scope], returning a [ScopeId].
    pub fn create_scope(
        &self,
        kind: ScopeKind,
        members: impl IntoIterator<Item = Member>,
    ) -> ScopeId {
        let scope = Scope::new(kind, members);
        self.gs.scope_store.create(scope)
    }

    /// Create a trait definition either being named or nameless.
    pub fn create_trt_def(
        &self,
        trait_name: Option<impl Into<Identifier>>,
        members: ScopeId,
    ) -> TrtDefId {
        let name = trait_name.map(|t| t.into());

        let trt_def_id = self.gs.trt_def_store.create(TrtDef { name, members });
        let trt_def_ty = self.create_trt_kind_term();
        let trt_def_value = self.create_trt_term(trt_def_id);

        if let Some(name) = name {
            self.add_pub_member_to_scope(name, trt_def_ty, trt_def_value);
        }

        trt_def_id
    }

    /// Create a trait definition with no name, and the given members.
    pub fn create_nameless_trt_def(&self, members: impl Iterator<Item = Member>) -> TrtDefId {
        let members = self.create_scope(ScopeKind::Trait, members);

        self.gs.trt_def_store.create(TrtDef { name: None, members })
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

    /// Create a [ParamsId] from an iterator of [Param]. This function will
    /// create a [Params](crate::Params), append it to the store and return the
    /// created id.
    pub fn create_params(
        &self,
        params: impl IntoIterator<Item = Param>,
        origin: ParamOrigin,
    ) -> ParamsId {
        let params_id = self.gs.params_store.create_from_iter(params);
        self.gs.params_store.set_origin(params_id, origin);
        params_id
    }

    /// Create a [ArgsId] from an iterator of [Arg]. This function wil create a
    /// [Args](crate::Args), append it to the store and return  the created id.
    pub fn create_args(&self, args: impl IntoIterator<Item = Arg>, origin: ParamOrigin) -> ArgsId {
        let args_id = self.gs.args_store.create_from_iter(args);
        self.gs.args_store.set_origin(args_id, origin);
        args_id
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
        let resolution_id = self.gs.term_store.new_resolution_id();
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

    /// Create a set bound term, given a term and scope which is of kind
    /// [ScopeKind::SetBound].
    pub fn create_set_bound_term(&self, term: TermId, set_bound_scope: ScopeId) -> TermId {
        self.create_term(Term::SetBound(SetBound { term, scope: set_bound_scope }))
    }

    /// Create an argument with the given name and value.
    pub fn create_arg(&self, name: impl Into<Identifier>, value: TermId) -> Arg {
        Arg { name: Some(name.into()), value }
    }

    /// Create a nameless argument with the given value.
    pub fn create_nameless_arg(&self, value: TermId) -> Arg {
        Arg { name: None, value }
    }

    /// Create a type function application type, given type function value and
    /// arguments.
    ///
    /// This calls [Self::create_app_ty_fn], so its conditions apply here.
    pub fn create_app_ty_fn_term(&self, subject: TermId, args: ArgsId) -> TermId {
        let app_ty_fn = self.create_app_ty_fn(subject, args);
        self.create_term(Term::TyFnCall(app_ty_fn))
    }

    /// Create pattern arguments from the given pattern argument iterator.
    pub fn create_pat_args(
        &self,
        args: impl IntoIterator<Item = PatArg>,
        origin: ParamOrigin,
    ) -> PatArgsId {
        let args_id = self.gs.pat_args_store.create_from_iter(args);
        self.gs.pat_args_store.set_origin(args_id, origin);
        args_id
    }

    /// Create a pattern parameter
    pub fn create_pat_arg(&self, name: impl Into<Identifier>, pat: PatId) -> PatArg {
        PatArg { name: Some(name.into()), pat }
    }

    /// Create a constructor pattern.
    pub fn create_constructor_pat(&self, subject: TermId, params: PatArgsId) -> PatId {
        self.create_pat(Pat::Constructor(ConstructorPat { subject, args: params }))
    }

    /// Create a constructor pattern without parameters.
    pub fn create_constant_pat(&self, term: TermId) -> PatId {
        self.create_pat(Pat::Const(ConstPat { term }))
    }

    /// Create a list pattern with parameters.
    pub fn create_list_pat(&self, term: TermId, inner: PatArgsId) -> PatId {
        self.create_pat(Pat::Array(ArrayPat { list_element_ty: term, element_pats: inner }))
    }

    /// Create a binding pattern.
    pub fn create_binding_pat(
        &self,
        name: impl Into<Identifier>,
        mutability: Mutability,
        visibility: Visibility,
    ) -> PatId {
        self.create_pat(Pat::Binding(BindingPat { name: name.into(), mutability, visibility }))
    }

    /// Create a module pattern.
    pub fn create_mod_pat(&self, members: PatArgsId) -> PatId {
        self.create_pat(Pat::Mod(ModPat { members }))
    }

    /// Create a tuple pattern.
    pub fn create_tuple_pat(&self, members: PatArgsId) -> PatId {
        self.create_pat(Pat::Tuple(members))
    }

    /// Create a literal pattern.
    pub fn create_lit_pat(&self, lit_term: TermId) -> PatId {
        self.create_pat(Pat::Lit(lit_term))
    }

    /// Create a [Pat::Range]
    pub fn create_range_pat(&self, range: RangePat) -> PatId {
        self.create_pat(Pat::Range(range))
    }

    /// Create an OR-pattern.
    pub fn create_or_pat(&self, pats: impl IntoIterator<Item = PatId>) -> PatId {
        let pats = pats.into_iter().collect();
        self.create_pat(Pat::Or(pats))
    }

    /// Create a conditional pattern.
    pub fn create_if_pat(&self, pat: PatId, condition: TermId) -> PatId {
        self.create_pat(Pat::If(IfPat { pat, condition }))
    }

    /// Create a wildcard pattern `_`.
    pub fn create_wildcard_pat(&self) -> PatId {
        self.create_pat(Pat::Wild)
    }

    /// Create an access pattern.
    pub fn create_access_pat(&self, subject: PatId, property: impl Into<Identifier>) -> PatId {
        self.create_pat(Pat::Access(AccessPat { subject, property: property.into() }))
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
        self.gs.location_store.add_location_to_target(target, location);
    }
}
