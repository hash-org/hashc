// @@Docs
use hash_source::{identifier::Identifier, location::SourceLocation};
use hash_types::new::{
    data::{DataDef, DataDefId},
    defs::DefParamsId,
    environment::env::AccessToEnv,
    fns::{FnDef, FnDefId},
    holes::{Hole, HoleKind},
    locations::LocationTarget,
    params::ParamsId,
    symbols::{Symbol, SymbolData},
    terms::{Term, TermId},
    tuples::TupleTy,
    tys::{Ty, TyId, UniverseTy},
    unions::UnionTy,
};
use hash_utils::store::{CloneStore, SequenceStore, Store};

/**
 * Common operations during typechecking.
 */
pub trait CommonOps: AccessToEnv {
    /**
     * Get a term by its ID.
     */
    fn get_term(&self, term_id: TermId) -> Term {
        self.stores().term().get(term_id)
    }

    /**
     * Get a type by its ID.
     */
    fn get_ty(&self, ty_id: TyId) -> Ty {
        self.stores().ty().get(ty_id)
    }

    /**
     * Get a data definition by its ID.
     */
    fn get_data_def(&self, data_def_id: DataDefId) -> DataDef {
        self.stores().data_def().get(data_def_id)
    }

    /**
     * Get a function definition by its ID.
     */
    fn get_fn_def(&self, fn_def_id: FnDefId) -> FnDef {
        self.stores().fn_def().get(fn_def_id)
    }

    fn get_location(&self, target: impl Into<LocationTarget>) -> Option<SourceLocation> {
        self.stores().location().get_location(target)
    }

    /**
     * Create a new type.
     */
    fn new_ty(&self, ty: Ty) -> TyId {
        self.stores().ty().create(ty)
    }
    /*
     * Create a new term.
     */
    fn new_term(&self, term: Term) -> TermId {
        self.stores().term().create(term)
    }

    /**
     * Create a new symbol with the given name.
     */
    fn new_symbol(&self, name: impl Into<Identifier>) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: Some(name.into()), symbol })
    }

    /**
     * Create a new internal symbol.
     */
    fn new_fresh_symbol(&self) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: None, symbol })
    }

    /**
     * Create a new term hole.
     */
    fn new_term_hole(&self) -> TermId {
        let hole_id = self.stores().hole().create_with(|id| Hole { id, kind: HoleKind::Term });
        self.stores().term().create_with(|_| Term::Hole(hole_id))
    }

    /**
     * Create a new type hole.
     */
    fn new_ty_hole(&self) -> TyId {
        let hole_id = self.stores().hole().create_with(|id| Hole { id, kind: HoleKind::Ty });
        self.stores().ty().create_with(|_| Ty::Hole(hole_id))
    }

    /**
     * Create a new empty parameter list.
     */
    fn new_empty_params(&self) -> ParamsId {
        self.stores().params().create_from_slice(&[])
    }

    /**
     * Create a new empty definition parameter list.
     */
    fn new_empty_def_params(&self) -> DefParamsId {
        self.stores().def_params().create_from_slice(&[])
    }

    /**
     * Create a type of types, i.e. small `Type`.
     */
    fn new_small_universe_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Universe(UniverseTy { size: 0 }))
    }

    /**
     * Create a large type of types, i.e. `Type(n)` for some natural number
     * `n`.
     */
    fn new_universe_ty(&self, n: usize) -> TyId {
        self.stores().ty().create(Ty::Universe(UniverseTy { size: n }))
    }

    /**
     * Create a new empty union type.
     */
    fn new_never_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Union(UnionTy { variants: self.new_empty_params() }))
    }

    /**
     * Create a new empty tuple type.
     */
    fn new_void_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Tuple(TupleTy {
            data: self.new_empty_params(),
            conditions: self.new_empty_params(),
        }))
    }
}

impl<T: AccessToEnv> CommonOps for T {}
