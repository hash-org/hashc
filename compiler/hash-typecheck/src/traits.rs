use crate::{
    error::{TypecheckError, TypecheckResult, Symbol},
    storage::{GlobalStorage, ModuleStorage},
    types::{TypeId, TypeList, TypeStorage},
    unify::{Substitution, Unifier, UnifyStrategy},
    writer::TypeWithStorage,
};
use hash_alloc::{collections::row::Row, row, Wall};
use hash_source::location::SourceLocation;
use hash_utils::counter;
use std::collections::{BTreeMap, HashMap};
use std::cell::Cell;

counter! {
    name: TraitId,
    counter_name: TRAIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug)]
pub struct TraitBounds<'c> {
    pub bounds: Row<'c, TraitBound<'c>>,
}

impl<'c> TraitBounds<'c> {
    pub fn empty() -> Self {
        Self { bounds: row![] }
    }
}

#[derive(Debug)]
pub struct TraitBound<'c> {
    pub trt: TraitId,
    pub params: TypeList<'c>,
}

impl TraitBound<'_> {}

counter! {
    name: TraitImplId,
    counter_name: TRAIT_IMPL_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug)]
pub struct TraitImpl<'c> {
    pub trait_id: TraitId,
    pub args: TypeList<'c>,
    pub bounds: TraitBounds<'c>,
}

#[derive(Debug)]
pub struct Trait<'c> {
    pub id: TraitId,
    pub args: TypeList<'c>,
    pub bounds: TraitBounds<'c>,
    pub fn_type: TypeId,
}

#[derive(Debug)]
pub struct ImplsForTrait<'c> {
    impls: BTreeMap<TraitImplId, &'c TraitImpl<'c>>,
}

impl<'c> ImplsForTrait<'c> {
    pub fn empty() -> Self {
        Self {
            impls: BTreeMap::new(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (TraitImplId, &'c TraitImpl<'c>)> + '_ {
        self.impls.iter().map(|(&a, &b)| (a, b))
    }
}

#[derive(Debug)]
pub struct TraitImplStorage<'c, 'w> {
    data: HashMap<TraitId, ImplsForTrait<'c>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> TraitImplStorage<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self {
            data: HashMap::new(),
            wall,
        }
    }

    pub fn add_impl(&mut self, trait_id: TraitId, trait_impl: TraitImpl<'c>) -> TraitImplId {
        let impls_for_trait = self
            .data
            .entry(trait_id)
            .or_insert_with(|| ImplsForTrait::empty());
        let id = TraitImplId::new();
        impls_for_trait
            .impls
            .insert(id, self.wall.alloc_value(trait_impl));
        id
    }

    pub fn get_impls(&mut self, trait_id: TraitId) -> &ImplsForTrait<'c> {
        self.data
            .entry(trait_id)
            .or_insert_with(|| ImplsForTrait::empty())
    }

    pub fn get_impls_mut(&mut self, trait_id: TraitId) -> &mut ImplsForTrait<'c> {
        self.data
            .entry(trait_id)
            .or_insert_with(|| ImplsForTrait::empty())
    }
}

#[derive(Debug)]
pub struct TraitStorage<'c, 'w> {
    data: HashMap<TraitId, Cell<&'c Trait<'c>>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> TraitStorage<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self {
            data: HashMap::new(),
            wall,
        }
    }

    pub fn get(&self, trait_id: TraitId) -> &'c Trait<'c> {
        self.data.get(&trait_id).unwrap().get()
    }

    pub fn create(
        &mut self,
        args: TypeList<'c>,
        bounds: TraitBounds<'c>,
        fn_type: TypeId,
    ) -> TraitId {
        let id = TraitId::new();
        self.data.insert(
            id,
            Cell::new(self.wall.alloc_value(Trait {
                id,
                args,
                bounds,
                fn_type,
            })),
        );
        id
    }
}

#[derive(Debug)]
pub struct CoreTraits {
    pub hash: TraitId,
    pub eq: TraitId,
}

impl<'c, 'w> CoreTraits {
    pub fn create(_types: &mut TypeStorage<'c, 'w>, _wall: &'w Wall<'c>) -> Self {
        CoreTraits {
            hash: TraitId::new(),
            eq: TraitId::new(),
        }
    }
}

pub struct TraitHelper<'c, 'w, 'm, 'ms, 'gs> {
    module_storage: &'ms mut ModuleStorage,
    global_storage: &'gs mut GlobalStorage<'c, 'w, 'm>,
}

impl<'c, 'w, 'm, 'ms, 'gs> TraitHelper<'c, 'w, 'm, 'ms, 'gs> {
    pub fn new(
        module_storage: &'ms mut ModuleStorage,
        global_storage: &'gs mut GlobalStorage<'c, 'w, 'm>,
    ) -> Self {
        Self {
            module_storage,
            global_storage,
        }
    }

    fn unifier(&mut self) -> Unifier<'c, 'w, 'm, '_, '_> {
        Unifier::new(self.module_storage, self.global_storage)
    }

    pub fn find_trait_impl(
        &mut self,
        trt: &Trait,
        trait_args: &[TypeId],
        fn_type: Option<TypeId>,
        trt_symbol: impl FnOnce() -> Symbol,
        args_location: Option<SourceLocation>,
    ) -> TypecheckResult<Substitution> {
        let mut trait_args = trait_args.to_owned();
        if trait_args.is_empty() {
            trait_args.extend(
                trt.args
                    .iter()
                    .map(|_| self.global_storage.types.create_unknown_type()),
            )
        }

        if trait_args.len() != trt.args.len() {
            return Err(TypecheckError::TypeArgumentLengthMismatch {
                location: args_location.or_else(|| trt_symbol().location()),
                expected: trt.args.len(),
                got: trait_args.len(),
            });
        }

        // Resolve any remaining fn args
        let mut unifier = self.unifier();
        if let Some(fn_type) = fn_type {
            let trait_vars_sub = unifier.instantiate_vars_list(&trt.args)?;
            let instantiated_fn = unifier.apply_sub(&trait_vars_sub, fn_type)?;
            unifier.unify(fn_type, instantiated_fn, UnifyStrategy::ModifyBoth)?;
        }

        // let mut last_err = None;

        // @@Performance: we have to collect due to lifetime issues, this is not ideal.
        let impls: Vec<_> = self
            .global_storage
            .trait_impls
            .get_impls(trt.id)
            .iter()
            .collect();
        for (_, trait_impl) in impls.iter() {
            match self.match_trait_impl(&trait_impl, &trait_args) {
                Ok(matched) => return Ok(matched),
                Err(e) => {
                    continue;
                    // last_err.replace(e);
                }
            }
        }
        // @@Todo: better errors
        Err(TypecheckError::NoMatchingTraitImplementations(trt_symbol()))
    }

    pub fn print_types(&self, types: &[TypeId]) {
        print!("[");
        for &a in types {
            print!("{}, ", TypeWithStorage::new(a, self.global_storage));
        }
        println!("]");
    }

    pub fn match_trait_impl(
        &mut self,
        trait_impl: &TraitImpl,
        trait_args: &[TypeId],
    ) -> TypecheckResult<Substitution> {
        let trt = self.global_storage.traits.get(trait_impl.trait_id);

        // @@Ambiguity: for now let's assume all type variables in here are new
        let impl_vars: Vec<_> = trait_impl
            .args
            .iter()
            .map(|&arg| {
                let arg_ty = self.global_storage.types.get(arg);
                let type_vars = arg_ty.fold_type_ids(vec![], |mut vars, ty_id| {
                    match self.global_storage.types.get(ty_id) {
                        crate::types::TypeValue::Var(_) => {
                            vars.push(ty_id);
                            vars
                        }
                        _ => vars,
                    }
                });
                type_vars
            })
            .flatten()
            .collect();

        let mut unifier = Unifier::new(self.module_storage, self.global_storage);
        let trait_args_sub = unifier.instantiate_vars_list(&trt.args)?;
        let trait_impl_args_sub =
            unifier.instantiate_vars_for_list(&trait_impl.args, &impl_vars)?;

        let trait_args_instantiated =
            unifier.apply_sub_to_list_make_vec(&trait_args_sub, &trt.args)?;
        let trait_impl_args_instantiated =
            unifier.apply_sub_to_list_make_vec(&trait_impl_args_sub, &trait_impl.args)?;
        // self.print_types(&trait_args_instantiated);
        // self.print_types(&trait_impl_args_instantiated);

        let merged_sub = trait_args_sub.merge(trait_impl_args_sub);
        Ok(merged_sub)
    }
}
