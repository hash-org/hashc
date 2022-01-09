use std::{
    cell::Cell,
    collections::{BTreeMap, HashMap},
    slice::SliceIndex,
};

use hash_alloc::{brick::Brick, collections::row::Row, row, Wall};
use hash_utils::counter;

use crate::{
    error::TypecheckResult,
    storage::{GlobalStorage, ModuleStorage},
    types::{FnType, TypeId, TypeList, Types},
    unify::{Substitution, Unifier, UnifyStrategy},
};

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

    // pub fn map(&self, f: impl FnMut(&TraitBound<'c>) -> TraitBound<'c>) -> Self {
    //     TraitBounds {
    //         data: Row::from_iter(self.data.iter().map(f), &self.wall),
    //         wall: self.wall.clone(),
    //     }
    // }
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

fn match_trait_impl(
    trait_impl: &TraitImpl,
    trait_args: &[TypeId],
    global_storage: &mut GlobalStorage,
    module_storage: &mut ModuleStorage,
) -> TypecheckResult<Substitution> {
    let trt = global_storage.traits.get(trait_impl.trait_id);

    // @@Ambiguity: for now let's assume all type variables in here are new
    let impl_vars: Vec<_> = trait_impl
        .args
        .iter()
        .map(|&arg| {
            let arg_ty = global_storage.types.get(arg);
            let type_vars = arg_ty.fold_type_ids(vec![], |mut vars, ty_id| {
                match global_storage.types.get(ty_id) {
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

    let mut unifier = Unifier::new(module_storage, global_storage);

    let trait_args_sub = unifier.instantiate_vars_list(&trt.args)?;
    let trait_impl_args_sub = unifier.instantiate_vars_for_list(&trait_impl.args, &impl_vars)?;

    let trait_args_instantiated = unifier.apply_sub_to_list_make_vec(&trait_args_sub, &trait_args);
    let trait_impl_args_instantiated =
        unifier.apply_sub_to_list_make_vec(&trait_impl_args_sub, &trait_impl.args);
    unifier.unify_pairs(
        trait_impl_args_instantiated
            .iter()
            .zip(trait_args_instantiated.iter()),
        UnifyStrategy::ModifyBoth,
    )?;

    Ok(trait_args_sub.merge(trait_impl_args_sub))
}

fn find_trait_impl(
    trt: &Trait,
    trait_args: &[TypeId],
    fn_type: TypeId,
    global_storage: &mut GlobalStorage,
    module_storage: &mut ModuleStorage,
) -> TypecheckResult<Substitution> {
    let impls = global_storage.trait_impls.for_trait(trt.id);

    // Resolve any remaining fn args
    let mut unifier = Unifier::new(module_storage, global_storage);
    let trait_vars_sub = unifier.instantiate_vars_list(&trt.args)?;
    let instantiated_fn = unifier.apply_sub(&trait_vars_sub, fn_type);
    unifier.unify(fn_type, instantiated_fn, UnifyStrategy::ModifyBoth)?;

    let mut last_err = None;
    for (_, trait_impl) in &impls.impls {
        match match_trait_impl(&trait_impl, trait_args, global_storage, module_storage) {
            Ok(matched) => return Ok(matched),
            Err(e) => {
                last_err.replace(e);
            }
        }
    }
    // @@Todo: better errors
    Err(last_err.unwrap())
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
    trt: TraitId,
    impls: BTreeMap<TraitImplId, TraitImpl<'c>>,
}

impl<'c> ImplsForTrait<'c> {
    pub fn resolve_call(&self, _fn_args: &[TypeId]) -> TraitImplId {
        todo!();
        // for (&impl_id, impl) in self.impls.iter() {
        // }
    }
}

#[derive(Debug)]
pub struct TraitImpls<'c, 'w> {
    data: HashMap<TraitId, Cell<&'c ImplsForTrait<'c>>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> TraitImpls<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self {
            data: HashMap::new(),
            wall,
        }
    }

    pub fn for_trait(&self, trait_id: TraitId) -> &'c ImplsForTrait<'c> {
        self.data.get(&trait_id).unwrap().get()
    }

    pub fn resolve_call(_trait_id: TraitId, _fn_args: &[TypeId]) -> TraitImplId {
        // Should substitute given TypeIds with their correct version from the trait impl!

        todo!()
    }
}

#[derive(Debug)]
pub struct Traits<'c, 'w> {
    data: HashMap<TraitId, Cell<&'c Trait<'c>>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> Traits<'c, 'w> {
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
    pub fn create(_types: &mut Types<'c, 'w>, _wall: &'w Wall<'c>) -> Self {
        CoreTraits {
            hash: TraitId::new(),
            eq: TraitId::new(),
        }
    }
}
