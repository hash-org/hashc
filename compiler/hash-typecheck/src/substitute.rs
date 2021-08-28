use std::{
    borrow::Borrow,
    collections::HashMap,
    iter::{self, FromIterator},
};

use hash_ast::ast::TypeId;
use smallvec::SmallVec;

use crate::types::{
    GenTypeVarId, TypeValue, TypecheckCtx, TypecheckError, TypecheckResult, Types,
};

#[derive(Debug)]
pub struct Substitutions {
    data: HashMap<GenTypeVarId, TypeId>,
}

impl Substitutions {
    pub fn empty() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    pub fn single(from: GenTypeVarId, to: TypeId) -> Self {
        Self {
            data: HashMap::from_iter(iter::once((from, to))),
        }
    }

    pub fn try_merge(
        types: &Types,
        mut subs: impl Iterator<Item = TypecheckResult<Substitutions>>,
    ) -> TypecheckResult<Substitutions> {
        match subs.next() {
            Some(accumulating_sub) => {
                let mut accumulating_sub = accumulating_sub?;
                for sub in subs {
                    accumulating_sub.update(types, &sub?);
                }

                Ok(accumulating_sub)
            }
            // No elements means empty substitution
            None => Ok(Substitutions::empty()),
        }
    }

    pub fn merge_many(types: &Types, mut subs: impl Iterator<Item = Substitutions>) -> Substitutions {
        match subs.next() {
            Some(mut accumulating_sub) => {
                for sub in subs {
                    accumulating_sub.update(types, &sub);
                }

                accumulating_sub
            }
            // No elements means empty substitution
            None => Substitutions::empty(),
        }
    }

    pub fn update(&mut self, types: &Types, other: &Substitutions) {
        // Update current values with substitutions.
        for v in self.data.values_mut() {
            if let TypeValue::GenVar(gen_var) = *types.get(*v) {
                if let Some(resolved_type_id) = other.data.get(&gen_var.id) {
                    *v = *resolved_type_id;
                }
            }
        }

        // Update with other values
        for (k, v) in &other.data {
            // If it fails, do nothing (key already present).
            let _ = self.data.try_insert(*k, *v);
        }
    }

    pub fn merge(mut self, types: &Types, other: &Substitutions) -> Self {
        self.update(types, other);
        self
    }
}
