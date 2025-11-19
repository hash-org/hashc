//! This module contains the implementation for constructing a call graph
//! from the given program IR.

use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use hash_repr::ty::InstanceId;
use hash_storage::store::statics::StoreId;

use crate::ir::{Body, TerminatorKind};

#[derive(Debug)]
pub struct CallGraph {
    /// The calls that are made from one instance to another.
    calls: HashMap<InstanceId, HashSet<InstanceId>>,

    /// The callers of an instance.
    callers: HashMap<InstanceId, HashSet<InstanceId>>,
}

impl CallGraph {
    pub fn build(bodies: &[Body]) -> Self {
        let mut calls = HashMap::new();
        let mut callers = HashMap::new();

        for body in bodies.iter() {
            let body_ty = body.metadata().ty();
            let id = body_ty.borrow().as_instance();

            // Assuming that the bodies have been optimised and no longer contain dead
            // blocks.
            //
            // We can just check for any terminators that are of the `Call` kind, and add
            // the target body to the call graph.
            for terminator in body.terminators() {
                if let TerminatorKind::Call { op, .. } = &terminator.kind {
                    let ty = op.ty(&body.aux());

                    if !ty.is_fn_def() {
                        continue;
                    }

                    let instance = ty.borrow().as_instance();
                    calls.entry(id).or_insert_with(HashSet::new).insert(instance);
                    callers.entry(instance).or_insert_with(HashSet::new).insert(id);
                }
            }
        }

        Self { calls, callers }
    }
