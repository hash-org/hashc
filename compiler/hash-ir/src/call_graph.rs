//! This module contains the implementation for constructing a call graph
//! from the given program IR.
//!
//! This module also contains a Graphviz visualizer for the call graph that
//! can generate `.dot` files for visualization.

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

    /// Get all function instances that appear in the call graph.
    pub fn all_instances(&self) -> HashSet<InstanceId> {
        let mut instances = HashSet::new();
        instances.extend(self.calls.keys().copied());
        instances.extend(self.calls.values().flatten().copied());
        instances.extend(self.callers.keys().copied());
        instances.extend(self.callers.values().flatten().copied());
        instances
    }
}

/// Options for styling the call graph visualization.
#[derive(Debug, Clone)]
pub struct CallGraphOptions {
    /// The font to use for the graph when writing labels.
    pub font: String,

    /// The background colour of each node.
    pub node_background_colour: String,
}

impl Default for CallGraphOptions {
    fn default() -> Self {
        Self {
            font: "Courier, monospace".to_string(),
            node_background_colour: "lightblue".to_string(),
        }
    }
}

/// A writer for generating Graphviz `.dot` format output from a call graph.
pub struct CallGraphWriter {
    /// The call graph to visualize.
    call_graph: CallGraph,

    /// Options for styling the graph.
    options: CallGraphOptions,
}

impl CallGraphWriter {
    /// Create a new call graph writer.
    pub fn new(call_graph: CallGraph, options: CallGraphOptions) -> Self {
        Self { call_graph, options }
    }

    /// Create a new call graph writer with default options.
    pub fn with_default_options(call_graph: CallGraph) -> Self {
        Self::new(call_graph, CallGraphOptions::default())
    }

    /// Create a valid Graphviz node identifier from an InstanceId.
    /// Graphviz identifiers must be alphanumeric or underscore, so we sanitize
    /// the Debug output to only keep valid characters.
    fn node_id(instance_id: InstanceId) -> String {
        let debug_str = format!("{:?}", instance_id);

        let sanitized: String = debug_str
            .chars()
            .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
            .collect();
        format!("fn_{}", sanitized)
    }
}

impl fmt::Display for CallGraphWriter {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(w, "digraph call_graph {{")?;

        // Set graph, node, and edge font options
        writeln!(w, "  graph [fontname=\"{}\"];", self.options.font)?;
        writeln!(w, "  node [fontname=\"{}\"];", self.options.font)?;
        writeln!(w, "  edge [fontname=\"{}\"];", self.options.font)?;

        // Get all instances that appear in the call graph
        let all_instances = self.call_graph.all_instances();

        // Create nodes for each function instance
        for instance_id in &all_instances {
            let instance = instance_id.borrow();
            let name = instance.name();

            // Create a valid Graphviz node identifier
            let node_id = Self::node_id(*instance_id);

            // Format the function name and escape special characters for Graphviz
            let name_str = format!("{}", name);
            let escaped_name = name_str.replace('"', "\\\"").replace('\n', "\\n");

            // Create a node with the function name as the label
            writeln!(
                w,
                r#"  {} [shape="box", style="rounded,filled", fillcolor="{}", label="{}"];"#,
                node_id, self.options.node_background_colour, escaped_name
            )?;
        }

        // Create edges for function calls
        for (caller_id, callees) in &self.call_graph.calls {
            let caller_node = Self::node_id(*caller_id);

            for callee_id in callees {
                let callee_node = Self::node_id(*callee_id);
                writeln!(w, r#"  {} -> {} [label=""];"#, caller_node, callee_node)?;
            }
        }

        writeln!(w, "}}")
    }
}
