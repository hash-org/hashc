//! Contains useful utilities for traversing a CFG of
//! a particular body in pre-order, post-order, etc.

use fixedbitset::FixedBitSet;

use crate::ir::{BasicBlock, BasicBlockData, Body, Successors, START_BLOCK};

/// A [PreOrder] struct contains the relevant information
/// about a pre-order traversal of a [Body]. This implements
/// the [Iterator] trait and will yield the next basic block
/// in the pre-order traversal.
pub struct PreOrder<'ir> {
    /// The body that we are traversing.
    body: &'ir Body,

    /// The visited blocks of the body.
    visited: FixedBitSet,

    /// The current work_list of the nodes that
    /// need to visited
    work_list: Vec<BasicBlock>,

    /// If the traversal orders starts at the beginning
    /// [START_BLOCK] of the body.
    root_is_start_block: bool,
}

impl<'ir> PreOrder<'ir> {
    /// Creates a new instance of [PreOrder] that will
    /// traverse the body in pre-order.
    pub fn new(body: &'ir Body, root: BasicBlock) -> Self {
        Self {
            body,
            visited: FixedBitSet::with_capacity(body.blocks().len()),
            work_list: vec![root],
            root_is_start_block: root == START_BLOCK,
        }
    }

    /// Create a new instance of [PreOrder] that will
    /// traverse the body in pre-order starting at the
    /// beginning [START_BLOCK] of the body.
    pub fn new_from_start(body: &'ir Body) -> Self {
        Self::new(body, START_BLOCK)
    }
}

impl<'ir> Iterator for PreOrder<'ir> {
    type Item = (BasicBlock, &'ir BasicBlockData);

    /// Implements the [Iterator] trait for [PreOrder]. Essentially
    /// traverses the body [BasicBlock]s in pre-order.
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.work_list.pop() {
            // Check if we have already visited this block, if not
            // then add it to the `visited` list and return this as
            // the next element of the graph traversal.
            if self.visited.contains(next.index()) {
                continue;
            } else {
                self.visited.insert(next.index());
            }

            let data = &self.body.blocks()[next];

            // Add all of the successors to the worklist so we
            // can visit them on the next iteration.
            if let Some(ref term) = data.terminator {
                self.work_list.extend(term.successors());
            }

            return Some((next, data));
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // All the blocks, minus the number of blocks we've visited.
        let upper = self.body.basic_blocks.len() - self.visited.ones().count();

        // If we start at the root, then we will visit all of the remaining
        // blocks in the body, otherwise we only visit the remaining blocks
        // in the `work_list`.
        let lower = if self.root_is_start_block { upper } else { self.work_list.len() };

        (lower, Some(upper))
    }
}

/// Compute reachable blocks from the [START_BLOCK] of the body.
pub fn reachable_block_indices(body: &Body) -> FixedBitSet {
    let mut pre_order_traversal = PreOrder::new_from_start(body);

    // now we perform the iteration, and only keep the visited blocks.
    (&mut pre_order_traversal).for_each(drop);

    pre_order_traversal.visited
}

/// A [PostOrder] struct performs a post-order traversal of a
/// [Body] and implements the [Iterator] trait. This will yield
/// the next basic block in the post-order traversal.
///
/// # Example
/// ```ignore, notrust
///              A
///              |
///              B
///            /   \
///            F     D
///           / \     \
///          G   H     E
///             / \
///            I   C
/// ```
///
/// The post-order traversal of the above graph would be:
/// ```ignore
/// G, I, C,  H, F, E, D, B, A
/// ```
pub struct PostOrder<'ir> {
    /// The body that we are traversing.
    body: &'ir Body,

    /// The visited blocks of the body.
    visited: FixedBitSet,

    /// The current visiting stack of the traversal.
    stack: Vec<(BasicBlock, Successors<'ir>)>,

    /// If the traversal orders starts at the beginning
    /// [START_BLOCK] of the body.
    root_is_start_block: bool,
}

impl<'ir> PostOrder<'ir> {
    /// Creates a new instance of [PostOrder] that will
    /// traverse the body in post-order.
    pub fn new(body: &'ir Body, root: BasicBlock) -> Self {
        let mut ordering = Self {
            body,
            visited: FixedBitSet::with_capacity(body.blocks().len()),
            stack: vec![],
            root_is_start_block: root == START_BLOCK,
        };

        // We need to initialise the parameters by "visiting" the root
        // block and adding the successors of the block to the working
        // stack.
        let data = &body.blocks()[root];

        if let Some(ref terminator) = data.terminator {
            ordering.visited.insert(root.index());
            ordering.stack.push((root, terminator.successors()));
            ordering.traverse_successor();
        }

        ordering
    }

    /// Create a new instance of [PostOrder] that will
    /// traverse the body in post-order starting at the
    /// beginning [START_BLOCK] of the body.
    pub fn new_from_start(body: &'ir Body) -> Self {
        Self::new(body, START_BLOCK)
    }

    /// Traverses the successor from the current state.
    fn traverse_successor(&mut self) {
        while let Some(&mut (_, ref mut successors)) = self.stack.last_mut() {
            if let Some(successor) = successors.next() {
                // check if we have already visited this block...
                if self.visited.contains(successor.index()) {
                    continue;
                }

                // if not, then we "visit" this current `successor` and it's
                // successors to the working stack.
                let data = &self.body.blocks()[successor];

                if let Some(ref terminator) = data.terminator {
                    self.visited.insert(successor.index());
                    self.stack.push((successor, terminator.successors()));
                }
            } else {
                break;
            }
        }
    }
}

impl<'ir> Iterator for PostOrder<'ir> {
    type Item = (BasicBlock, &'ir BasicBlockData);

    /// Implements the [Iterator] trait for [PostOrder]. Essentially
    /// traverses the body [BasicBlock]s in post-order.
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.stack.pop();

        if next.is_some() {
            self.traverse_successor();
        }

        next.map(|(block, _)| (block, &self.body.blocks()[block]))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // All the blocks, minus the number of blocks we've visited.
        let upper = self.body.basic_blocks.len() - self.visited.ones().count();

        // If we start at the root, then we will visit all of the remaining
        // blocks in the body, otherwise we only visit the remaining blocks
        // in the `work_list`.
        let lower = if self.root_is_start_block { upper } else { self.stack.len() };

        (lower, Some(upper))
    }
}

/// [ReversePostOrder] is a struct that implements the [Iterator] trait
/// and will iterate a control flow graph in reverse post-order.
///
/// Reverse post-order is the reverse of a post-order traversal. It is different
/// from a pre-order traversal in that it will visit all of the successors of a
/// node before visiting the node itself. Reverse post-order traversal
/// represents a natural linearisation of a control flow graph. To illustrate
/// the order, consider the following graph:
/// ```notrust, ignore
///    A
///   / \
///  B   C
///   \ / \
///    D   E
///        |
///        F
/// ```
///
/// A reverse post-order traversal of this graph would be either `A, B, C, D, E,
/// F` or `A, C, B, E, D, F`. The order of the successors of a node is not
/// important. For a graph that contains no loops (i.e. a DAG), the reverse
/// post-order traversal is equivalent to a topological sort of the graph.
///
/// Construction of a [ReversePostOrder] traversal is done by performing a
/// post-order traversal, pushing all the visited nodes onto a stack, and
/// popping them off to get the reverse post-order traversal.
pub struct ReversePostOrder<'ir> {
    /// The body that we are traversing.
    body: &'ir Body,

    /// The order of the blocks to traverse in reverse post-order.
    blocks: Vec<BasicBlock>,

    /// The current index into the `blocks` vector. This is used
    /// to compute the remaining number of blocks left to traverse.
    index: usize,
}

impl<'ir> ReversePostOrder<'ir> {
    /// Creates a new instance of [ReversePostOrder] that will
    /// traverse the body in reverse post-order.
    pub fn new(body: &'ir Body, root: BasicBlock) -> Self {
        let blocks: Vec<_> = PostOrder::new(body, root).map(|(bb, _)| bb).collect();
        let index = blocks.len();

        Self { body, blocks, index }
    }

    /// Create a new instance of [ReversePostOrder] that will
    /// traverse the body in reverse post-order starting at the
    /// beginning [START_BLOCK] of the body.
    pub fn new_from_start(body: &'ir Body) -> Self {
        Self::new(body, START_BLOCK)
    }
}

impl<'ir> Iterator for ReversePostOrder<'ir> {
    type Item = (BasicBlock, &'ir BasicBlockData);

    /// Implements the [Iterator] trait for [ReversePostOrder]. Essentially
    /// traverses the body [BasicBlock]s in reverse post-order.
    fn next(&mut self) -> Option<Self::Item> {
        if self.index == 0 {
            return None;
        }

        self.index -= 1;

        let block = self.blocks[self.index];
        Some((block, &self.body.blocks()[block]))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.index, Some(self.index))
    }
}

impl<'ir> ExactSizeIterator for ReversePostOrder<'ir> {}
