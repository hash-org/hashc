//! Contains logic for displaying a computed [Layout] in a pretty format
//! that can be queried by users.

use std::fmt;

use hash_utils::store::Store;

use crate::{LayoutCtx, LayoutId, Variants};

/// The [LayoutWriter] is a wrapper around [LayoutCtx] that allows
/// for the pretty printing of a [Layout] in a human readable format.
pub struct LayoutWriter<'l> {
    /// The layout to be written.
    pub layout: LayoutId,

    /// The current context for printing the layout.
    pub ctx: LayoutCtx<'l>,
}

impl<'l> LayoutWriter<'l> {
    pub fn new(layout: LayoutId, ctx: LayoutCtx<'l>) -> Self {
        Self { layout, ctx }
    }
}

impl fmt::Display for LayoutWriter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ctx.map_fast(self.layout, |layout| {
            // Firstly, we print the initial "shape" of the
            // layout in order to account for the fact that
            // the layout may contain "multiple" variants that
            // are present in the layout, which we will also have to print.
            match layout.variants {
                Variants::Single { index: _ } => {
                    // this is the simple case, we merely need to print the
                    write!(f, "shape")
                }
                Variants::Multiple { tag: _, field: _, variants: _ } => {
                    write!(f, "tag then shape")
                }
            }
        })
    }
}
