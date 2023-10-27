//! Implementation of attribute checking for specific attributes.
//!
//!  
use hash_ast_utils::attr::{AttrNode, AttrTarget};
use hash_source::SourceId;
use hash_target::data_layout::TargetDataLayout;

use crate::{
    attr::{Attr, Attrs, ReprAttr},
    builtin::attrs,
    diagnostics::{AttrError, AttrResult, AttrWarning},
};

/// Used to check attributes, and emit diagnostics if the attributes
/// are not correct or have been used incorrectly.
pub struct AttrChecker<'env> {
    /// The current source that the checker is
    /// checking attributes for.
    source: SourceId,

    /// Any warnings collected by the checker.
    warnings: Vec<AttrWarning>,

    /// The current compilation target.
    _data_layout: &'env TargetDataLayout,
}

impl<'env> AttrChecker<'env> {
    /// Create a new [AttrChecker].
    pub fn new(source: SourceId, target: &'env TargetDataLayout) -> Self {
        Self { source, warnings: Vec::new(), _data_layout: target }
    }

    /// Take any warnings that the checker has collected.
    pub fn take_warnings(&mut self) -> Vec<AttrWarning> {
        std::mem::take(&mut self.warnings)
    }

    /// Check that adding an attribute with the current context is valid.
    pub fn check_attr(&mut self, attrs: &Attrs, attr: &Attr, node: AttrNode<'_>) -> AttrResult {
        match attr.id {
            attrs::INTRINSICS => self.check_intrinsics_attr(attrs, attr, node)?,
            attrs::REPR => self.check_repr_attr(attrs, attr, node)?,
            attrs::LAYOUT_OF => self.check_layout_of_attr(attrs, attr, node)?,
            _ => {
                // By default, check if we are trying to apply the attribute twice.
                self.check_duplicate_attr(attrs, attr)?;
            }
        }

        Ok(())
    }

    /// A function to emit a warning if the an attribute that is being
    /// applied has already been registered. This is only a warning because
    /// attributes that introduce a "conflict" produce an error.
    pub fn check_duplicate_attr(&mut self, attrs: &Attrs, attr: &Attr) -> AttrResult {
        if let Some(prev) = attrs.get_attr(attr.id) {
            self.warnings
                .push(AttrWarning::Unused { origin: attr.origin, preceeding: prev.origin });
        }

        Ok(())
    }

    /// Check that a `#intrinsics` attribute application is valid.
    ///
    /// # Errors
    ///
    /// - If the attribute is not being applied to the prelude module.
    ///
    /// - If the attribute is not applied onto a function or a mod-def.
    fn check_intrinsics_attr(
        &mut self,
        attrs: &Attrs,
        attr: &Attr,
        node: AttrNode<'_>,
    ) -> AttrResult {
        // Check if we are in the prelude module, and if not we emit an error.
        if !self.source.is_prelude() {
            return Err(AttrError::NonPreludeIntrinsics { origin: node.id() });
        } else {
            self.check_duplicate_attr(attrs, attr)?;
        }

        Ok(())
    }

    /// Check that a `#[repr(...)]` attribute application is valid.
    ///
    /// # Errors
    /// - If the repr hint is not a valid repr hint.
    ///
    /// - If the repr hint is given as `u8`, `u16`, `u32`, `u64`, or `u128` and
    ///   attempted to be applied to a struct definition.
    ///
    /// - If a previous repr hint has been applied to the item, and the new repr
    ///   are incompatible.
    fn check_repr_attr(&mut self, attrs: &Attrs, attr: &Attr, node: AttrNode<'_>) -> AttrResult {
        let arg = attr.get_arg(0).unwrap();

        // Check that the specified `#repr` attribute is valid.
        let repr = ReprAttr::parse(attr)?;

        if let ReprAttr::Int(_) = repr
            && let AttrNode::StructDef(_) = node
        {
            return Err(AttrError::InvalidReprForItem {
                origin: attr.origin,
                item: AttrTarget::StructDef,
                arg: *arg,
            });
        }

        // Check if we have a conflicting representation argument with a previously
        // applied representation argument.
        if let Some(prev) = attrs.get_attr(attr.id) {
            // @@Improve: we're re-parsing the repr attribute here, which is
            // wasteful!.
            let prev_repr = ReprAttr::parse(prev).unwrap();
            if prev_repr != repr {
                return Err(AttrError::IncompatibleReprArgs {
                    origin: prev.origin,
                    second: attr.origin,
                });
            } else {
                self.check_duplicate_attr(attrs, attr)?;
            }
        }

        Ok(())
    }

    /// Check that the `#layout_of` attribute application is valid.
    ///
    /// # Errors
    /// - If the attribute is applied to a struct or enum definition with
    ///   generics.
    fn check_layout_of_attr(
        &mut self,
        attrs: &Attrs,
        attr: &Attr,
        node: AttrNode<'_>,
    ) -> AttrResult {
        self.check_duplicate_attr(attrs, attr)?;

        let (maybe_params, item) = match &node {
            AttrNode::StructDef(def) => (def.ty_params.as_ref(), AttrTarget::StructDef),
            AttrNode::EnumDef(def) => (def.ty_params.as_ref(), AttrTarget::EnumDef),
            _ => unreachable!("`#layout_of` attribute applied to non-struct/enum item"),
        };

        if let Some(params) = maybe_params
            && !params.body().params.is_empty()
        {
            Err(AttrError::LayoutOfGenericItem { origin: node.id(), generics: params.id(), item })
        } else {
            Ok(())
        }
    }
}
