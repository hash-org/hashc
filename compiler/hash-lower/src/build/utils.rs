//! Contains utility functions that perform resolutions on
//! [PatId]s, [TermId]s, [ast::AstNodeId]s. This will read the
//! provided mappings between nodes to locations, patterns, and
//! types.

use hash_ir::{
    ir::{
        AggregateKind, AssertKind, BasicBlock, Const, Local, LocalDecl, Operand, Place, RValue,
        TerminatorKind,
    },
    ty::{IrTyId, Mutability},
    IrCtx,
};
use hash_source::{constant::CONSTANT_MAP, location::Span};
use hash_tir::{
    data::DataTy,
    environment::env::AccessToEnv,
    fns::FnDefId,
    mods::{ModMember, ModMemberValue},
    pats::PatId,
    symbols::Symbol,
    terms::TermId,
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::{log, store::SequenceStore};

use super::{Builder, LocalKey};

// @@Temporary: use this for terms that don't have a location
const DUMMY_SPAN: Span = Span::new(0, 0);

impl<'tcx> Builder<'tcx> {
    /// Get a reference to a [IrCtx].
    pub(crate) fn ctx(&self) -> &IrCtx {
        self.ctx.lcx
    }

    /// Get the [Span] of a given [PatId].
    pub(crate) fn span_of_pat(&self, id: PatId) -> Span {
        self.get_location(id).map(|loc| loc.span).unwrap_or_else(|| {
            log::debug!("expected pattern `{}` to have a location", self.env().with(id));
            DUMMY_SPAN
        })
    }

    /// Get the [Span] of a [FnDefId].
    pub(crate) fn span_of_def(&self, id: FnDefId) -> Span {
        self.get_location(id).map(|loc| loc.span).unwrap_or_else(|| {
            log::debug!(
                "expected function definition `{}` to have a location",
                self.env().with(id)
            );
            DUMMY_SPAN
        })
    }

    /// Get the [Span] of a given [TermId].
    pub(crate) fn span_of_term(&self, id: TermId) -> Span {
        self.get_location(id).map(|loc| loc.span).unwrap_or_else(|| {
            log::debug!("expected term `{:?}` to have a location", self.env().with(id));
            DUMMY_SPAN
        })
    }

    /// Create a [LocalKey] from a [Symbol].
    pub(crate) fn local_key_from_symbol(&self, symbol: Symbol) -> LocalKey {
        self.context().get_binding(symbol).kind.into()
    }

    /// Lookup a local by its [LocalKey].
    pub(crate) fn lookup_local(&self, key: &LocalKey) -> Option<Local> {
        self.declaration_map.get(key).copied()
    }

    /// Lookup a [Local] by a specified [Symbol].
    pub(crate) fn lookup_local_symbol(&self, symbol: Symbol) -> Option<Local> {
        let key = self.context().get_binding(symbol).kind.into();
        self.lookup_local(&key)
    }

    /// Lookup the definition of an item within the prelude defined
    /// LibC module definition. This is useful for looking up items
    /// and function definitions such as `malloc` and `free`.
    ///
    /// @@Future: ideally, we can remove this and just use `#lang_item`
    /// declaration to find the appropriate items.
    pub(crate) fn lookup_libc_fn(&mut self, name: &str) -> Option<IrTyId> {
        let libc_mod = match self.mod_utils().get_mod_member_by_ident(self.ctx.prelude, "libc") {
            Some(ModMember { value: ModMemberValue::Mod(libc_mod), .. }) => libc_mod,
            _ => return None,
        };

        // Now lookup the item in the libc module
        let Some(fn_def) = self.mod_utils().get_mod_fn_member_by_ident(libc_mod, name) else {
            return None;
        };

        Some(self.ty_id_from_tir_fn_def(fn_def))
    }

    /// Lookup the definition of an item within the prelude. This is used
    /// to lookup items such as `SizedPointer`.
    ///
    /// N.B. This assumes that the items have no type arguments.
    pub(crate) fn lookup_prelude_item(&mut self, name: &str) -> Option<IrTyId> {
        // Now lookup the item in the libc module
        let Some(member) = self.mod_utils().get_mod_member_by_ident(self.ctx.prelude, name) else {
            return None;
        };

        match member.value {
            ModMemberValue::Data(data_def) => {
                let args = self.stores().args().create_empty();
                let ty_id = self.ty_id_from_tir_data(DataTy { data_def, args });
                Some(ty_id)
            }
            ModMemberValue::Mod(_) => unreachable!("tried to lookup a module as an item"),
            ModMemberValue::Fn(fn_def) => Some(self.ty_id_from_tir_fn_def(fn_def)),
        }
    }

    /// Create a new [RValue] that represents a pointer with metadata, this uses
    /// the prelude defined `SizedPointer` type.
    pub(crate) fn create_ptr_with_metadata(
        &mut self,
        ty: IrTyId,
        ptr: Operand,
        metadata: usize,
    ) -> RValue {
        let id = self.ctx().map_ty_as_adt(ty, |_, id| id);

        let ptr_width = self.settings.target().ptr_size();
        let metadata =
            Operand::Const(Const::Int(CONSTANT_MAP.create_usize_int(metadata, ptr_width)).into());

        RValue::Aggregate(AggregateKind::Struct(id), vec![ptr, metadata])
    }

    /// Function to create a new [Place] that is used to ignore
    /// the results of expressions, i.e. blocks.
    pub(crate) fn make_tmp_unit(&mut self) -> Place {
        match &self.tmp_place {
            Some(tmp) => *tmp,
            None => {
                let local = LocalDecl::new_auxiliary(
                    self.ctx().tys().common_tys.unit,
                    Mutability::Immutable,
                );
                let local_id = self.declarations.push(local);

                let place = Place::from_local(local_id, self.ctx());
                self.tmp_place = Some(place);
                place
            }
        }
    }

    /// Create an assertion on a particular block
    pub(crate) fn assert(
        &mut self,
        block: BasicBlock,
        condition: Operand,
        expected: bool,
        kind: AssertKind,
        span: Span,
    ) -> BasicBlock {
        let success_block = self.control_flow_graph.start_new_block();

        self.control_flow_graph.terminate(
            block,
            span,
            TerminatorKind::Assert { condition, expected, kind, target: success_block },
        );

        success_block
    }
}
