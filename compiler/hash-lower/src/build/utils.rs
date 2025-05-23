//! Contains utility functions that perform resolutions on
//! [PatId]s, [TermId]s, [ast::AstNodeId]s. This will read the
//! provided mappings between nodes to locations, patterns, and
//! types.

use hash_ast::ast::AstNodeId;
use hash_const_eval::Const;
use hash_ir::{
    IrCtx,
    ir::{
        AggregateKind, AssertKind, BasicBlock, Local, LocalDecl, Operand, Place, RValue,
        TerminatorKind,
    },
    lang_items::LangItem,
    ty::{COMMON_REPR_TYS, Mutability, ReprTyId},
};
use hash_storage::store::statics::{SequenceStoreValue, StoreId};
use hash_tir::tir::{
    Arg, DataTy, FnDefId, HasAstNodeId, ModMember, ModMemberValue, Node, NodeId, PatId, SymbolId,
    TermId,
};

use super::BodyBuilder;

impl BodyBuilder<'_> {
    /// Get a reference to a [IrCtx].
    pub(crate) fn ctx(&self) -> &IrCtx {
        self.ctx.lcx
    }

    /// Get the interned span of a given [PatId].
    pub(crate) fn span_of_pat(&self, id: PatId) -> AstNodeId {
        id.node_id_or_default()
    }

    /// Get the interned span of a [FnDefId].
    pub(crate) fn span_of_def(&self, id: FnDefId) -> AstNodeId {
        id.node_id_or_default()
    }

    /// Get the interned span of a given [TermId].
    pub(crate) fn span_of_term(&self, id: TermId) -> AstNodeId {
        id.node_id_or_default()
    }

    /// Lookup a [Local] by a specified [Symbol].
    pub(crate) fn lookup_local(&self, symbol: SymbolId) -> Option<Local> {
        self.declaration_map.get(&symbol).copied()
    }

    /// Lookup the definition of an item within the prelude defined
    /// LibC module definition. This is useful for looking up items
    /// and function definitions such as `malloc` and `free`.
    ///
    /// @@Future: ideally, we can remove this and just use `#lang_item`
    /// declaration to find the appropriate items.
    pub(crate) fn lookup_libc_fn(&mut self, name: &str) -> Option<ReprTyId> {
        let libc_mod = match self.ctx.prelude.borrow().get_mod_member_by_ident("libc").map(|x| *x) {
            Some(ModMember { value: ModMemberValue::Mod(libc_mod), .. }) => libc_mod,
            _ => return None,
        };

        // Now lookup the item in the libc module
        let fn_def = libc_mod.borrow().get_mod_fn_member_by_ident(name)?;
        Some(self.ty_id_from_tir_fn_def(fn_def))
    }

    /// Lookup the definition of an item within the prelude. This is used
    /// to lookup items such as `SizedPointer`.
    ///
    /// N.B. This assumes that the items have no type arguments.
    pub(crate) fn lookup_prelude_item(&mut self, name: &str) -> Option<ReprTyId> {
        // Now lookup the item in the libc module
        let member = self.ctx.prelude.borrow().get_mod_member_by_ident(name)?;

        match member.value {
            ModMemberValue::Data(data_def) => {
                let args = Node::create_at(Node::<Arg>::empty_seq(), data_def.origin());
                let ty_id = self.ty_id_from_tir_data(DataTy { data_def, args });
                Some(ty_id)
            }
            ModMemberValue::Mod(_) => unreachable!("tried to lookup a module as an item"),
            ModMemberValue::Fn(fn_def) => Some(self.ty_id_from_tir_fn_def(fn_def)),
            ModMemberValue::Intrinsic(intrinsic) => {
                Some(self.ty_id_from_tir_intrinsic(intrinsic, member.node_id_or_default()))
            }
        }
    }

    pub(crate) fn get_lang_item(&self, name: LangItem) -> ReprTyId {
        self.ctx.lcx.lang_items().get_ty(name).expect("lang item not found or not defined")
    }

    /// Create a new [RValue] that represents a pointer with metadata, this uses
    /// the prelude defined `SizedPointer` type.
    pub(crate) fn create_ptr_with_metadata(
        &mut self,
        ty: ReprTyId,
        ptr: Operand,
        metadata: usize,
    ) -> RValue {
        let adt = ty.borrow().as_adt();
        let metadata = Operand::Const(Const::usize(metadata as u64, &self.ctx));
        RValue::Aggregate(AggregateKind::Struct(adt), vec![ptr, metadata])
    }

    /// Function to create a new [Place] that is used to ignore
    /// the results of expressions, i.e. blocks.
    pub(crate) fn make_tmp_unit(&mut self) -> Place {
        match &self.tmp_place {
            Some(tmp) => *tmp,
            None => {
                let local = LocalDecl::new_auxiliary(COMMON_REPR_TYS.unit, Mutability::Immutable);
                let local_id = self.locals.push(local);

                let place = Place::from_local(local_id);
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
        origin: AstNodeId,
    ) -> BasicBlock {
        let success_block = self.control_flow_graph.start_new_block();

        self.control_flow_graph.terminate(
            block,
            origin,
            TerminatorKind::Assert {
                condition,
                expected,
                kind: Box::new(kind),
                target: success_block,
            },
        );

        success_block
    }
}
