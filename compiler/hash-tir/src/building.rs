/// Building utilities for TIR nodes.

pub mod gen {
    use hash_source::identifier::Identifier;
    use hash_storage::store::statics::SequenceStoreValue;
    use hash_utils::itertools::Itertools;

    use crate::{
        args::{Arg, ArgsId},
        data::{DataDef, DataDefCtors, DataDefId, DataTy, PrimitiveCtorInfo},
        node::{Node, NodeOrigin},
        params::{Param, ParamsId},
        pats::{Pat, PatId},
        primitives::primitives,
        symbols::SymbolId,
        terms::{Term, TermId},
        tys::{Ty, TyId},
    };

    /// Building utilities for TIR nodes which do not have an origin, i.e. are
    /// "generated".

    /// Create a symbol with the given name.
    pub fn sym(name: impl Into<Identifier>) -> SymbolId {
        SymbolId::from_name(name, NodeOrigin::Generated)
    }

    /// Create a parameter list with the given parameters.
    pub fn params_pos(tys: impl IntoIterator<Item = TyId>) -> ParamsId {
        Param::seq_positional(tys, NodeOrigin::Generated)
    }

    /// Create a parameter list with the given parameters.
    pub fn params(data: impl IntoIterator<Item = (SymbolId, TyId, Option<TermId>)>) -> ParamsId {
        Node::create_gen(Node::<Param>::seq(
            data.into_iter()
                .map(|(name, ty, default)| Node::gen(Param { name, ty, default }))
                .collect_vec(),
        ))
    }

    /// Create a parameter list with the given parameters.
    pub fn args(data: impl IntoIterator<Item = TermId>) -> ArgsId {
        Arg::seq_positional(data, NodeOrigin::Generated)
    }

    /// Create an empty data definition.
    pub fn empty_data_def(name: SymbolId, params: ParamsId) -> DataDefId {
        DataDef::empty(name, params, NodeOrigin::Generated, NodeOrigin::Generated)
    }

    /// Create an enum definition.
    pub fn enum_def(
        name: SymbolId,
        params: ParamsId,
        variants: impl IntoIterator<Item = (SymbolId, ParamsId)>,
    ) -> DataDefId {
        let variants = Node::gen(
            variants.into_iter().map(|(name, params)| Node::gen((name, params))).collect_vec(),
        );
        DataDef::enum_def(name, params, move |_| variants, NodeOrigin::Generated)
    }

    /// Create an indexed enum definition.
    pub fn indexed_enum_def(
        name: SymbolId,
        params: ParamsId,
        variants: impl IntoIterator<Item = (SymbolId, ParamsId, Option<ArgsId>)>,
    ) -> DataDefId {
        DataDef::indexed_enum_def(
            name,
            params,
            move |_| {
                Node::gen(
                    variants
                        .into_iter()
                        .map(|(name, params, args)| Node::gen((name, params, args)))
                        .collect_vec(),
                )
            },
            NodeOrigin::Generated,
        )
    }

    /// Create a primitive data definition.
    pub fn primitive(name: SymbolId, info: PrimitiveCtorInfo) -> DataDefId {
        Node::create_gen(DataDef {
            name,
            params: Node::create_gen(Node::<Param>::empty_seq()),
            ctors: DataDefCtors::Primitive(info),
        })
    }

    /// Create a primitive data definition with parameters.
    ///
    /// These may be referenced in `info`.
    pub fn primitive_with_params(
        name: SymbolId,
        params: ParamsId,
        info: PrimitiveCtorInfo,
    ) -> DataDefId {
        Node::create_gen(DataDef { name, params, ctors: DataDefCtors::Primitive(info) })
    }

    pub fn universe_ty() -> TyId {
        Ty::flexible_universe(NodeOrigin::Generated)
    }

    pub fn data_ty(data: DataDefId) -> TyId {
        Ty::data(data, NodeOrigin::Generated)
    }

    pub fn void_term() -> TermId {
        Term::void(NodeOrigin::Generated)
    }

    pub fn void_ty() -> TyId {
        Ty::void(NodeOrigin::Generated)
    }

    pub fn never_ty() -> TyId {
        Ty::from(
            DataTy {
                args: Node::create_at(Node::<Arg>::empty_seq(), NodeOrigin::Generated),
                data_def: primitives().never(),
            },
            NodeOrigin::Generated,
        )
    }

    pub fn term(inner: impl Into<Term>) -> TermId {
        Term::from(inner, NodeOrigin::Generated)
    }

    pub fn ty(inner: impl Into<Ty>) -> TyId {
        Ty::from(inner, NodeOrigin::Generated)
    }

    pub fn pat(inner: impl Into<Pat>) -> PatId {
        Node::create_at(inner.into(), NodeOrigin::Generated)
    }
}
