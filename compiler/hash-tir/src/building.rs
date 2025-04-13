//! Building utilities for TIR nodes.

/// Building utilities for TIR nodes which do not have an origin, i.e. are
/// "generated".
///
/// Ideally, when this module is used, an according `##GeneratedOrigin` comment
/// should be added to the code.
pub mod generate {
    use hash_source::identifier::Identifier;
    use hash_storage::store::statics::SequenceStoreValue;
    use hash_target::primitives::IntTy;
    use hash_utils::itertools::Itertools;

    use crate::tir::{
        Arg, ArgsId, DataDef, DataDefCtors, DataDefId, Node, NodeOrigin, Param, ParamsId, Pat,
        PatId, PrimitiveCtorInfo, RefKind, SymbolId, Term, TermId, Ty, TyId, VariantData,
        VariantDataWithoutArgs,
    };

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
                .map(|(name, ty, default)| Node::generate(Param { name, ty, default }))
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
        discriminant_ty: IntTy,
        params: ParamsId,
        variants: impl IntoIterator<Item = VariantDataWithoutArgs>,
    ) -> DataDefId {
        let variants = Node::generate(variants.into_iter().map(Node::generate).collect_vec());
        DataDef::enum_def(name, discriminant_ty, params, move |_| variants, NodeOrigin::Generated)
    }

    /// Create an indexed enum definition.
    pub fn indexed_enum_def(
        name: SymbolId,
        discriminant_ty: IntTy,
        params: ParamsId,
        variants: impl IntoIterator<Item = VariantData>,
    ) -> DataDefId {
        DataDef::indexed_enum_def(
            name,
            discriminant_ty,
            params,
            move |_| Node::generate(variants.into_iter().map(Node::generate).collect_vec()),
            NodeOrigin::Generated,
        )
    }

    /// Create a primitive data definition.
    pub fn primitive(name: SymbolId, info: PrimitiveCtorInfo) -> DataDefId {
        Node::create_gen(DataDef {
            name,
            params: Node::create_gen(Node::<Param>::empty_seq()),
            ctors: DataDefCtors::Primitive(info),
            discriminant_ty: None,
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
        Node::create_gen(DataDef {
            name,
            params,
            ctors: DataDefCtors::Primitive(info),
            discriminant_ty: None,
        })
    }

    /// Create a universe type.
    #[allow(non_snake_case)]
    pub fn Type() -> TyId {
        Ty::universe(NodeOrigin::Generated)
    }

    /// Create a data type with no arguments.
    pub fn data_ty(data: DataDefId) -> TyId {
        Ty::data_ty(data, NodeOrigin::Generated)
    }

    /// Create an empty tuple term `()`.
    pub fn unit_term() -> TermId {
        Term::unit(NodeOrigin::Generated)
    }

    /// Create an empty tuple type `()`.
    pub fn unit_ty() -> TyId {
        Ty::unit_ty(NodeOrigin::Generated)
    }

    /// Create a reference type with the given data.
    pub fn ref_ty(ty: TyId, kind: RefKind, mutable: bool) -> TyId {
        Ty::ref_ty(ty, kind, mutable, NodeOrigin::Generated)
    }

    /// Create a term by the given data.
    pub fn term(inner: impl Into<Term>) -> TermId {
        Term::from(inner, NodeOrigin::Generated)
    }

    /// Create a type by the given data.
    pub fn ty(inner: impl Into<Ty>) -> TyId {
        Ty::from(inner, NodeOrigin::Generated)
    }

    /// Create a pattern by the given data.
    pub fn pat(inner: impl Into<Pat>) -> PatId {
        Node::create_at(inner.into(), NodeOrigin::Generated)
    }
}
