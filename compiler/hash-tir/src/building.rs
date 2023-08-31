/// Building utilities for TIR nodes.

pub mod gen {
    use hash_source::identifier::Identifier;
    use hash_storage::store::statics::SequenceStoreValue;
    use hash_utils::itertools::Itertools;

    use crate::{
        node::Node,
        params::{Param, ParamsId},
        symbols::SymbolId,
        terms::TermId,
        tys::TyId,
    };

    /// Building utilities for TIR nodes which do not have an origin, i.e. are
    /// "generated".

    /// Create a symbol with the given name.
    pub fn sym(name: impl Into<Identifier>) -> SymbolId {
        SymbolId::from_name(name)
    }

    /// Create a parameter list with the given parameters.
    pub fn params(data: impl IntoIterator<Item = (SymbolId, TyId, Option<TermId>)>) -> ParamsId {
        Node::create_gen(Node::<Param>::seq_data(
            data.into_iter()
                .map(|(name, ty, default)| Node::gen(Param { name, ty, default }))
                .collect_vec(),
        ))
    }
}
