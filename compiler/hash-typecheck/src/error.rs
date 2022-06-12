use crate::storage::primitives::KindId;

pub type TcResult<T> = Result<T, TcError>;

pub enum TcError {
    CannotUnify(KindId, KindId),
}
