use crate::storage::primitives::TyId;

pub type TcResult<T> = Result<T, TcError>;

pub enum TcError {
    CannotUnify(TyId, TyId),
}
