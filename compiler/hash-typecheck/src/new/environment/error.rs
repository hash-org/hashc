pub enum TcError {
    /// @@Todo: write out error variants
    Err,
}

pub type TcResult<T> = Result<T, TcError>;
