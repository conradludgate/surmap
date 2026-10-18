/// Reservation can fail in either the entry vector or a hash index.
#[derive(Debug)]
pub enum TryReserveError {
    /// The entry vector or a temporary rehash buffer could not reserve memory.
    Entries(std::collections::TryReserveError),
    /// A key or value hash index could not reserve memory.
    Index(hashbrown::TryReserveError),
}

impl std::fmt::Display for TryReserveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Entries(err) => err.fmt(f),
            Self::Index(err) => write!(f, "hash index reservation failed: {err:?}"),
        }
    }
}

impl std::error::Error for TryReserveError {}
