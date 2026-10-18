#![forbid(unsafe_code)]
#![warn(missing_docs)]
#![doc = include_str!("../README.md")]

mod bidi_table;
mod bimap;
mod error;
mod iter;
#[cfg(feature = "serde")]
mod serde_impl;
mod surmap;

pub use bimap::{BiMap, InsertResult};
pub use error::TryReserveError;
pub use hashbrown::Equivalent;
pub use iter::{Drain, IntoIter, Iter, SurMapKeysIter};
pub use surmap::SurMap;
