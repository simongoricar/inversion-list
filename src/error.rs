//! Custom error types.

use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum InsertError {
    #[error("provided range is invalid: need an ascending closed range")]
    InvalidRange,

    /// Note: this can only be returned when using [`InversionMap::try_insert`][super::InversionMap::try_insert],
    /// and **not** when using the forceful version of it
    /// ([`InversionMap::insert_with_overwrite`][super::InversionMap::insert_with_overwrite]).
    #[error("the provided range collsides with an existing entry")]
    CollidesWithExistingEntry,
}

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum LookupError {
    #[error("provided range is invalid: need an ascending closed range")]
    InvalidRange,
}
