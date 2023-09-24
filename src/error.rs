//! Custom error types.

use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum InsertError {
    #[error("provided range is invalid: need an ascending closed range")]
    InvalidRange,
}

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum LookupError {
    #[error("provided range is invalid: need an ascending closed range")]
    InvalidRange,
}
