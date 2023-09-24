//! Custom error types.

use thiserror::Error;

#[derive(Error, Debug, Clone)]
pub enum InsertError {
    #[error("provided range is invalid: need an ascending closed range")]
    InvalidRange,
}
