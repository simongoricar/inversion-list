use thiserror::Error;

use crate::error::InsertError;

#[derive(Error, Clone, Debug)]
pub enum TestError {
    #[error("insertion error: {0}")]
    InsertError(#[from] InsertError),
}

pub type TestResult = Result<(), TestError>;
