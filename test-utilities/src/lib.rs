use thiserror::Error;


#[derive(Error, Clone, Debug)]
pub enum TestError {
    #[error("insertion error: {0}")]
    InsertError(#[from] inversion_list::error::InsertError),
}

pub type TestResult = Result<(), TestError>;
