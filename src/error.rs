use rust_asm::error::ClassReadError;
use std::error::Error as StdError;
use std::fmt::{Display, Formatter};

pub type Result<T> = std::result::Result<T, DecompileError>;

#[derive(Debug)]
pub enum DecompileError {
    Io(std::io::Error),
    ClassRead(ClassReadError),
    InvalidClass(String),
    Unsupported(String),
    Usage(String),
}

impl Display for DecompileError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            DecompileError::Io(error) => write!(f, "io error: {error}"),
            DecompileError::ClassRead(error) => write!(f, "class read error: {error}"),
            DecompileError::InvalidClass(message) => write!(f, "invalid class: {message}"),
            DecompileError::Unsupported(message) => write!(f, "unsupported feature: {message}"),
            DecompileError::Usage(message) => write!(f, "{message}"),
        }
    }
}

impl StdError for DecompileError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            DecompileError::Io(error) => Some(error),
            DecompileError::ClassRead(error) => Some(error),
            DecompileError::InvalidClass(_)
            | DecompileError::Unsupported(_)
            | DecompileError::Usage(_) => None,
        }
    }
}

impl From<std::io::Error> for DecompileError {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

impl From<ClassReadError> for DecompileError {
    fn from(value: ClassReadError) -> Self {
        Self::ClassRead(value)
    }
}
