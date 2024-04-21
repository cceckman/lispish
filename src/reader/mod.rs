//! Support for reading LISP expressions from strings.

use std::io::ErrorKind;

pub use parse::parse;
pub use token::tokenize;

mod parse;
mod token;

/// Error type if a read does not complete.
///
/// A reader may experience a true tokenizing/parsing error, e.g. "())", that no additional input can fix.
/// This is distinct from a reader that gets an unexpected end-of-input, e.g. "(()":
/// it may be that more input will fix the issue.
///
/// If input is coming in interactively, this is a useful distinction;
/// in the first case, we'd want to indicate an error to the user,
/// while in the latter we'd like to prompt the user for more input.
///
/// This type covers this distinction.
#[derive(Debug, Clone)]
pub enum ReadErr {
    Error(String),
    Incomplete(String),
}

impl ReadErr {
    /// Add additional context to an error.
    pub fn annotate(self, more: impl AsRef<str>) -> Self {
        match self {
            ReadErr::Error(e) => ReadErr::Error(format!("{}: {}", more.as_ref(), e)),
            ReadErr::Incomplete(e) => ReadErr::Incomplete(format!("{}: {}", more.as_ref(), e)),
        }
    }
}

/// The main result type for this module:
/// a T (token, expression, etc), or an error, or incomplete.
pub type ReadResult<T> = Result<T, ReadErr>;

impl<T> From<ReadErr> for ReadResult<T> {
    fn from(value: ReadErr) -> Self {
        Err(value)
    }
}

impl From<ReadErr> for std::io::Error {
    fn from(value: ReadErr) -> Self {
        match value {
            ReadErr::Incomplete(s) => std::io::Error::new(ErrorKind::BrokenPipe, s),
            ReadErr::Error(s) => std::io::Error::new(ErrorKind::InvalidInput, s),
        }
    }
}
