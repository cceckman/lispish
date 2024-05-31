#![cfg_attr(not(feature = "std"), no_std)]
//! Reader for Lispish.
//!
//! The reader operates on a string that is already in the Lisp store.
//! It:
//! - Tokenizes the string (or returns an error)
//! - Parses the string (or returns an error)
//! -

use lispish_store::{Error, Ptr, Storage};

mod location;
mod tokens;

pub struct Reader<'a> {
    store: &'a mut Storage,
}

impl<'a> Reader<'a> {
    pub fn new(store: &'a mut Storage) -> Self {
        Reader { store }
    }

    pub fn parse(&mut self, input: Ptr<'a>) -> Result<(), Error> {
        todo!()
    }
}
