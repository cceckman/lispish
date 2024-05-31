//! Routines for tokenization.
//!
//! ## Speculative design
//!
//! To keep the interpreter in fixed memory,
//! the tokenizer operates as a series of iterators.
//!
//! The `Tokenizer` iterates over a character iterator,
//! and produces `Token`s.
//!

use lispish_store::{ByteVector, Ptr, Storage};

struct Tokenizer<'a, CharIter> {
    store: &'a Storage,
    characters: CharIter,

    buffer: [char; 8],
    buf_len: usize,
}

enum TokenType {
    LParen,
    RParen,
    Quote,
    String,
}

struct Token<'a> {
    tt: TokenType,
    content: Option<ByteVector<'a>>,
    location: Ptr<'a>,
}
