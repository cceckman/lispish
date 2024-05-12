//! Routines for tokenization.

struct Tokenizer<CharIter> {
    characters: CharIter,
    buffer: [char; 8],
    buf_len: usize,
}

impl<CharIter> From<CharIter> for Tokenizer<CharIter>
where
    CharIter: Iterator<Item = char>,
{
    fn from(characters: CharIter) -> Self {
        Tokenizer {
            characters,
            buffer: Default::default(),
            buf_len: 0,
        }
    }
}

enum TokenType {
    LParen,
    RParen,
    Quote,
    String,
}

struct Token {}
