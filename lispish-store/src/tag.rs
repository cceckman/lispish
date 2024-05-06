//! Tags for Lisp object pointers.
//!
//! This is kept as a separate module so the u8 repr is not exposed.

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Tag {
    Nil = Self::NIL,
    Integer = Self::INTEGER,
    Float = Self::FLOAT,

    Symbol = Self::SYMBOL,
    Pair = Self::PAIR,

    Vector = Self::VECTOR,
    Bytes = Self::BYTES,
    String = Self::STRING,
}

impl Tag {
    const NIL: u8 = 0;
    const INTEGER: u8 = 1;
    const FLOAT: u8 = 2;

    const SYMBOL: u8 = 3;

    const PAIR: u8 = 4;

    const VECTOR: u8 = 5;
    const BYTES: u8 = 6;
    const STRING: u8 = 7;
}

impl From<u8> for Tag {
    fn from(value: u8) -> Self {
        match value {
            Self::NIL => Tag::Nil,
            Self::INTEGER => Tag::Integer,
            Self::FLOAT => Tag::Float,
            Self::SYMBOL => Tag::Symbol,
            Self::PAIR => Tag::Pair,
            Self::VECTOR => Tag::Vector,
            Self::BYTES => Tag::Bytes,
            Self::STRING => Tag::String,
            v => unreachable!("invalid tag value {v}"),
        }
    }
}
