//! Basic Lisp parser (and eventually evaluator) for RC application.
//!
//! Restrictions:
//! - Only integer numbers, not all numeric formats
//! - Probably other things because I don't know Lisp?
//!


// I read a little of Practical Common Lisp (https://gigamonkeys.com/book/) to understand the basic syntax,
// but stopped once I understood that "forms" matter (only) in the evaluation phase.
//
// My first draft of this parser was based on iterators: an iterator over `char`s becomes an iterator over
// tokens, then an iterator over tokens becomes an iterator over expressions.
//
// But that's a more complicated interaction than we really need. Even with REPL-style interaction, we want to allow
// waiting for at least a full line at a time before we start parsing.
// 
// Where I landed was on was "parse a &str into SExpressions"...but have the error type distinguish between
// "this has an error", e.g. an extra RParen, and "this is a conceivable prefix, but is missing a closing paren / string terminator / etc"
// I think this is useful for a REPL; we try to parse on each newline,
// and we either raise an error or ask for more input depending on the result.
// (If the caller reads from a file, they're both errors.)
//

use std::{convert::Infallible, fmt::Display, str::FromStr};

mod reader;

pub mod prelude {
    pub use crate::{Atom, LispNumber, LispString, LispSymbol, SExpression};
}

pub use reader::{ReadErr,read};

/// A Lisp S-expression.
/// Either a list or an atom.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpression {
    List(Vec<SExpression>),
    Atom(Atom),
}

/// A Lisp atom.
/// - A symbol: an unquoted string referring to a variable, function, macro...
/// - A string: a quoted string, representing a sequence of characters
/// - A number: a numeric value.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Atom {
    Symbol(LispSymbol),
    String(LispString),
    Number(LispNumber),
}

/// A string literal.
/// This wrapper type contains the actual value;
/// the Display implementation renders it with appropriate escapes.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LispString(String);

/// A Lisp symbol.
/// Converting to a LispSymbol canonicalizes the string (i.e. uses uppercase).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LispSymbol(String);

/// A Lisp number.
/// Just "signed integer" for now; consider support for other numeric types in the future.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LispNumber(i64);

impl From<LispString> for Atom {
    fn from(value: LispString) -> Self {
        Atom::String(value)
    }
}
impl From<LispSymbol> for Atom {
    fn from(value: LispSymbol) -> Self {
        Atom::Symbol(value)
    }
}
impl From<LispNumber> for Atom {
    fn from(value: LispNumber) -> Self {
        Atom::Number(value)
    }
}
impl From<Atom> for SExpression {
    fn from(value: Atom) -> Self {
        SExpression::Atom(value)
    }
}

impl Display for LispString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Escape quotes and backslashes; everything else is literal.
        let formatted = self.0.replace('\\', "\\\\").replace("\"", "\\\"");
        write!(f, "\"{}\"", formatted)
    }
}

impl FromStr for LispString {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(LispString(s.to_owned()))
    }
}

impl FromStr for LispSymbol {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(LispSymbol(s.to_uppercase()))
    }
}

impl Display for LispSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for LispNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Symbol(x) => x.fmt(f),
            Atom::String(x) => x.fmt(f),
            Atom::Number(x) => x.fmt(f),
        }
    }
}

impl Display for SExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO - This implementation leans in to Lisp's recursion, so it generates stack frames
        // equal to the expression tree depth.
        // I should consider not using Rust's stack for that, using an explicit stack instead;
        // also makes it easier to pretty-print (depth for indents), etc.
        // But this will do for now.
        match self {
            SExpression::Atom(x) => x.fmt(f),
            SExpression::List(x) => {
                write!(f, "(")?;
                // Streaming "join":
                let spaces = std::iter::repeat(" ")
                    .take(x.len() - 1)
                    .chain(std::iter::once(""));
                for (atom, space) in x.iter().zip(spaces) {
                    write!(f, "{}{}", atom, space)?;
                }
                write!(f, ")")
            }
        }
    }
}
