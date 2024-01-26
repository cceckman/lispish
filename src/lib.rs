//! Basic Lisp parser (and eventually evaluator) for RC application.
//!
//! Restrictions:
//! - Only integer numbers, not all numeric formats
//! - Probably other things because I don't know Lisp?
//!
//! I read a little of Practical Common Lisp (https://gigamonkeys.com/book/) to understand the basic syntax,
//! but stopped once I understood that "forms" matter (only) in the evaluation phase.

use std::{convert::Infallible, fmt::Display, str::FromStr};

mod tokens;

pub mod prelude {
    pub use crate::{SExpression,Atom,LispNumber,LispString,LispSymbol};
}


/// A Lisp S-expression.
/// Either a list or an atom.
#[derive(Clone, Debug)]
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
pub type LispNumber = i64;

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
