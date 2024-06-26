//! Lisp parser.
//!

use crate::{
    data::{Pair, Ptr, Storage},
    reader::{token::Token, ReadErr},
};

use super::{token::TokenOffset, ReadResult};

enum SValue<'a> {
    ListStart { line: usize, column: usize },
    Pointer(Ptr<'a>),
}

impl<'a> From<Ptr<'a>> for SValue<'a> {
    fn from(value: Ptr<'a>) -> Self {
        SValue::Pointer(value)
    }
}

/// Parse the input stream into a list of Lisp expressions.
///
/// If successful, returns a pointer to the body.
///
/// Note that (per the signature) this does not run garbage collection.
/// If parsing fails, it is recommended to run GC afterwards, to clean up anything generated by failed parsing.
pub fn parse(store: &Storage, input: impl Iterator<Item = TokenOffset>) -> ReadResult<Ptr> {
    let mut stack: Vec<_> = Default::default();

    for token in input {
        let top = match token.token {
            Token::Integer(i) => store.put(i).into(),
            Token::Float(f) => store.put(f).into(),
            Token::String(s) => store.put_string(s.as_bytes()).into(),
            Token::Symbol(s) => store.put_symbol(&s).into(),
            Token::LParen => SValue::ListStart {
                line: token.line,
                column: token.column,
            },
            Token::RParen => {
                // We have the list in reverse order; cons it.
                let mut acc = Ptr::nil();
                loop {
                    match stack.pop() {
                        None => {
                            return Err(ReadErr::Error(format!(
                                "unmatched closing paren at line {} column {}",
                                token.line, token.column
                            )))
                        }
                        Some(SValue::Pointer(p)) => acc = store.put(Pair { car: p, cdr: acc }),
                        Some(SValue::ListStart { .. }) => break,
                    }
                }
                acc.into()
            }
            Token::Quote => todo!(),
        };
        stack.push(top);
    }

    // Our stack should be a stack of expressions.
    // We should be able to pop and cons a list from them; if not, there's an unmatched opening paren somewhere.
    let mut acc = Ptr::nil();
    while let Some(it) = stack.pop() {
        match it {
            SValue::ListStart { line, column } =>
            // This expression isn't closed; we're in an incomplete parse state.
            {
                return Err(ReadErr::Incomplete(format!(
                    "unmatched opening paren at line {} column {}",
                    line, column
                )))
            }
            SValue::Pointer(ptr) => {
                acc = store.put(Pair::cons(ptr, acc));
            }
        }
    }

    Ok(acc)
}
