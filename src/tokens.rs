//! Lisp syntax support.
//!
//! This module provides support for parsing and printing Lisp expressions.
//! For each type, the Display implementation renders the expression as a string
//! (that can be parsed back as the same type.)
//!
//! Limitations:
//! - Only i64 numbers are supported.
//! - Symbols are strictly "non-strings"; not doing any limitations on character sets or interning.
//!
//! This would be a good opportunity to learn what a parser combinator is and use it?
//! Or to use a regex library. But I'm having fun doing it without libraries.

use std::iter::{Enumerate, Peekable};

use crate::prelude::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Token {
    LParen,
    Atom(Atom),
    RParen,
}

struct Tokenizer<I>
where
    I: Iterator<Item = char>,
{
    input: Peekable<Enumerate<I>>,
}

impl<I> Tokenizer<I>
where
    I: Iterator<Item = char>,
{
    fn new(input: I) -> Self {
        Tokenizer {
            input: input.enumerate().peekable(),
        }
    }

    /// Parser helper: get a symbol, starting at our current position.
    fn get_symbol(&mut self) -> Result<Token, String> {
        // LispSymbol is canonicalized to uppercase:
        let s = self.get_non_terminator().to_uppercase();

        Ok(Token::Atom(Atom::Symbol(LispSymbol(s))))
    }

    /// Parser helper: get the contiguous characters that aren't terminals.
    /// This is the underlying routine for symbols and numbers;
    /// the number routine further requires that it parses as a number.
    fn get_non_terminator(&mut self) -> String {
        // This is pretty simple; we just have to keep pulling until we hit a token terminator.
        let mut string = String::new();
        while let Some((_, ch)) = self.input.peek() {
            if *ch == '(' || *ch == ')' || ch.is_whitespace() {
                break;
            } else {
                string.push(*ch);
                self.input.next();
            }
        }
        string
    }

    /// Parser helper: get a string, starting at our current position.
    fn get_string(&mut self) -> Result<Token, String> {
        // TODO: Keep track of the line number too!

        // Our starting position should be the start-of-string character.
        // Check (without panicking, we can return an error.)
        let (start_position, start_ch) = self
            .input
            .next()
            .ok_or_else(|| {
                "internal error: expected start-of-string, but at end-of-file".to_owned()
            })
            .and_then(|(position, ch)| {
                if ch != '"' {
                    Err(format!(
                        "internal error: expected start-of-string at position {}, but found {:?}",
                        position, ch
                    ))
                } else {
                    Ok((position, ch))
                }
            })?;

        let mut string = String::new();
        // Mini-lanaguge for strings:
        // A backslash always escapes the next character.
        // An unescaped double-quote terminates the string.
        let mut escaped = false;
        // We always consume a character.
        while let Some((_, ch)) = self.input.next() {
            if escaped {
                escaped = false;
                string.push(ch);
            } else if ch == start_ch {
                return Ok(Token::Atom(Atom::String(LispString(string))));
            } else {
                string.push(ch);
                escaped = ch == '\\';
            }
        }
        // Exited the loop without encountering the paired start-of-string character.
        // Throw an error.
        Err(
            format!("tokenizing error: failed to parse string starting at character {}: could not find terminal {:?}", start_position, start_ch)
        )
    }

    /// Parser helper: get a number, starting at our current position.
    fn get_number(&mut self) -> Result<Token, String> {
        let (position, _) = self
            .input
            .peek()
            .ok_or_else(|| "internal error: expected numeric, but at end of input".to_owned())?
            .to_owned();
        let s = self.get_non_terminator();
        let number: i64 = s.parse().map_err(|err| {
            format!(
                "tokenizing error: at character {}, could not parse {:?} as a number: {}",
                position, s, err
            )
        })?;

        Ok(Token::Atom(Atom::Number(number)))
    }
}

impl<I> Iterator for Tokenizer<I>
where
    I: Iterator<Item = char>,
{
    type Item = Result<Token, String>;

    fn next(&mut self) -> Option<Self::Item> {
        // Forward over any whitespace:
        while let Some((_, ch)) = self.input.peek() {
            if ch.is_whitespace() {
                self.input.next();
            } else {
                break;
            }
        }
        let (_, token_start) = self.input.peek()?;

        match token_start {
            '(' => {
                self.input.next();
                return Some(Ok(Token::LParen));
            }
            ')' => {
                self.input.next();
                return Some(Ok(Token::RParen));
            }
            '"' => Some(self.get_string()),
            '0'..='9' | '-' => Some(self.get_number()),
            _ => Some(self.get_symbol()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;

    #[test]
    fn tokenize_atoms() -> Result<(), String> {
        let input = "hello \"hi\" world 24601 -6";
        let output: Result<Vec<Token>, _> = Tokenizer::new(input.chars()).collect();
        let output = output?;

        let want = &[
            Token::Atom(Atom::Symbol("HeLlO".parse().unwrap())),
            Token::Atom(Atom::String("hi".parse().unwrap())),
            Token::Atom(Atom::Symbol("world".parse().unwrap())),
            Token::Atom(Atom::Number(24601)),
            Token::Atom(Atom::Number(-6)),
        ];

        assert_eq!(output.len(), want.len());

        for ((i, got), want) in output.iter().enumerate().zip(want.iter()) {
            assert_eq!(got, want, "unexpected token in case {}", i);
        }
        Ok(())
    }

    #[test]
    fn tokenize_parens() -> Result<(), String> {
        let input = "(1)( 2 ) (hello) ( hello (\"hi\") (( \"hi\" )))";
        let output: Result<Vec<Token>, _> = Tokenizer::new(input.chars()).collect();
        let output = output?;

        let want = &[
            Token::LParen,
            Token::Atom(Atom::Number(1)),
            Token::RParen,
            Token::LParen,
            Token::Atom(Atom::Number(2)),
            Token::RParen,
            Token::LParen,
            Token::Atom(Atom::Symbol("hello".parse().unwrap())),
            Token::RParen,
            Token::LParen,
            Token::Atom(Atom::Symbol("hello".parse().unwrap())),
            Token::LParen,
            Token::Atom(Atom::String("hi".parse().unwrap())),
            Token::RParen,
            Token::LParen,
            Token::LParen,
            Token::Atom(Atom::String("hi".parse().unwrap())),
            Token::RParen,
            Token::RParen,
            Token::RParen,
        ];

        assert_eq!(output.len(), want.len());

        for ((i, got), want) in output.iter().enumerate().zip(want.iter()) {
            assert_eq!(got, want, "unexpected token in case {}", i);
        }
        Ok(())
    }

    #[test]
    fn tokenize_unbalanced() -> Result<(), String> {
        let input = ")))()(";
        let output: Result<Vec<Token>, _> = Tokenizer::new(input.chars()).collect();
        let output = output?;

        let want = &[
            Token::RParen,
            Token::RParen,
            Token::RParen,
            Token::LParen,
            Token::RParen,
            Token::LParen,
        ];

        assert_eq!(output.len(), want.len());

        for ((i, got), want) in output.iter().enumerate().zip(want.iter()) {
            assert_eq!(got, want, "unexpected token in case {}", i);
        }
        Ok(())
    }

    #[test]
    fn escaped_string() {
        let input = r#"  
        "hello \"sons\" \\slashdaughters a\nd others "   "#;
        let output: Result<Vec<Token>, _> = Tokenizer::new(input.chars()).collect();
        let output = output.unwrap();
        let trimmed = input.trim().trim_matches('"');

        assert_eq!(output.len(), 1);
        assert_eq!(output[0], Token::Atom(Atom::String(LispString(trimmed.to_owned()))));
    }


    #[test]
    fn error_on_unexpected_stringend() {
        let input = "\"hello";
        let output: Result<Vec<Token>, _> = Tokenizer::new(input.chars()).collect();
        output.expect_err("no error for unmatched end-quote");
    }

    #[test]
    fn error_on_escaped_stringend() {
        let input = "\"hello\\\"";
        let output: Result<Vec<Token>, _> = Tokenizer::new(input.chars()).collect();
        output.expect_err("no error for escaped end-quote");
    }
}
