//! Module for extracting Lisp tokens from an input stream.

use crate::reader::ReadResult;
use crate::{data, reader::*};

/// A Lisp token.
///
/// Whitespace and comments are ignored.
#[derive(Debug, PartialEq, PartialOrd)]
pub enum Token {
    LParen,
    RParen,
    Dot,
    Quote,
    String(String),
    Symbol(String),
    Integer(data::Integer),
    Float(data::Float),
}

/// A token along with its starting position in the input stream.
#[derive(Debug, PartialEq, PartialOrd)]
pub struct TokenOffset {
    pub token: Token,
    pub line: usize,
    pub column: usize,
}

/// Split the input into its constituent tokens.
pub fn tokenize(mut input: &[u8]) -> ReadResult<Vec<TokenOffset>> {
    let mut result = Vec::new();

    // Position info for debug messages:
    // Line number (starting from 0 - fix it up when doing output)
    let mut line = 0;
    let mut column = 0;
    while !input.is_empty() {
        let next = get_next_token(input)
            .map_err(|err| err.annotate(format!("at line {} column {}", line + 1, column + 1)))?;

        if let Some(token) = next.token {
            result.push(TokenOffset::new(line, column, token));
        }
        line += next.lines;
        if next.lines > 0 {
            column = next.columns
        } else {
            column += next.columns;
        }

        input = next.remainder;
    }

    Ok(result)
}

impl TokenOffset {
    fn new(line: usize, column: usize, token: Token) -> Self {
        // In useful output, lines and columns are 1-indexed
        TokenOffset {
            token,
            line: line + 1,
            column: column + 1,
        }
    }
}

impl From<TokenOffset> for Token {
    fn from(value: TokenOffset) -> Self {
        value.token
    }
}

#[derive(Default)]
struct NextToken<'a> {
    // Token retrieved, if any.
    // May be None if only whitespace was consumed,
    // or if the end-of-file was reached.
    token: Option<Token>,
    // Lines traversed in finding the token.
    lines: usize,
    // Columns in the final line traversed in finding the token.
    columns: usize,

    // Remaining string.
    remainder: &'a [u8],
}

mod regex {
    use regex::bytes::Regex;
    use std::sync::OnceLock;

    pub(super) fn space() -> &'static Regex {
        static SPACE: OnceLock<Regex> = OnceLock::new();
        SPACE.get_or_init(|| {
            Regex::new("\\A[[:space:]]+").expect("could not compile regex for empty space")
        })
    }

    pub(super) fn string() -> &'static Regex {
        static STRING: OnceLock<Regex> = OnceLock::new();
        STRING.get_or_init(|| {
            // Quote,
            // followed by:
            //  - a backslash + character (an escaped character, of any sort), or
            //  - any character other than a quote or backslash
            // repeatedly
            // We do _not_ require the trailing quote; we check that after consuming the
            // regex, so we can return "early end" if we haven't closed the quote.
            Regex::new(r#"\A(?sR)"([\\][\\]|[\\]"|[^\"])*"#)
                .expect("could not compile regex for string")
        })
    }

    pub(super) fn integer() -> &'static Regex {
        static MATCH: OnceLock<Regex> = OnceLock::new();
        MATCH.get_or_init(|| {
            Regex::new(r#"\A-?[0-9]+"#).expect("could not compile regex for integer")
        })
    }

    pub(super) fn float() -> &'static Regex {
        static MATCH: OnceLock<Regex> = OnceLock::new();
        MATCH.get_or_init(|| {
            Regex::new(r#"\A-?[0-9]+[.][0-9]*"#).expect("could not compile regex for float")
        })
    }

    pub(super) fn symbol() -> &'static Regex {
        static MATCH: OnceLock<Regex> = OnceLock::new();
        MATCH.get_or_init(|| {
            Regex::new(r#"\A[^;[:space:]'()."]+"#).expect("could not compile regex for symbol")
        })
    }

    pub(super) fn comment() -> &'static Regex {
        static MATCH: OnceLock<Regex> = OnceLock::new();
        MATCH.get_or_init(|| Regex::new(r#"\A;.*"#).expect("could not compile regex for comment"))
    }
}

/// Returns the (line, column) that the cursor ends at, after following the given path,
/// assuming it started at (0, 0).
/// Tabs still count as a single column
/// TODO: Establish tabstop?
fn cursor_distance(s: &[u8]) -> (usize, usize) {
    let mut line_count = 0;
    let last_line_start = s
        .iter()
        .enumerate()
        .filter(|(_, &c)| c == b'\n')
        .map(|v| {
            line_count += 1;
            v
        })
        .last()
        .map(|(x, _)| x + 1)
        .unwrap_or(0);
    let column = s.len() - last_line_start;
    (line_count, column)
}

/// Get the next token from the input, and return the remainder of the input.
fn get_next_token(input: &[u8]) -> ReadResult<NextToken<'_>> {
    // Shouldn't bother calling if the remainder is none.
    assert!(!input.is_empty());

    // Single-character matchers:
    if let Some(token) = match input[0] {
        b'(' => Some(Token::LParen),
        b')' => Some(Token::RParen),
        b'\'' => Some(Token::Quote),
        b'.' => Some(Token::Dot),
        _ => None,
    } {
        return Ok(NextToken {
            token: Some(token),
            lines: 0,
            columns: 1,
            remainder: &input[1..],
        });
    };

    // Regex matchers:
    if let Some(space) = regex::space().find(input) {
        let (lines, columns) = cursor_distance(space.as_bytes());
        return Ok(NextToken {
            token: None,
            lines,
            columns,
            remainder: &input[space.as_bytes().len()..],
        });
    }
    if let Some(s) = regex::string().find(input) {
        let s = s.as_bytes();
        let remainder = &input[s.len()..];
        if remainder.len() == 0 || remainder[0] != b'"' {
            // No closing quote; consider this a premature end.
            // That's okay!
            return Err(ReadErr::Incomplete("incomplete string".to_owned()));
        }
        assert_eq!(remainder[0], b'"');
        assert_eq!(s[0], b'"');
        let true_remainder = &remainder[1..];
        let escaped_bytes = &s[1..];
        let escaped_string = std::str::from_utf8(escaped_bytes)
            .map_err(|_| ReadErr::Error("non-UTF-8 string".to_owned()))?;
        let true_string = escaped_string
            .replace(r#"\\"#, r#"\"#)
            .replace(r#"\""#, r#"""#);
        let (lines, columns) = cursor_distance(true_string.as_bytes());
        return Ok(NextToken {
            token: Some(Token::String(true_string)),
            lines,
            columns,
            remainder: true_remainder,
        });
    }

    if let Some(s) = regex::float().find(input) {
        let s = std::str::from_utf8(s.as_bytes())
            .expect("internal error: regex recognized float that was not utf-8");
        let float: data::Float = s.parse().map_err(|e| {
            ReadErr::Error(format!("failed to convert \"{}\" into float: {}", s, e))
        })?;
        let remainder = &input[s.len()..];
        return Ok(NextToken {
            token: Some(Token::Float(float)),
            lines: 0,
            columns: s.len(),
            remainder,
        });
    }

    if let Some(s) = regex::integer().find(input) {
        let s = std::str::from_utf8(s.as_bytes())
            .expect("internal error: regex recognized integer that was not utf-8");
        let int: data::Integer = s.parse().map_err(|e| {
            ReadErr::Error(format!("failed to convert \"{}\" into integer: {}", s, e))
        })?;
        let remainder = &input[s.len()..];
        return Ok(NextToken {
            token: Some(Token::Integer(int)),
            lines: 0,
            columns: s.len(),
            remainder,
        });
    }

    if let Some(s) = regex::symbol().find(input) {
        let s = std::str::from_utf8(s.as_bytes())
            .expect("internal error: recognized symbol that was not UTF-8");
        let (lines, columns) = cursor_distance(s.as_bytes());
        let remainder = &input[s.len()..];
        // We leave "canonicalize to uppercase" for later, when we go from a "symbol token" to a "symbol".
        // This should let our debug output look more similar to our input.
        return Ok(NextToken {
            token: Some(Token::Symbol(s.to_owned())),
            lines,
            columns,
            remainder,
        });
    }

    if let Some(s) = regex::comment().find(input) {
        let (lines, columns) = cursor_distance(s.as_bytes());
        let remainder = &input[s.len()..];
        return Ok(NextToken {
            token: None,
            lines,
            columns,
            remainder,
        });
    }

    Err(ReadErr::Error(
        "could not parse remainder of input as anything".to_owned(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader::ReadErr;

    #[test]
    fn recognize_symbols() -> Result<(), String> {
        for sym in [
            "hello",
            "hi",
            "tree->list",
            "operator<>",
            "Queryable?",
            "IMPORTANT!",
        ] {
            let r = token::regex::symbol();
            if !r.is_match(sym.as_bytes()) {
                return Err(format!("did not find symbol {}", sym));
            }
        }
        Ok(())
    }

    #[test]
    fn tokenize_atoms() -> Result<(), ReadErr> {
        let input = br#"hello "hi" world 24601 -6 -3.33 3.22"#;
        let output: Vec<Token> = tokenize(input)?.into_iter().map(|v| v.token).collect();

        let want = &[
            Token::Symbol("hello".to_owned()),
            Token::String("hi".to_owned()),
            Token::Symbol("world".to_owned()),
            Token::Integer(24601),
            Token::Integer(-6),
            Token::Float(-3.33),
            Token::Float(3.22),
        ];

        assert_eq!(output.len(), want.len());

        for ((i, got), want) in output.iter().enumerate().zip(want.iter()) {
            assert_eq!(got, want, "unexpected token in case {}", i);
        }
        Ok(())
    }
    #[test]
    fn tokenize_parens() -> Result<(), ReadErr> {
        let input = b"(1)( 2 ) (hello) ( hello (\"hi\") (( \"hi\" )))";
        let output: Vec<Token> = tokenize(input)?.into_iter().map(|v| v.token).collect();

        let want = &[
            Token::LParen,
            Token::Integer(1),
            Token::RParen,
            Token::LParen,
            Token::Integer(2),
            Token::RParen,
            Token::LParen,
            Token::Symbol("hello".parse().unwrap()),
            Token::RParen,
            Token::LParen,
            Token::Symbol("hello".parse().unwrap()),
            Token::LParen,
            Token::String("hi".parse().unwrap()),
            Token::RParen,
            Token::LParen,
            Token::LParen,
            Token::String("hi".parse().unwrap()),
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
    fn tokenize_unbalanced() -> Result<(), ReadErr> {
        let input = b")))()(";
        let output: Vec<Token> = tokenize(input)?.into_iter().map(|v| v.token).collect();

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
    fn error_on_unexpected_stringend() {
        let input = br#"(
"hello1"
 "hello

)"#;
        // Our example ends with the string-start at line 3 (1-indexed),
        // column 2 (1-indexed)

        match tokenize(input) {
            Ok(_) => panic!("expected error for input"),
            Err(ReadErr::Error(e)) => panic!(
                "got terminal error, expected incomplete error; got: {:?}",
                e
            ),
            Err(ReadErr::Incomplete(e)) => {
                // We got the error that we want...Does it have the useful debug info?
                let want_line = "line 3";
                let want_col = "column 2";
                assert!(
                    e.contains(want_line),
                    "missing line info from error string: {:?}",
                    e
                );
                assert!(
                    e.contains(want_col),
                    "missing column info from error string: {:?}",
                    e
                );
            }
        }
    }

    #[test]
    fn error_on_escaped_stringend() {
        // This Lisp string has:
        // - An unescaped quote (which starts a string)
        // - An escaped quote (which is a quote, inside the string)
        // - An escaped backslash (which is a backslash, inside the string)
        // - An escaped quote (which is a quote, inside the string)
        // But no end-quote, so it's incomplete.
        let input = br#"
            "\"hello\\\"
        "#;

        match tokenize(input) {
            Ok(_) => panic!("expected error for input"),
            Err(ReadErr::Error(e)) => panic!(
                "got terminal error, expected incomplete error; got: {:?}",
                e
            ),
            Err(ReadErr::Incomplete(_)) => (),
        }
    }

    #[test]
    fn string_escapes() {
        // This Lisp string has:
        // - An unescaped quote (which starts a string)
        // - An escaped quote (which is a quote, inside the string)
        // - An escaped backslash (which is a backslash, inside the string)
        // - An escaped quote (which is a quote, inside the string)
        // - A newline
        // - Several indents
        let input = br#"
            "\"hello\\\"
            "
        "#;

        let tokens = tokenize(input).unwrap();
        assert_eq!(tokens.len(), 1);
        let token = &tokens[0];
        assert_eq!(
            token.token,
            Token::String(
                r#""hello\"
            "#
                .to_owned()
            )
        );
    }
}
