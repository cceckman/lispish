//! Support for reading LISP expressions from strings.

use crate::prelude::*;

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

/// The main result type for this module:
/// a T (token, expression, etc), or an error, or incomplete.
pub type ReadResult<T> = Result<T, ReadErr>;

/// Attempt to read the provided input as an SExpression.
///
/// A result of Incomplete indicates that the provided input may become complete if
/// more input is provided. The associated string gives an indication as to what is expected.
/// If parsing dynamic input (e.g. stdin), the user may wish to wait for more input;
/// if parsing state input (e.g. a file), Incomplete may be treated as a read error.
pub fn read(input: &str) -> ReadResult<Vec<SExpression>> {
    // I'd like to `impl Try for ReadResult` but
    let tok = tokens::tokenize(input)?;
    parse::parse(tok.into_iter())
}

mod tokens {
    use std::iter::Peekable;

    use super::*;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Token {
        LParen,
        Atom(Atom),
        RParen,
    }

    /// Token along with its starting position in the input stream.
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct TokenOffset {
        pub token: Token,
        pub line: usize,
        pub column: usize,
    }

    impl TokenOffset {
        pub fn new(line: usize, column: usize, token: Token) -> Self {
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

    /// Split the input into its constituent tokens.
    pub fn tokenize(input: &str) -> ReadResult<Vec<TokenOffset>> {
        let mut result = Vec::new();

        let mut characters = input.chars().enumerate().peekable();

        // Position info for debug messages:
        // Line number (starting from 0 - fix it up when doing output)
        let mut line = 0;
        // Absolute offset at which the current line started; for computing column counts.
        let mut line_start = 0;
        loop {
            // We have to use this rather than `while peek` to avoid a double-borrow;
            // the `while` construct borrows `characters`.
            let (offset, c) = match characters.peek() {
                Some(v) => v.to_owned(),
                None => break,
            };

            let token: ReadResult<Token> = match c {
                '(' => {
                    characters.next();
                    Ok(Token::LParen)
                }

                ')' => {
                    characters.next();
                    Ok(Token::RParen)
                }
                '"' => get_string(&mut characters).map(|v| Token::Atom(Atom::String(v))),
                '0'..='9' | '-' => {
                    get_number(&mut characters).map(|v| Token::Atom(Atom::Number(v)))
                }
                '\n' => {
                    line += 1;
                    line_start = offset + 1;
                    characters.next();
                    continue;
                }
                c => {
                    if c.is_whitespace() {
                        characters.next();
                        continue;
                    } else {
                        get_symbol(&mut characters).map(|v| Token::Atom(Atom::Symbol(v)))
                    }
                }
            };
            let column = offset - line_start;
            let next = match token {
                Err(ReadErr::Incomplete(v)) => Err(ReadErr::Incomplete(format!(
                    "incomplete input at line {} column {}: {}",
                    line + 1, column + 1, v
                ))),
                Err(ReadErr::Error(v)) => Err(ReadErr::Incomplete(format!(
                    "input error at line {} column {}: {}",
                    line + 1, column + 1, v
                ))),

                Ok(token) => Ok(TokenOffset::new(line, column, token)),
            }?;

            // One final fixup: our string parser allows for multiline strings, just matching on the terminal '"'.
            // We need to make sure any newlines in our string token count towards the output.
            if let Token::Atom(Atom::String(s)) = &next.token {
                for (string_offset, c) in s.0.chars().enumerate() {
                    // This string started with its double-quote at 'offset', so this character's absolute offset is...
                    let char_abs_offset = offset + 1 + string_offset;
                    if c == '\n' {
                        line += 1;
                        line_start = char_abs_offset;
                    }
                }
            }

            result.push(next);
        }

        Ok(result)
    }

    /// Consumes a Lisp string from the input iterator.
    fn get_string(
        it: &mut Peekable<impl Iterator<Item = (usize, char)>>,
    ) -> ReadResult<LispString> {
        // Our starting position should be the start-of-string character.
        // Check and consume it (without panicking, we can return an error.)
        let (_, start_ch) = it
            .next()
            .ok_or_else(|| {
                ReadErr::Error(
                    "internal error: expected start-of-string, but at end-of-file".to_owned(),
                )
            })
            .and_then(|(position, ch)| {
                if ch != '"' {
                    Err(ReadErr::Error(format!(
                        "internal error: expected start-of-string {:?} but found {:?}",
                        '"', ch
                    )))
                } else {
                    Ok((position, ch))
                }
            })?;

        let mut string = String::new();
        // Inner language for string literals:
        // A backslash always escapes the next character.
        // An unescaped double-quote terminates the string.
        let mut escaped = false;
        // We always consume a character.
        while let Some((_, ch)) = it.next() {
            if escaped {
                escaped = false;
                string.push(ch);
            } else if ch == start_ch {
                return Ok(LispString(string));
            } else {
                string.push(ch);
                escaped = ch == '\\';
            }
        }

        // If we exited the loop without seeing the end-of string explicitly,
        // then we have incomplete input.
        Err(ReadErr::Incomplete(format!(
            "did not find string terminator"
        )))
    }

    /// Consumes a Lisp number from the input iterator.
    fn get_number(
        it: &mut Peekable<impl Iterator<Item = (usize, char)>>,
    ) -> ReadResult<LispNumber> {
        let s = get_contguous(it);
        // TODO: We only support i64 for numbers for now.
        let value: Result<i64, _> = s.parse();

        // There's only one kind of "incomplete" error I can think of for reading numbers:
        // If the user wrote `-` and that's all, then that would be interpreted as an unparseable
        // negative number.
        // I could be pedantic here and return "Incomplete"... but in practice, whatever is calling
        // this should probably wait for a newline or similar to parse anyway.
        // We'll leave this as a TODO / known-bug unless someone runs in to it.

        match value {
            Ok(v) => Ok(LispNumber(v)),
            Err(e) => Err(ReadErr::Error(format!(
                "could not parse string \"{}\" as a number: {}",
                s, e
            ))),
        }
    }

    /// Consumes a Lisp number from the input iterator.
    fn get_symbol(
        it: &mut Peekable<impl Iterator<Item = (usize, char)>>,
    ) -> ReadResult<LispSymbol> {
        let symbol = get_contguous(it);
        // There's no "incomplete" version for a symbol; it's either there, or isn't.
        symbol
            .parse()
            .map_err(|v| ReadErr::Error(format!("failed to parse symbol: {}", v)))
    }

    /// Consumes a stream of non-terminating characters (not whitespace or parens) from the input.
    /// This is an internal routine for numbers and symbols, both of which are delimited in this way.
    fn get_contguous(it: &mut Peekable<impl Iterator<Item = (usize, char)>>) -> String {
        // This is pretty simple; we just have to keep pulling until we hit a token terminator.
        let mut string = String::new();
        while let Some((_, ch)) = it.peek() {
            let ch = ch;
            if *ch == '(' || *ch == ')' || ch.is_whitespace() {
                break;
            } else {
                string.push(*ch);
                it.next();
            }
        }
        string
    }
}

mod parse {
    use crate::prelude::*;

    use super::{
        tokens::{Token, TokenOffset},
        ReadErr, ReadResult,
    };

    pub fn parse(mut tokens: impl Iterator<Item = TokenOffset>) -> ReadResult<Vec<SExpression>> {
        let mut results = Vec::new();
        while let Some(v) = parse_single(&mut tokens)? {
            results.push(v);
        }
        Ok(results)
    }

    /// Attemps to parse a single expression out of a stream of tokens.
    fn parse_single(
        tokens: &mut impl Iterator<Item = TokenOffset>,
    ) -> ReadResult<Option<SExpression>> {
        // I _think_ that the SExpression layer of syntax is context-free, so it can be parsed "with a stack".
        // The canonical way would be to push everything but RParen onto the parse stack;
        // for an RParen, we pop all tokens to (and including) the last LParen, discard the LParen,
        // and push a new SExpresson::List onto the stack.
        //
        // This is - I think - an equivalent construction:
        // LParen pushes a new Vec of expressions on the stack,
        // RParen pops the stack-top Vec and inserts it as a List into the previous frame.
        // Reading in lex order (i.e. [0][0], [0][1], [1][0]) would give the same contents as the
        // single stack;
        // this just saves us having to shuffle from the main stack to the expression stack in a way
        // that preserves the list order.

        // While we're parsing an S-expression,
        // a stack of incomplete S-expressions, by depth.
        let mut stack: Vec<Vec<SExpression>> = Vec::new();

        while let Some(TokenOffset {
            token,
            line,
            column,
        }) = tokens.next()
        {
            match token {
                Token::LParen => {
                    // Start of a new subexpression. Push it on the stack.
                    stack.push(Vec::new());
                }
                Token::Atom(v) => {
                    let atom = SExpression::Atom(v);
                    if let Some(last) = stack.last_mut() {
                        last.push(atom);
                    } else {
                        // There's nothing on the stack.
                        // This is "just" a raw atom- which is a valid SExpression.
                        return Ok(Some(atom));
                    }
                }
                Token::RParen => {
                    // Closing out an SExpression::List... if we can?
                    if let Some(contents) = stack.pop() {
                        let sexpr = SExpression::List(contents);
                        if let Some(last) = stack.last_mut() {
                            last.push(sexpr);
                        } else {
                            // This was the top-level SExpression during the evaluaton;
                            // so it's the one we want.
                            return Ok(Some(sexpr));
                        }
                    } else {
                        // An unbalanced paren!
                        // That's not just an amount-of-input error; it's a semantic error.
                        return Err(
                            ReadErr::Error(format!("parse error: encountered right paren (line {}, column {}) without matching left paren", line, column))
                        );
                    }
                }
            }
        }

        if stack.len() != 0 {
            return Err(ReadErr::Incomplete(format!(
                "parse error: got end of input within an expression of depth {}",
                stack.len(),
            )));
        }

        // Stack size is 0; implies we didn't have any input.
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::tokens::*;
    use super::*;

    #[test]
    fn tokenize_atoms() -> Result<(), ReadErr> {
        let input = "hello \"hi\" world 24601 -6";
        let output: Vec<Token> = tokenize(input)?.into_iter().map(|v| v.token).collect();

        let want = &[
            Token::Atom(Atom::Symbol("HeLlO".parse().unwrap())),
            Token::Atom(Atom::String("hi".parse().unwrap())),
            Token::Atom(Atom::Symbol("world".parse().unwrap())),
            Token::Atom(Atom::Number(LispNumber(24601))),
            Token::Atom(Atom::Number(LispNumber(-6))),
        ];

        assert_eq!(output.len(), want.len());

        for ((i, got), want) in output.iter().enumerate().zip(want.iter()) {
            assert_eq!(got, want, "unexpected token in case {}", i);
        }
        Ok(())
    }
    #[test]
    fn tokenize_parens() -> Result<(), ReadErr> {
        let input = "(1)( 2 ) (hello) ( hello (\"hi\") (( \"hi\" )))";
        let output: Vec<Token> = tokenize(input)?.into_iter().map(|v| v.token).collect();

        let want = &[
            Token::LParen,
            Token::Atom(Atom::Number(LispNumber(1))),
            Token::RParen,
            Token::LParen,
            Token::Atom(Atom::Number(LispNumber(2))),
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
    fn tokenize_unbalanced() -> Result<(), ReadErr> {
        let input = ")))()(";
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
    fn escaped_string() -> Result<(), ReadErr> {
        let input = r#"
               "hello \"sons\" \\slashdaughters a\nd others "   "#;
        let output: Vec<Token> = tokenize(input)?.into_iter().map(|v| v.token).collect();
        let trimmed = input.trim().trim_matches('"');

        assert_eq!(output.len(), 1);
        assert_eq!(
            output[0],
            Token::Atom(Atom::String(LispString(trimmed.to_owned())))
        );
        Ok(())
    }

    #[test]
    fn error_on_unexpected_stringend() {
        let input = r#"(
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
        let input = "\"hello\\\"";

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
    fn parse_several_atoms() -> ReadResult<()> {
        let input = "1 2 3";
        let want = vec![
            SExpression::Atom(Atom::Number(LispNumber(1))),
            SExpression::Atom(Atom::Number(LispNumber(2))),
            SExpression::Atom(Atom::Number(LispNumber(3))),
        ];

        let got = read(input)?;

        assert_eq!(&got, &want);
        Ok(())
    }

    #[test]
    fn parse_tree() -> ReadResult<()> {
        let input = "1 (lambda (arga **arg_b**) ( arga + **arg_b**)) (lambda \"one\" 2)";
        let want = vec![
            SExpression::Atom(Atom::Number(LispNumber(1))),
            SExpression::List(vec![
                SExpression::Atom(Atom::Symbol("lambda".parse().unwrap())),
                SExpression::List(vec![
                    Atom::Symbol("arga".parse().unwrap()).into(),
                    Atom::Symbol("**ARG_B**".parse().unwrap()).into(),
                ]),
                SExpression::List(vec![
                    Atom::Symbol("arga".parse().unwrap()).into(),
                    Atom::Symbol("+".parse().unwrap()).into(),
                    Atom::Symbol("**arg_b**".parse().unwrap()).into(),
                ]),
            ]),
            SExpression::List(vec![
                SExpression::Atom(Atom::Symbol("LAMBDA".parse().unwrap())),
                Atom::String("one".parse().unwrap()).into(),
                Atom::Number(LispNumber(2)).into(),
            ]),
        ];

        let got = read(input)?;

        assert_eq!(&got, &want);
        Ok(())
    }

    #[test]
    fn want_more_on_unbalanced() {
        let input = "(incomplete keep going";
        let got = read(input);

        match got {
            Ok(_) => panic!("expected error for input"),
            Err(ReadErr::Error(e)) => panic!(
                "got terminal error, expected incomplete error; got: {:?}",
                e
            ),
            Err(ReadErr::Incomplete(_)) => (),
        }
    }

    #[test]
    fn want_more_on_string() {
        let input = r#"( parse a string starting "here! )"#;
        let got = read(input);
        match got {
            Ok(_) => panic!("expected error for input"),
            Err(ReadErr::Error(e)) => panic!(
                "got terminal error, expected incomplete error; got: {:?}",
                e
            ),
            Err(ReadErr::Incomplete(_)) => (),
        }
    }

    #[test]
    fn multi_line_ok() -> ReadResult<()> {
        let input = r#"(
            start,
"and 
keep"
            going
        )

        "#;
        let got = read(input)?;
        let want = vec![SExpression::List(vec![
            Atom::Symbol("START,".parse().unwrap()).into(),
            Atom::String("and \nkeep".parse().unwrap()).into(),
            Atom::Symbol("going".parse().unwrap()).into(),
        ])];

        assert_eq!(&got, &want);
        Ok(())
    }
}
