//! Support for reading LISP expressions from strings.

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

impl ReadErr {
    /// Add additional context to an error.
    pub fn annotate(self, more: impl AsRef<str>) -> Self {
        match self {
            ReadErr::Error(e) => ReadErr::Error(format!("{}: {}", more.as_ref(), e)),
            ReadErr::Incomplete(e) => ReadErr::Incomplete(format!("{}: {}", more.as_ref(), e)),
        }

    }
}

/// The main result type for this module:
/// a T (token, expression, etc), or an error, or incomplete.
pub type ReadResult<T> = Result<T, ReadErr>;


mod token;

/// Attempt to read the provided input as an SExpression.
///
/// A result of Incomplete indicates that the provided input may become complete if
/// more input is provided. The associated string gives an indication as to what is expected.
/// If parsing dynamic input (e.g. stdin), the user may wish to wait for more input;
/// if parsing state input (e.g. a file), Incomplete may be treated as a read error.
pub fn read(input: &str) -> ReadResult<()> {
    // I'd like to `impl Try for ReadResult` but that's not stable yet.
    _ = token::tokenize(input)?;

    todo!();
}

/*mod parse {
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
}*/

/*
#[cfg(test)]
mod tests {
    use super::*;

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
}*/