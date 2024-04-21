//! Basic Lisp parser (and eventually evaluator) at RC.
//!

use std::io::{BufRead, Write};

use data::{Pair, Storage};
use eval::{create_env_stack, eval};
use reader::ReadErr;

pub mod reader;

pub mod data;

mod eval;

/// Runs a read-evaluate-print loop,
/// and returns an exit code on success.
pub fn repl(
    program_input: &mut impl BufRead,
    eval_input: &mut impl BufRead,
    stdout: &mut impl Write,
    stderr: &mut impl Write,
) -> std::io::Result<i32> {
    let mut store = Storage::default();
    store.set_root(create_env_stack(&store));
    let mut gc_flag = false;

    let mut input_buffer = String::new();
    loop {
        // We're honest here: we only offer the prompt after we're done with GC.
        if gc_flag {
            store.gc();
            gc_flag = false;
        }

        // Offer a prompt:
        if input_buffer.is_empty() {
            stderr.write("=> ".as_bytes())?;
            stderr.flush()?;
        }

        // Try to parse the input buffer so far.
        //
        // TODO: This approach only attempts to parse at \n, which is not necessarily what we want.
        // The Best option would be to have stacked iterators:
        // - an iterator over bytes (looking for terminating bytes: whitespace or close-paren)
        // - an iterator over tokens
        // - an iterator over expressions
        // But we're not there yet.
        match program_input.read_line(&mut input_buffer)? {
            0 => {
                stderr.write("End of input.\nNolite te Bastardes Carborundorum.\n".as_bytes())?;
                stderr.flush()?;
                return Ok(0);
            }
            _ => (),
        }

        let tokens = match reader::tokenize(&input_buffer) {
            Ok(t) => t,
            Err(ReadErr::Incomplete(s)) => {
                tracing::trace!("incomplete tokenization: {}", s);
                continue;
            }
            Err(ReadErr::Error(e)) => {
                tracing::error!("error in tokenizing: {}", e);
                writeln!(stderr, "error in tokenizing: {}", e)?;
                stderr.flush()?;
                // The input buffer is bad; discard it.
                input_buffer.clear();
                continue;
            }
        };
        // We're going to start evaluating.
        // Perform a GC afterwards, so we clean up any residual objects from failed (or successful) parsing.
        gc_flag = true;

        let body = match reader::parse(&store, tokens.into_iter()) {
            Ok(body) => body,
            Err(ReadErr::Incomplete(s)) => {
                tracing::trace!("incomplete parse: {}", s);
                continue;
            }
            Err(ReadErr::Error(e)) => {
                tracing::error!("error in parsing: {}", e);
                writeln!(stderr, "error in parsing: {}", e)?;
                stderr.flush()?;
                // The input buffer is bad; discard it.
                // We'll also discard the body (via GC).
                input_buffer.clear();
                continue;
            }
        };

        // We've parsed successfully. We're going to run this input- discard it.
        input_buffer.clear();

        // We have a body! Evaluate it.
        store.set_root(store.put(Pair::cons(body, store.root())));
        // TODO pretty-print errors, have an error enum, etc etc.
        eval(&mut store, eval_input, stdout, stderr).unwrap();
    }
}
