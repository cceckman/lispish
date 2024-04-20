//! Render an unevaluated Lisp tree into:
//! - Lisp on stdout, i.e. a mirror of the input
//! - Debug on stderr - the internal representation from the `lispish` crate.
//!
//! The debug format is given by the defaults of the `derive(Debug)` macro in Rust.
//!
//!
//! ```ignore
//! <input.lisp lisp_to_debug
//! ```

use std::io::Cursor;

fn main() {
    let mut stdin = std::io::stdin().lock();
    let mut stdout = std::io::stdout().lock();
    let mut stderr = std::io::stderr().lock();

    lispish::repl(
        &mut stdin,
        &mut Cursor::new(&[0u8]),
        &mut stdout,
        &mut stderr,
    )
    .expect("unexpected error");
}
