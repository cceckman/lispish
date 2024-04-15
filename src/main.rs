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

use std::io::Read;

fn main() {
    let mut input = std::io::stdin().lock();
    let mut bytes = Vec::new();
    input
        .read_to_end(&mut bytes)
        .expect("error: could not read input");
    let s: String = String::from_utf8(bytes).expect("error: input is not UTF-8");
    let _ = lispish::reader::read(&s);
}
