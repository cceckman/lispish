use std::io::{stdout, Read, Write};

use lispish::{data::Storage, parse_body, render_store};

/// Reads a Lisp file on input, renders it as Graphviz.
pub fn main() -> std::io::Result<()> {
    let mut input: Vec<u8> = Default::default();
    std::io::stdin().read_to_end(&mut input)?;
    let s: Storage = Default::default();
    s.set_root(parse_body(&s, &input)?);
    let out = render_store(&s, []);
    stdout().write_all(&out)
}
