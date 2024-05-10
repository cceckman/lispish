//! Support routines for symbol manipulation.
//!
//! TODO: Currently, this treats the symbol table as a single vector,
//! and performs a linear scan when performing string-to-symbol conversion
//! (O(n), with an O(m) comparison).
//! It would be nice to make that faster, e.g.:
//! - Keep a "tail of new symbols" with a linear scan
//! - At GC, renumber symbols in sorted order, and sort them in the list
//!   - Skip this step if the tail is empty; there are no new symbols since last GC.
//! This would keep constant-time symbol-to-string conversions,
//! but make the string-to-symbol conversion O(log n) after a GC
//! (falling back to linear beyond that.)
//!

use crate::{
    vectors::{self, compare_byte_vector_fast, read_byte_vector},
    Ptr, Storage, StoredPtr, Symbol, Tag,
};

/// The types-of-types that can be used for symbol lookup.
/// To keep memory bounded, symbol contents must be compared bytewise.
pub trait SymbolInput {
    fn get_iter(&self) -> impl '_ + Clone + Iterator<Item = char>;
}

impl SymbolInput for &str {
    fn get_iter(&self) -> impl '_ + Clone + Iterator<Item = char> {
        self.chars()
    }
}

#[derive(Clone)]
struct SymbolWriter<CharIter> {
    chars: CharIter,
    bytes: [u8; 4],
    next_byte: u8,
    last_byte: u8,
}

fn new_symbol_writer<CI: Iterator<Item = char>>(c: CI) -> impl Iterator<Item = u8> {
    // Handle uppercasing here;
    // this way we only have one layer of "iterate over chars",
    // and they're always upper.
    let chars = c.flat_map(|c| c.to_uppercase());
    SymbolWriter {
        chars,
        bytes: Default::default(),
        next_byte: 0,
        last_byte: 0,
    }
}

impl<CharIter> Iterator for SymbolWriter<CharIter>
where
    CharIter: Iterator<Item = char>,
{
    type Item = u8;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next_byte == self.last_byte {
            // Try to refill.
            let c = self.chars.next()?;
            let buf = c.encode_utf8(&mut self.bytes);
            self.next_byte = 0;
            self.last_byte = buf.len() as u8;
        }
        let b = self.bytes[self.next_byte as usize];
        self.next_byte += 1;
        Some(b)
    }
}

/// Helper routine: put a symbol into the symbol table,
/// or find it.
pub fn put(store: &Storage, symbol: impl SymbolInput) -> Ptr {
    // Stringify first, so we're comparing normalized byte vectors.
    let char_iter = symbol.get_iter();
    let byte_iter = new_symbol_writer(char_iter);
    let string = vectors::make_byte_vector(store, byte_iter);

    for (i, ptr) in store.symbols().enumerate() {
        let same = compare_byte_vector_fast(string, ptr)
            .expect("all entries in the symbol table should be well-formed bytevectors");
        if same {
            return store.bind(StoredPtr::new(i, Tag::Symbol));
        }
    }
    // Need to add. ...which means copying the whole table, eugh.
    let table = store.symbols();
    let new_idx = table.length;
    let new_items = table
        .map(|v| v.get().as_pair().unwrap())
        .chain(std::iter::once(string.get().as_pair().unwrap()));
    let new_table = store.put_vector(new_items);
    store.set_symbols(new_table);
    store.bind(StoredPtr::new(new_idx as usize, Tag::Symbol))
}

struct SymbolReader<ByteIter> {
    it: ByteIter,
    bytes: [u8; 4],
    next_byte: u8,
}

impl<ByteIter> Iterator for SymbolReader<ByteIter>
where
    ByteIter: Iterator<Item = u8>,
{
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        let s = loop {
            if let Ok(s) = core::str::from_utf8(&self.bytes[0..self.next_byte as usize]) {
                if !s.is_empty() {
                    break s;
                }
            }
            // Otherwise, read more data.
            self.bytes[self.next_byte as usize] = self.it.next()?;
            self.next_byte += 1;
        };
        let c = s.chars().next()?;
        self.next_byte = 0;
        Some(c)
    }
}

/// Get a string from a symbol.
pub fn get(symbol: Symbol) -> impl '_ + Iterator<Item = char> {
    let v = symbol.store().symbols();
    let string = v
        .offset(symbol.idx())
        .expect("All symbol pointers bound to this store should be present in the symbol table");
    let it = read_byte_vector(string)
        .expect("All symbol entries in the table should be valid byte vectors");
    SymbolReader {
        it,
        bytes: Default::default(),
        next_byte: 0,
    }
}

#[cfg(test)]
mod tests {
    use crate::Storage;

    #[test]
    fn put_symbol_retrieve_string() {
        let name = "definition";
        let store = Storage::default();

        let c = store.put_symbol(name);
        let st: String = c.get().as_symbol().unwrap().get().collect();
        // Canonical capitalization:
        assert_eq!(&st, "DEFINITION")
    }

    #[test]
    fn put_again() {
        let a = "definition";
        let b = "lambda";
        let store = Storage::default();

        let aptr = store.put_symbol(a);
        let bptr = store.put_symbol(b);
        let a2ptr = store.put_symbol(a);
        assert_eq!(aptr, a2ptr);
        assert_ne!(bptr, a2ptr);
    }

    #[test]
    fn put_across_gc() {
        let a = "definition";
        let b = "lambda";
        let mut store = Storage::default();

        let _ = store.put_symbol(a);
        let bptr = store.put_symbol(b).to_string();
        store.gc();

        let bptr = store.lookup(&bptr).unwrap();
        let st: String = bptr.get().as_symbol().unwrap().get().collect();
        assert_eq!(&st, "LAMBDA");
    }
}
