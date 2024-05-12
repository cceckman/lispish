//! Support routines for dealing with strings.

#[derive(Clone)]
struct CharToBytes<CharIter> {
    chars: CharIter,
    bytes: [u8; 4],
    next_byte: u8,
    last_byte: u8,
}

/// Convert an iterator-over-chars into an iterator-over-bytes.
pub fn to_bytes<CI: Iterator<Item = char>>(chars: CI) -> impl Iterator<Item = u8> {
    // Handle uppercasing here;
    // this way we only have one layer of "iterate over chars",
    // and they're always upper.
    CharToBytes {
        chars,
        bytes: Default::default(),
        next_byte: 0,
        last_byte: 0,
    }
}

/// Pipeline: convert to uppercase, then to bytes.
pub fn to_upper_bytes<CI: Iterator<Item = char>>(c: CI) -> impl Iterator<Item = u8> {
    // Handle uppercasing here;
    // this way we only have one layer of "iterate over chars",
    // and they're always upper.
    let chars = c.flat_map(|c| c.to_uppercase());
    CharToBytes {
        chars,
        bytes: Default::default(),
        next_byte: 0,
        last_byte: 0,
    }
}

impl<CharIter> Iterator for CharToBytes<CharIter>
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

/// Convert an iterator-over-bytes to an iterator-over-characters
pub fn to_chars(b: impl Iterator<Item = u8>) -> impl Iterator<Item = char> {
    StringReader {
        it: b,
        bytes: Default::default(),
        next_byte: 0,
    }
}

struct StringReader<ByteIter> {
    it: ByteIter,
    bytes: [u8; 4],
    next_byte: u8,
}

impl<ByteIter> Iterator for StringReader<ByteIter>
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
