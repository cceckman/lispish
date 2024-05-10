//! Additional routinames for manipulating vectors.
//!

use std::fmt::Debug;

use crate::{Bytes, Pair, Ptr, Storage, Tag, Vector};

pub struct Error<'a> {
    message: &'static str,
    ptr: Ptr<'a>,
}

impl<'a> Error<'a> {
    const fn new(format: &'static str, ptr: Ptr<'a>) -> Self {
        Error {
            message: format,
            ptr,
        }
    }
}

impl Debug for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "for object {}: {}", self.ptr, self.message)
    }
}

impl std::fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "for object {}: {}", self.ptr, self.message)
    }
}

/// A converter from iterator-over-bytes to iterator-over-chunks.
#[derive(Clone)]
struct BytesToChunks<I> {
    it: I,
}

impl<I> Iterator for BytesToChunks<I>
where
    I: Iterator<Item = u8>,
{
    // The last chunk returned may be incomplete.
    type Item = (usize, Bytes);

    fn next(&mut self) -> Option<Self::Item> {
        let mut next = [0u8; 8];
        let mut count = 0;
        for i in 0..8 {
            if let Some(b) = self.it.next() {
                next[count] = b;
                count = i + 1;
            } else {
                break;
            }
        }
        if count > 0 {
            Some((count, next))
        } else {
            None
        }
    }
}

/// Compare two byte-vectors for equality.
///
/// NOTE: This does not run in constant time.
/// This is good for string comparisons, bad for cryptography.
pub fn compare_byte_vector_fast<'a>(a: Ptr<'a>, b: Ptr<'a>) -> Result<bool, Error<'a>> {
    let a = read_byte_vector(a)?;
    let b = read_byte_vector(b)?;
    Ok(|| -> bool {
        if a.max != b.max {
            // Length mismatch
            return false;
        }
        for (a, b) in a.zip(b) {
            if a != b {
                return false;
            }
        }
        true
    }())
}

/// A byte-vector consists of a pair: (length in bytes, vector of 8B chunks).
///
/// This is also used for strings.
pub fn make_byte_vector(store: &Storage, bytes: impl IntoIterator<Item = u8>) -> Ptr {
    let mut len = 0i64;

    let it = BytesToChunks {
        it: bytes.into_iter(),
    }
    .map(|(l, bytes)| {
        len += l as i64;
        bytes
    });
    let vptr = store.put_vector(it);
    let length = store.put(len);
    store.put(Pair::cons(length, vptr))
}

#[derive(Clone)]
pub struct ByteVectorReader<'a> {
    vector: Vector<'a>,
    buffer: [u8; 8],
    consumed: i64,
    max: i64,
}

impl<'a> Iterator for ByteVectorReader<'a> {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.consumed == self.max {
            return None;
        }
        let idx: usize = (self.consumed % 8) as usize;
        if idx == 0 {
            // Refill the local buffer, advance the chunk pointer.
            let b = self.vector.next()?;
            // We checked the object type at construction,
            // so we won't really early-return here.
            self.buffer = b.get().as_bytes()?;
        }
        let byte = self.buffer[idx];
        self.consumed += 1;
        Some(byte)
    }
}

/// Read a byte-vector / string.
pub fn read_byte_vector(byte_vector: Ptr) -> Result<ByteVectorReader, Error> {
    let Pair {
        car: lptr,
        cdr: vptr,
    } = byte_vector
        .get()
        .as_pair()
        .ok_or(Error::new("bytevector head is not a pair", byte_vector))?;
    let len = lptr.get().as_integer().ok_or(Error::new(
        "bytevector length is not an integer",
        byte_vector,
    ))?;
    let vector = vptr.get().as_vector().ok_or(Error::new(
        "bytevector contents are not a vector",
        byte_vector,
    ))?;
    if vector.start.tag() != Tag::Bytes {
        Err(Error::new("bytevector contents are not bytes", byte_vector))?;
    }

    Ok(ByteVectorReader {
        vector,
        buffer: Default::default(),
        consumed: 0,
        max: len,
    })
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::*;

    #[test]
    fn store_bytes() {
        const S: &[u8] = b"Hello everybody! I'm so happy to see you";

        let store = Storage::default();
        let p = make_byte_vector(&store, S.iter().cloned());
        let Pair {
            car: lptr,
            cdr: vptr,
        } = p.get().as_pair().unwrap();
        let got_len = lptr.get().as_integer().unwrap();
        assert_eq!(got_len, S.len() as i64);

        let Vector { start, .. } = vptr.get().as_vector().unwrap();
        let data = start.get().as_bytes().unwrap();
        assert_eq!(&data, &S[0..8]);
    }

    #[test]
    fn reproduce_bytes() {
        const S: &[u8] = b"Hello everybody! I'm so happy to see you";

        let store = Storage::default();
        let p = make_byte_vector(&store, S.iter().cloned());
        let got: Vec<u8> = read_byte_vector(p).unwrap().collect();
        assert_eq!(&got, S);
    }
}
