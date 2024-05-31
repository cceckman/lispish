use super::{Bind, Storage, StoredPair, StoredPtr, StoredValue, Tag};
use crate::{symbols, StoredVector};
use core::fmt::{Debug, Display, Write};

/// Enum for a Lisp object.
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Object<'a> {
    Nil = Tag::Nil as u8,
    Integer(Integer) = Tag::Integer as u8,
    Float(Float) = Tag::Float as u8,
    Symbol(Symbol<'a>) = Tag::Symbol as u8,
    Pair(Pair<'a>) = Tag::Pair as u8,
    Bytes(Bytes) = Tag::Bytes as u8,
    Vector(Vector<'a>) = Tag::Vector as u8,
}

/// An ID for a stored object: a combination of pointer and type-tag.
#[derive(Clone, Copy)]
pub struct Ptr<'a> {
    pub(super) raw: StoredPtr,
    // Nil pointers can be unassociated with a store;
    // this permits the default constructor.
    store: Option<&'a Storage>,
}

impl PartialEq for Ptr<'_> {
    fn eq(&self, other: &Self) -> bool {
        let raw = self.raw == other.raw;
        raw && match (self.store, other.store) {
            (Some(a), Some(b)) => core::ptr::eq(a, b),
            (None, None) => true,
            _ => false,
        }
    }
}

impl Eq for Ptr<'_> {}

impl Display for Ptr<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Display::fmt(&self.raw, f)
    }
}

impl<'a> Ptr<'a> {
    pub fn get(&self) -> Object<'a> {
        if let Some(store) = self.store {
            let p = *self;
            store.get(p)
        } else {
            assert!(self.is_nil());
            Object::Nil
        }
    }
}

impl core::fmt::Display for Object<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Object::Nil => write!(f, "nil"),
            Object::Integer(i) => write!(f, "{}", i),
            Object::Float(i) => write!(f, "{}", i),
            Object::Symbol(j) => {
                for c in j.get() {
                    f.write_char(c)?
                }
                Ok(())
            }
            Object::Pair(Pair { car, cdr }) => write!(f, "({car}, {cdr})"),
            Object::Bytes(b) => write!(f, "0x{b:02x?}"),
            Object::Vector(b) => {
                f.write_char('[')?;
                // As with Pair, we don't display the objects themselves, just the
                // pointers. A vector may contain itself!
                let l = (b.length - 1) as usize;
                for (i, ptr) in b.enumerate() {
                    write!(f, "{ptr}")?;
                    if i != l {
                        write!(f, ", ")?;
                    }
                }
                f.write_char(']')
            }
        }
    }
}

impl Ptr<'_> {
    pub fn nil<'a>() -> Ptr<'a> {
        Default::default()
    }

    #[inline]
    pub fn is_nil(&self) -> bool {
        self.raw.is_nil()
    }
    #[inline]
    pub fn is_integer(&self) -> bool {
        self.raw.is_integer()
    }
    #[inline]
    pub fn is_float(&self) -> bool {
        self.raw.is_float()
    }
    #[inline]
    pub fn is_symbol(&self) -> bool {
        self.raw.is_symbol()
    }
    #[inline]
    pub fn is_pair(&self) -> bool {
        self.raw.is_pair()
    }
    #[inline]
    pub fn is_vector(&self) -> bool {
        self.raw.is_vector()
    }

    #[inline]
    pub(super) fn tag(&self) -> Tag {
        self.raw.tag()
    }

    #[inline]
    pub(super) fn idx(&self) -> usize {
        self.raw.idx()
    }
}

impl Default for Ptr<'_> {
    fn default() -> Self {
        Ptr {
            raw: StoredPtr { combined_tag: 0 },
            store: None,
        }
    }
}

impl<'a> Object<'a> {
    /// Create a nil object.
    /// Nil objects are never stored, so this can be constructed directly (for convienient consing)
    pub fn nil() -> Ptr<'static> {
        Ptr::default()
    }

    pub(super) fn tag(&self) -> Tag {
        // From https://doc.rust-lang.org/std/mem/fn.discriminant.html:
        //
        // SAFETY: Because `Self` is marked `repr(u8)`, its layout is a `repr(C)` `union`
        // between `repr(C)` structs, each of which has the `u8` discriminant as its first
        // field, so we can read the discriminant without offsetting the pointer.
        unsafe { *<*const _>::from(self).cast::<u8>() }.into()
    }

    pub fn as_integer(&self) -> Option<Integer> {
        match self {
            Object::Integer(p) => Some(*p),
            _ => None,
        }
    }

    pub fn as_float(&self) -> Option<Float> {
        match self {
            Object::Float(p) => Some(*p),
            _ => None,
        }
    }

    pub fn as_symbol(&self) -> Option<Symbol> {
        match self {
            Object::Symbol(p) => Some(*p),
            _ => None,
        }
    }

    pub fn as_pair(&self) -> Option<Pair<'a>> {
        match self {
            Object::Pair(p) => Some(*p),
            _ => None,
        }
    }

    pub fn as_bytes(&self) -> Option<Bytes> {
        match self {
            Object::Bytes(p) => Some(*p),
            _ => None,
        }
    }

    pub fn as_vector(&self) -> Option<Vector<'a>> {
        match self {
            Object::Vector(p) => Some(*p),
            _ => None,
        }
    }
}

impl From<i64> for Object<'_> {
    fn from(value: i64) -> Self {
        Object::Integer(value)
    }
}

impl From<f64> for Object<'_> {
    fn from(value: f64) -> Self {
        Object::Float(value)
    }
}

impl From<Bytes> for Object<'_> {
    fn from(value: Bytes) -> Self {
        Object::Bytes(value)
    }
}

impl<'a> From<Pair<'a>> for Object<'a> {
    fn from(value: Pair<'a>) -> Self {
        Object::Pair(value)
    }
}

impl<'a> From<Symbol<'a>> for Object<'a> {
    fn from(value: Symbol<'a>) -> Self {
        Object::Symbol(value)
    }
}

impl<'a> TryInto<Pair<'a>> for Object<'a> {
    type Error = &'static str;

    fn try_into(self) -> Result<Pair<'a>, Self::Error> {
        match self {
            Object::Pair(p) => Ok(p),
            _ => Err("object is not a pair"),
        }
    }
}

impl From<Object<'_>> for (StoredValue, Tag) {
    fn from(object: Object<'_>) -> Self {
        match object {
            Object::Nil => unreachable!("Do not serialize nil"),
            Object::Symbol(_) => unreachable!("Symbols are interned, not stored"),
            Object::Integer(i) => (StoredValue { integer: i }, object.tag()),
            Object::Float(f) => (StoredValue { float: f }, object.tag()),
            Object::Bytes(b) => (StoredValue { bytes: b }, object.tag()),
            Object::Pair(p) => (
                StoredValue {
                    pair: StoredPair {
                        car: p.car.raw,
                        cdr: p.cdr.raw,
                    },
                },
                object.tag(),
            ),
            Object::Vector(v) => (
                StoredValue {
                    vector: StoredVector {
                        length: v.length,
                        start: v.start.raw,
                    },
                },
                object.tag(),
            ),
        }
    }
}

impl<'a> Bind<'a> for Object<'a> {
    type Free = (StoredPtr, StoredValue);

    fn bind(store: &'a Storage, free: Self::Free) -> Self {
        let (p, v) = free;

        match p.tag() {
            Tag::Nil => Object::Nil,
            Tag::Integer => Object::Integer(unsafe { v.integer }),
            Tag::Float => Object::Float(unsafe { v.float }),
            Tag::Bytes => Object::Bytes(unsafe { v.bytes }),
            Tag::Symbol => Object::Symbol(Symbol::bind(store, p.idx())),
            Tag::Pair => Object::Pair({
                let p = unsafe { v.pair };
                Pair {
                    car: Ptr::bind(store, p.car),
                    cdr: Ptr::bind(store, p.cdr),
                }
            }),
            Tag::Vector => Object::Vector({
                let v = unsafe { v.vector };
                Vector {
                    length: v.length,
                    start: Ptr::bind(store, v.start),
                }
            }),
        }
    }
}

pub type Integer = i64;
pub type Float = f64;
pub type Bytes = [u8; 8];

impl core::fmt::Debug for Ptr<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Id")
            .field("idx", &self.idx())
            .field("tag", &self.tag())
            .finish()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Pair<'a> {
    pub car: Ptr<'a>,
    pub cdr: Ptr<'a>,
}

impl<'a> Pair<'a> {
    pub fn cons(car: Ptr<'a>, cdr: Ptr<'a>) -> Self {
        Self { car, cdr }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Vector<'a> {
    pub length: u32,
    pub start: Ptr<'a>,
}

impl<'a> Vector<'a> {
    pub fn offset(&self, idx: usize) -> Option<Ptr<'a>> {
        if (idx as u32) < self.length {
            Some(Ptr {
                raw: StoredPtr::new(self.start.idx() + idx, self.start.tag()),
                store: self.start.store,
            })
        } else {
            None
        }
    }
}

impl<'a> Iterator for Vector<'a> {
    type Item = Ptr<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.length > 0 {
            let result = Some(self.start);
            self.length -= 1;
            self.start = Ptr {
                raw: StoredPtr::new(self.start.idx() + 1, self.start.tag()),
                store: self.start.store,
            };
            result
        } else {
            None
        }
    }
}

impl<'a> Bind<'a> for Vector<'a> {
    type Free = StoredVector;

    fn bind(store: &'a Storage, raw: Self::Free) -> Self {
        Self {
            length: raw.length,
            start: store.bind(raw.start),
        }
    }
}

#[derive(Clone, Copy)]
pub struct Symbol<'a> {
    /// Symbols are represented by their index in the symbol table.
    idx: usize,
    store: &'a Storage,
}

impl Symbol<'_> {
    pub fn idx(&self) -> usize {
        self.idx
    }
}

impl<'a> Symbol<'a> {
    pub(super) fn store(&self) -> &'a Storage {
        self.store
    }

    pub fn get(self) -> impl 'a + Iterator<Item = char> {
        symbols::get(self)
    }
}

impl core::fmt::Debug for Symbol<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.idx)
    }
}

impl PartialEq for Symbol<'_> {
    fn eq(&self, other: &Self) -> bool {
        let idx_eq = self.idx == other.idx;
        idx_eq && core::ptr::eq(self.store, other.store)
    }
}

impl Eq for Symbol<'_> {}

impl<'a> Bind<'a> for Symbol<'a> {
    type Free = usize;

    fn bind(store: &'a Storage, raw: Self::Free) -> Self {
        Self { idx: raw, store }
    }
}

impl<'a> Bind<'a> for Ptr<'a> {
    type Free = StoredPtr;

    fn bind(store: &'a Storage, raw: Self::Free) -> Self {
        Self {
            raw,
            store: if raw.is_nil() { None } else { Some(store) },
        }
    }
}

impl<'a> Bind<'a> for Pair<'a> {
    type Free = StoredPair;

    fn bind(store: &'a Storage, raw: Self::Free) -> Self {
        Self {
            car: Ptr::bind(store, raw.car),
            cdr: Ptr::bind(store, raw.cdr),
        }
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use crate::{Pair, Ptr, Storage};

    #[test]
    fn display_int() {
        let store = Storage::default();
        let v = store.put(10);
        assert_eq!(v.get().to_string(), "10");
    }

    #[test]
    fn display_float() {
        let store = Storage::default();
        let v = store.put(10.2);
        assert_eq!(v.get().to_string(), "10.2");
    }

    #[test]
    fn display_symbol() {
        let store = Storage::default();
        let v = store.put_symbol("hello");
        // Symbols are canonicalized to uppercase:
        assert_eq!(v.get().to_string(), "HELLO");
    }

    #[test]
    fn display_pair() {
        let store = Storage::default();
        let one = store.put(1);
        let two = store.put(2);
        let v = store.put(Pair::cons(one, two));
        // Symbols are canonicalized to uppercase:
        assert_eq!(v.get().to_string(), format!("({}, {})", one, two));
    }

    #[test]
    fn display_bytes() {
        let store = Storage::default();
        let v = store.put([1, 2, 3, 4, 0xa, 0xb, 0xc, 0xd]);
        // Symbols are canonicalized to uppercase:
        assert_eq!(v.get().to_string(), "0x[01, 02, 03, 04, 0a, 0b, 0c, 0d]",);
    }

    #[test]
    fn display_vector() {
        let store = Storage::default();
        let vp = store.put_vector([1i64, 2].into_iter());
        let vo = vp.get();
        let v = vo.as_vector().unwrap();
        let p0 = v.offset(0).unwrap();
        let p1 = v.offset(1).unwrap();
        // Symbols are canonicalized to uppercase:
        assert_eq!(vo.to_string(), format!("[{}, {}]", p0, p1));
    }

    #[test]
    fn display_nil() {
        let vo = Ptr::nil().get();
        // Symbols are canonicalized to uppercase:
        assert_eq!(vo.to_string(), "nil");
    }
}
