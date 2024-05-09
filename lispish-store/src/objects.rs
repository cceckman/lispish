use std::marker::PhantomData;

use string_interner::{DefaultSymbol, Symbol as InternerSymbol};

use crate::StoredVector;

use super::{Bind, Storage, StoredPair, StoredPtr, StoredValue, Tag};

/// Enum for a Lisp object.
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Object<'a> {
    Nil = Tag::Nil as u8,
    Integer(Integer) = Tag::Integer as u8,
    Float(Float) = Tag::Float as u8,
    Symbol(Symbol) = Tag::Symbol as u8,
    Pair(Pair<'a>) = Tag::Pair as u8,
    Bytes(Bytes) = Tag::Bytes as u8,
    Vector(Vector<'a>) = Tag::Vector as u8,
}

/// An ID for a stored object: a combination of pointer and type-tag.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Ptr<'a> {
    pub(super) raw: StoredPtr,
    store: PhantomData<&'a Storage>,
}

impl std::fmt::Display for Ptr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.raw.fmt(f)
    }
}

impl std::fmt::Display for StoredPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tag = match self.tag() {
            Tag::Nil => "nil",
            Tag::Integer => "i64",
            Tag::Float => "f64",
            Tag::Symbol => "sym",
            Tag::Pair => "obj",
            Tag::Bytes => "byt",
            Tag::Vector => "vec",
            Tag::String => "str",
        };
        write!(f, "{}#{}", tag, self.idx())
    }
}

impl std::str::FromStr for StoredPtr {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some((tag, number)) = s.split_once('#') {
            let tag = match tag {
                "nil" => Tag::Nil,
                "i64" => Tag::Integer,
                "f64" => Tag::Float,
                "sym" => Tag::Symbol,
                "obj" => Tag::Pair,
                "vec" => Tag::Vector,
                "byt" => Tag::Bytes,
                "str" => Tag::String,
                _ => return Err(format!("invalid tag {}", tag)),
            };
            let idx: usize = number
                .parse()
                .map_err(|e| format!("invalid index: {}", e))?;
            Ok(StoredPtr::new(idx, tag))
        } else {
            Err(format!("invalid pointer {}", s))
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
            store: PhantomData,
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

impl From<Symbol> for Object<'_> {
    fn from(value: Symbol) -> Self {
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
            Tag::Symbol => Object::Symbol(Symbol(DefaultSymbol::try_from_usize(p.idx()).unwrap())),
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
            _ => todo!(),
        }
    }
}

pub type Integer = i64;
pub type Float = f64;
pub type Bytes = [u8; 8];

impl std::fmt::Debug for Ptr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

impl<'a> Bind<'a> for Vector<'a> {
    type Free = StoredVector;

    fn bind(store: &'a Storage, raw: Self::Free) -> Self {
        Self {
            length: raw.length,
            start: store.bind(raw.start),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Symbol(pub DefaultSymbol);

impl<'a> Bind<'a> for Ptr<'a> {
    type Free = StoredPtr;

    fn bind(_store: &'a Storage, raw: Self::Free) -> Self {
        Self {
            raw,
            store: PhantomData,
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
