use std::marker::PhantomData;

use string_interner::{DefaultSymbol, Symbol as InternerSymbol};

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
            _ => "???",
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

impl Object<'_> {
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
            Object::Pair(p) => (
                StoredValue {
                    pair: StoredPair {
                        car: p.car.raw,
                        cdr: p.cdr.raw,
                    },
                },
                object.tag(),
            ),
        }
    }
}

impl<'a> Object<'a> {
    pub(super) fn new(p: Ptr<'a>, v: StoredValue) -> Self {
        let bind = |raw: StoredPair| -> Pair<'a> {
            Pair {
                car: Ptr {
                    raw: raw.car,
                    store: p.store,
                },
                cdr: Ptr {
                    raw: raw.cdr,
                    store: p.store,
                },
            }
        };

        match p.tag() {
            Tag::Nil => Object::Nil,
            Tag::Integer => Object::Integer(unsafe { v.integer }),
            Tag::Float => Object::Float(unsafe { v.float }),
            Tag::Symbol => Object::Symbol(Symbol(DefaultSymbol::try_from_usize(p.idx()).unwrap())),
            Tag::Pair => Object::Pair(bind(unsafe { v.pair })),
            _ => panic!("invalid tag, possible data corruption"),
        }
    }
}

pub type Integer = i64;
pub type Float = f64;

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