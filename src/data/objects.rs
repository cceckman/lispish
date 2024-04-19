use std::{marker::PhantomData, ops::Range};

use crate::eval::Builtin;

use super::{Bind, Storage, StoredPair, StoredPtr, StoredString, StoredValue};

///! Lisp object types.

/// Enum for a Lisp object.
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Object<'a> {
    Nil = StoredPtr::TAG_NIL,
    Integer(Integer) = StoredPtr::TAG_INTEGER,
    Float(Float) = StoredPtr::TAG_FLOAT,
    String(LString<'a>) = StoredPtr::TAG_STRING,
    Symbol(Symbol) = StoredPtr::TAG_SYMBOL,
    Pair(Pair<'a>) = StoredPtr::TAG_PAIR,

    Builtin(Builtin) = StoredPtr::TAG_BUILTIN,
    // TODO:
    // - Lisp Function
    // - Builtin (primitive / form)
}

/// An ID for a stored object: a combination of pointer and type-tag.
#[derive(Clone, Copy)]
pub struct Ptr<'a> {
    pub(super) raw: StoredPtr,
    store: PhantomData<&'a Storage>,
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
    pub fn is_string(&self) -> bool {
        self.raw.is_string()
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
    pub fn is_builtin(&self) -> bool {
        self.raw.is_builtin()
    }

    #[inline]
    pub(super) fn tag(&self) -> u8 {
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

    pub(super) fn tag(&self) -> u8 {
        // From https://doc.rust-lang.org/std/mem/fn.discriminant.html:
        //
        // SAFETY: Because `Self` is marked `repr(u8)`, its layout is a `repr(C)` `union`
        // between `repr(C)` structs, each of which has the `u8` discriminant as its first
        // field, so we can read the discriminant without offsetting the pointer.
        unsafe { *<*const _>::from(self).cast::<u8>() }
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

impl<'a> From<LString<'a>> for Object<'a> {
    fn from(value: LString<'a>) -> Self {
        Object::String(value)
    }
}

impl Into<(StoredValue, u8)> for Object<'_> {
    fn into(self) -> (StoredValue, u8) {
        match self {
            Object::Nil => (StoredValue { tombstone: 0 }, self.tag()),
            Object::Symbol(s) => (StoredValue { symbol: s }, self.tag()),
            Object::Integer(i) => (StoredValue { integer: i }, self.tag()),
            Object::Float(f) => (StoredValue { float: f }, self.tag()),
            Object::String(s) => (StoredValue { string: s.raw }, self.tag()),
            Object::Pair(p) => (
                StoredValue {
                    pair: StoredPair {
                        car: p.car.raw,
                        cdr: p.cdr.raw,
                    },
                },
                self.tag(),
            ),
            Object::Builtin(f) => (StoredValue { builtin: f }, self.tag()),
        }
    }
}

impl<'a> Object<'a> {
    pub(super) fn new(p: Ptr<'a>, v: StoredValue) -> Self {
        match p.tag() {
            StoredPtr::TAG_NIL => Object::Nil,
            StoredPtr::TAG_INTEGER => Object::Integer(unsafe { v.integer }),
            StoredPtr::TAG_FLOAT => Object::Float(unsafe { v.float }),
            StoredPtr::TAG_PAIR => Object::Pair({
                let raw = unsafe { v.pair };
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
            }),
            StoredPtr::TAG_STRING => Object::String({
                let raw = unsafe { v.string };
                LString {
                    raw,
                    store: p.store,
                }
            }),
            StoredPtr::TAG_SYMBOL => Object::Symbol(unsafe { v.symbol }),
            StoredPtr::TAG_BUILTIN => Object::Builtin(unsafe { v.builtin }),
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
pub struct Symbol {
    pub(super) symbol: string_interner::DefaultSymbol,
}

#[derive(Debug, Clone, Copy)]
pub struct LString<'a> {
    raw: StoredString,
    store: PhantomData<&'a Storage>,
}

impl LString<'_> {
    pub fn len(&self) -> u32 {
        self.raw.length
    }

    pub(super) fn range(&self) -> Range<usize> {
        self.raw.range()
    }
}

impl<'a> Bind<'a> for LString<'a> {
    type Free = StoredString;

    fn bind(_store: &'a Storage, raw: Self::Free) -> Self {
        Self {
            raw,
            store: PhantomData,
        }
    }
}

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
