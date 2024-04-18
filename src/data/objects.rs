use std::ops::Range;

use super::StoredValue;

///! Lisp object types.

/// Enum for a Lisp object.
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Object {
    Nil = Object::TAG_NIL,
    Symbol(Symbol) = Object::TAG_SYMBOL,
    Integer(Integer) = Object::TAG_INTEGER,
    Float(Float) = Object::TAG_FLOAT,
    String(LString) = Object::TAG_STRING,
    Pair(Pair) = Object::TAG_PAIR,

    // TODO:
    // - Lisp Function
    // - Builtin (primitive / form)
}

/// An ID for a stored object: a combination of pointer and type-tag.
#[derive(Clone, Copy)]
pub struct Ptr {
    combined_tag: u32,
}

impl Ptr {
    #[inline]
    pub fn is_nil(&self) -> bool {
        self.tag() == Object::TAG_NIL
    }
    #[inline]
    pub fn is_integer(&self) -> bool {
        self.tag() == Object::TAG_INTEGER
    }
    #[inline]
    pub fn is_symbol(&self) -> bool {
        self.tag() == Object::TAG_SYMBOL
    }
    #[inline]
    pub fn is_float(&self) -> bool {
        self.tag() == Object::TAG_FLOAT
    }
    #[inline]
    pub fn is_string(&self) -> bool {
        self.tag() == Object::TAG_STRING
    }
    #[inline]
    pub fn is_pair(&self) -> bool {
        self.tag() == Object::TAG_PAIR
    }



    pub fn new(idx: usize, tag: u8) -> Self {
        Ptr {
            combined_tag: ((idx as u32) << 3) | (tag as u32),
        }
    }

    #[inline]
    pub(super) fn tag(&self) -> u8 {
        (self.combined_tag & 0b111) as u8
    }

    #[inline]
    pub(super) fn idx(&self) -> usize {
        (self.combined_tag & !0b111) as usize >> 3
    }
}

impl Object {
    /// Create a nil object.
    /// Nil objects are never stored, so this can be constructed directly (for convienient consing)
    pub fn nil() -> Ptr {
        Ptr::new(0, Self::TAG_NIL)
    }

    pub(super) fn tag(&self) -> u8 {
        // From https://doc.rust-lang.org/std/mem/fn.discriminant.html:
        //
        // SAFETY: Because `Self` is marked `repr(u8)`, its layout is a `repr(C)` `union`
        // between `repr(C)` structs, each of which has the `u8` discriminant as its first
        // field, so we can read the discriminant without offsetting the pointer.
        unsafe { *<*const _>::from(self).cast::<u8>() }
    }

    const TAG_NIL: u8 = 0;
    const TAG_SYMBOL: u8 = 1;
    const TAG_INTEGER: u8 = 2;
    const TAG_FLOAT: u8 = 3;
    const TAG_STRING: u8 = 4;
    const TAG_PAIR: u8 = 5;
}

impl From<i64> for Object {
    fn from(value: i64) -> Self {
        Object::Integer(value)
    }
}

impl From<f64> for Object {
    fn from(value: f64) -> Self {
        Object::Float(value)
    }
}

impl From<Pair> for Object {
    fn from(value: Pair) -> Self {
        Object::Pair(value)
    }
}

impl From<Symbol> for Object {
    fn from(value: Symbol) -> Self {
        Object::Symbol(value)
    }
}

impl From<LString> for Object {
    fn from(value: LString) -> Self {
        Object::String(value)
    }
}

impl Into<(StoredValue, u8)> for Object {
    fn into(self) -> (StoredValue, u8) {
        match self {
            Object::Nil => (StoredValue { tombstone: 0 }, self.tag()),
            Object::Symbol(s) => (StoredValue { symbol: s }, self.tag()),
            Object::Integer(i) => (StoredValue { integer: i }, self.tag()),
            Object::Float(f) => (StoredValue { float: f }, self.tag()),
            Object::String(s) => (StoredValue { string: s }, self.tag()),
            Object::Pair(p) => (StoredValue { pair: p }, self.tag()),
        }
    }
}

impl From<(StoredValue, u8)> for Object {
    fn from((v, tag): (StoredValue, u8)) -> Self {
        match tag {
            Object::TAG_NIL => Object::Nil,
            Object::TAG_INTEGER => Object::Integer(unsafe { v.integer }),
            Object::TAG_FLOAT => Object::Float(unsafe { v.float }),
            Object::TAG_PAIR => Object::Pair(unsafe { v.pair }),
            Object::TAG_STRING => Object::String(unsafe { v.string }),
            Object::TAG_SYMBOL => Object::Symbol(unsafe { v.symbol }),
            _ => panic!("invalid tag, possible data corruption")
        }
    }
}



pub type Integer = i64;
pub type Float = f64;

impl std::fmt::Debug for Ptr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Id")
            .field("idx", &self.idx())
            .field("tag", &self.tag())
            .finish()
    }
}


#[derive(Debug, Clone, Copy)]
pub struct Pair {
    pub car: Ptr,
    pub cdr: Ptr,
}

impl Pair {
    pub fn cons(car: Ptr, cdr: Ptr) -> Self {
        Self {
            car, cdr
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Function {
    // TODO consider while building out eval; sketch:
    // Environment consists of a pair, "head of argument list" (list of symbols, need resolution),
    // and "head of lexical environment"
    // Body is a list of expressions- the SExpr tree of the body
    pub environment: Ptr,
    pub body: Ptr,
}


#[derive(Debug, Clone, Copy)]
pub struct Builtin { }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Symbol {
    pub(super) symbol: string_interner::DefaultSymbol,
}

#[derive(Debug, Clone, Copy)]
pub struct LString {
    pub offset: u32,
    pub length: u32,
}

impl LString {
    pub(super) fn range(&self) -> Range<usize> {
        let start = self.offset as usize;
        let end = (self.offset+self.length) as usize;
        start..end
    }
}
