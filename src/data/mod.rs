//! Lisp data types and allocators.
//!
//! 
//! Data in lispish falls into three categories:
//! - 8B data. i64, f64. Addressed by an 8B aligned pointer, with 3b of tag.
//! - 2xPTR data: Pair, String, Symbol. This may be 8B (on 32-bit systems) or 16B (on a 64-bit system.)
//!   Since pointers are _at least_ 8B-aligned, the pointers in these structs still provides 3b of tag.
//! - Variable-length data: content for String, Symbol. Each has their own allocator, since symbols are interned (allocate-only).
//!
//! Each of these gets its own allocator. Resolving a pointer requires using the appropriate allocator,
//! to ensure the tagged pointer get associated with the appropriate provenance.

mod bitset;

use std::fmt::Debug;

use self::bitset::BitSet;


trait ObjectAllocator {
    fn store(&mut self, value: Value) -> Id;
    fn get(&self, id: Id) -> Value;
}

/// An ID for a stored object: a combination of pointer and type-tag.
#[derive(Clone, Copy)]
struct Id {
    combined_tag: u32,
}

impl Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Id")
            .field("idx", &self.idx())
            .field("tag", &self.tag())
            .finish()
    }
}

impl Id {
    pub fn new(idx: usize, tag: u8) -> Self {
        Id {
            combined_tag: ((idx as u32) << 3) | (tag as u32),
        }
    }

    #[inline]
    pub fn tag(&self) -> u8 {
        (self.combined_tag & 0b111) as u8
    }

    #[inline]
    pub fn idx(&self) -> u32 {
        self.combined_tag & !0b111
    }
}

struct Allocator {
    allocations: BitSet,
    data: Vec<StoredValue>,
}

impl ObjectAllocator for Allocator {
    fn store(&mut self, value: Value) -> Id {
        let (stored, tag) = value.into();

        let slot = self.allocations.find_first_zero();
        self.allocations.set(slot);

        if slot >= self.data.len() {
            // Resize to fit.
            const OBJECTS_PER_PAGE: usize = 4096 / std::mem::size_of::<StoredValue>();
            self.data
                .resize_with(self.data.len() + OBJECTS_PER_PAGE, || StoredValue {
                    int: 0,
                });
        }
        self.data[slot] = stored;

        Id::new(slot, tag)
    }

    fn get(&self, value: Id) -> Value {
        let tag = value.tag();
        if tag == Value::NIL_TAG {
            // The nil value does not require an allocation;
            // any Id tagged "nil" is a nil value.
            return Value::Nil;
        }

        let idx = value.idx() as usize;
        assert!(idx < self.data.len());
        (self.data[idx], tag).into()
    }
}

#[derive(Clone, Copy)]
#[repr(align(8))]
union StoredValue {
    int: Integer,
    float: Float,
    pair: Pair,
}

/// Objects are 8 bytes big. Always and forever.
const OBJECT_SIZE: usize = std::mem::align_of::<StoredValue>();

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum Value {
    Nil = Value::NIL_TAG,
    Sym(Symbol) = Value::SYM_TAG,
    Int(Integer) = Value::INT_TAG,
    Flo(Float) = Value::FLO_TAG,
    Str(LString) = Value::STR_TAG,
    Con(Pair) = Value::CON_TAG,
}

impl Value {
    fn tag(&self) -> u8 {
        // From https://doc.rust-lang.org/std/mem/fn.discriminant.html:
        //
        // SAFETY: Because `Self` is marked `repr(u8)`, its layout is a `repr(C)` `union`
        // between `repr(C)` structs, each of which has the `u8` discriminant as its first
        // field, so we can read the discriminant without offsetting the pointer.
        unsafe { *<*const _>::from(self).cast::<u8>() }
    }

    const NIL_TAG: u8 = 0;
    const SYM_TAG: u8 = 1;
    const INT_TAG: u8 = 2;
    const FLO_TAG: u8 = 3;
    const STR_TAG: u8 = 4;
    const CON_TAG: u8 = 5;
}

impl Into<(StoredValue, u8)> for Value {
    fn into(self) -> (StoredValue, u8) {
        match self {
            Value::Nil => (StoredValue { int: 0 }, self.tag()),
            Value::Sym(_) => todo!(),
            Value::Int(i) => (StoredValue { int: i }, self.tag()),
            Value::Flo(f) => (StoredValue { float: f }, self.tag()),
            Value::Str(_) => todo!(),
            Value::Con(p) => (StoredValue { pair: p }, self.tag()),
        }
    }
}

impl From<(StoredValue, u8)> for Value {
    fn from((v, tag): (StoredValue, u8)) -> Self {
        match tag {
            Value::NIL_TAG => Value::Nil,
            Value::INT_TAG => Value::Int(unsafe { v.int }),
            Value::FLO_TAG => Value::Flo(unsafe { v.float }),
            Value::CON_TAG => Value::Con(unsafe { v.pair }),
            _ => todo!(),
        }
    }
}

pub type Integer = i64;
pub type Float = f64;

#[derive(Debug, Clone, Copy)]
pub struct LString {}

#[derive(Debug, Clone, Copy)]
pub struct Pair {
    car: Id,
    cdr: Id,
}

#[derive(Debug, Clone, Copy)]
pub struct Symbol {}
