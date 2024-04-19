//! Lisp data types and allocators.
//!
//!
//! The main data types of Lisp use a fixed-size arena allocator:
//! - i64, f64 primitives
//! - Pair, String, Symbol tuples (two pointers / offset+length)
//!
//! The arenas can grow (backed by Vec) but not shrink piecewise.
//! They shrink during garbage collection:
//! 1.  Create a new arena (based on current size times a load factor)
//! 2.  Walk from roots (environment) to all live objects
//!     - Keep a bitmask of all visited objects.
//!     - Copy all live objects into the new arena on first visit
//!     - ...and replace with a tombstone, pointing to the new-arena location.
//! 3.  Walk again, replacing environment and heap pointers with tombstones.
//!
//!  
//! Variable-sized data (string and symbol) use their own allocators.
//! -   Symbols are interned, and perpetual.
//!     The returned symbol
//! -   String _objects_ provide ownership semantics over string _ranges_.
//!     Strings use a ~typical allocator, with sizes rounded up to the nearest 8B.
//!

mod bitset;

use std::{
    cell::{Ref, RefCell},
    cmp::max,
    collections::VecDeque,
    ops::Range,
};
mod objects;
pub use objects::*;

use self::bitset::BitSet;

/// Storage allows representing all persistent objects.
#[derive(Default)]
pub struct Storage {
    generation: RefCell<Generation>,

    roots: RefCell<Vec<StoredPtr>>,

    high_water: StorageStats,
}

/// Runs a GC on the given storage and roots. This has the logical signature:
///
/// ```
/// # use lispish::data::Storage;
/// # use lispish::data::Ptr;
/// # use std::iter::Iterator;
/// fn run_gc<'a, 'b, 'c>(store: &'b mut Storage, roots: impl Iterator<Item=Ptr<'a>>) -> impl Iterator<Item=Ptr<'c>> {
/// # std::iter::empty()
/// # }
/// ```
///
/// except that the lifetimes `'a, 'b, 'c` do not overlap; they are sequential (in that order).
///
/// This has to be a macro, rather than a function, because a function can't take
///     fn gc(store, &'a)
/// where 'a is the lifetime of `store`.
// TODO: Is this what Pin<> is for? Kinda, except that we're also consuming it.
macro_rules! run_gc {
    ($store:expr, $roots:expr) => {{
        ($store).return_roots($roots);
        ($store).gc();
        ($store).retrieve_roots()
    }};
}

/// Data that exists for a single "generation" (between GCs).
#[derive(Default)]
struct Generation {
    objects: Vec<StoredValue>,
    string_data: Vec<u8>,

    // TODO: Understand & implement this myself.
    symbols: string_interner::DefaultStringInterner,
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Eq)]
pub struct StorageStats {
    pub objects: usize,
    pub string_data: usize,
    pub symbols: usize,
}

impl std::ops::Sub for StorageStats {
    type Output = StorageStats;

    fn sub(self, rhs: Self) -> Self::Output {
        StorageStats {
            objects: self.objects - rhs.objects,
            string_data: self.string_data - rhs.string_data,
            symbols: self.symbols - rhs.symbols,
        }
    }
}

impl Generation {
    /// Stores the Lisp object in storage.
    fn put_object(&mut self, object: Object) -> StoredPtr {
        let (stored, tag) = object.into();
        self.put(stored, tag)
    }

    /// Stores the Lisp object in storage.
    fn put(&mut self, stored: StoredValue, tag: u8) -> StoredPtr {
        let slot = self.objects.len();
        self.objects.push(stored);
        StoredPtr::new(slot, tag)
    }

    fn put_string(&mut self, content: &[u8]) -> StoredString {
        let offset = self.string_data.len() as u32;
        self.string_data.extend_from_slice(content);
        StoredString {
            offset,
            length: content.len() as u32,
        }
    }

    fn get(&self, ptr: StoredPtr) -> StoredValue {
        let idx = ptr.idx() as usize;
        assert!(idx < self.objects.len());
        self.objects[idx]
    }
}

/// Bind is a trait for binding stored types to the storage that holds them:
/// applying the Storage object lifetime to the underlying object.
trait Bind<'a> {
    type Free;

    fn bind(store: &'a Storage, free: Self::Free) -> Self;
}

impl Storage {
    fn bind<'a, T: Bind<'a>>(&'a self, raw: T::Free) -> T {
        T::bind(self, raw)
    }

    pub fn current_stats(&self) -> StorageStats {
        let gen = self.generation.borrow();
        StorageStats {
            objects: gen.objects.len(),
            string_data: gen.string_data.len(),
            symbols: gen.symbols.len(),
        }
    }
    pub fn max_stats(&self) -> StorageStats {
        self.high_water
    }

    /// Add a symbol to the symbol table.
    fn put_symbol<'a>(&'a self, symbol: &str) -> Ptr<'a> {
        let mut gen = self.generation.borrow_mut();
        let s = Symbol {
            symbol: gen.symbols.get_or_intern(symbol),
        };
        let raw = gen.put_object(Object::Symbol(s));
        self.bind(raw)
    }

    /// Add a string to the string content.
    pub fn put_string(&self, content: &[u8]) -> Ptr {
        let mut gen = self.generation.borrow_mut();
        let s: LString = self.bind(gen.put_string(content));
        self.bind(gen.put_object(s.into()))
    }

    /// Resolve a string to its binary contents.
    pub fn get_string<'a>(&'a self, s: &LString) -> Ref<'a, [u8]> {
        let gen = self.generation.borrow();
        Ref::map(gen, |v| &v.string_data[s.range()])
    }

    /// Stores the Lisp object in storage.
    pub fn put<'a>(&'a self, value: impl Into<Object<'a>>) -> Ptr<'a> {
        let value = value.into();
        if let Object::Nil = value {
            return Ptr::default();
        }
        let raw = self.generation.borrow_mut().put_object(value);
        self.bind(raw)
    }

    pub fn get<'a>(&'a self, ptr: Ptr<'a>) -> Object<'a> {
        if ptr.is_nil() {
            return Object::Nil;
        }

        let stored = self.generation.borrow().get(ptr.raw);
        Object::new(ptr, stored)
    }

    /// Provide the GC roots, in preparation for running a garbage collection pass.
    ///
    /// Because Ptr<>s borrow &self, all of them must be "returned" before performing a GC pass.
    /// The GC routine produces a new Storage from which roots may be taken;
    /// they are reported in the same order as they originally appeared when stored.
    pub fn return_roots<'a>(&'a self, roots: impl Iterator<Item = Ptr<'a>>) {
        *self.roots.borrow_mut() = roots.map(|x| x.raw).collect();
    }

    pub fn retrieve_roots<'a>(&'a self) -> impl 'a + Iterator<Item = Ptr<'a>> {
        self.roots.take().into_iter().map(|v| self.bind(v))
    }

    /// Run a garbage-collection pass, based on the provided roots.
    pub fn gc(&mut self) {
        // Soft-destructure:
        let last_gen = self.generation.take();
        let old_roots = self.roots.take();
        self.high_water = StorageStats {
            // Update stats before compaction:
            objects: max(self.high_water.objects, last_gen.objects.len()),
            string_data: max(self.high_water.string_data, last_gen.string_data.len()),
            symbols: max(self.high_water.symbols, last_gen.symbols.len()),
        };
        (*self.generation.get_mut(), *self.roots.get_mut()) = gc(last_gen, old_roots);
    }
}

/// Internal GC routine.
///
/// This is a "pure" function of the generations.
///
/// All pointers in the environment should be passed in via roots.
/// Pointers can change across a GC pass; the GC routine will fix up those in storage and those in `roots`.
fn gc(mut last_gen: Generation, roots: Vec<StoredPtr>) -> (Generation, Vec<StoredPtr>) {
    // TODO: Add trace output for debug

    let mut live_objects = BitSet::new();
    let mut queue: VecDeque<StoredPtr> = roots.iter().cloned().collect();

    let mut next_gen = Generation {
        symbols: Default::default(),
        // We'll never shrink below our number of live objects at _last_ GC.
        // We could apply some hysteresis here, but... eh, TODO.
        objects: Vec::with_capacity(last_gen.objects.len()),
        string_data: Vec::with_capacity(0),
    };
    let mut string_length = 0usize;

    // First pass:
    // -    Move all objects to the new arena.
    // -    Total up how much space we'll need for strings.
    // TODO: Consider a stack rather than a queue. Measure: do we run faster with one or the other?
    // (Hypothesis: stack will result in better data locality.)
    while let Some(old_ptr) = queue.pop_front() {
        let old_idx = old_ptr.idx();
        if live_objects.get(old_idx) {
            continue;
        }
        live_objects.set(old_idx);

        let got = last_gen.get(old_ptr);
        if let Some(p) = got.as_pair(old_ptr) {
            for rp in [p.car, p.cdr] {
                if !rp.is_nil() && !live_objects.get(rp.idx()) {
                    queue.push_back(rp);
                }
            }
        }
        if let Some(s) = got.as_string(old_ptr) {
            string_length += s.len() as usize;
        }

        // We've gotten what data we need.
        // Copy over, and leave a tombstone:
        let new_ptr = next_gen.put(got, old_ptr.tag());
        last_gen.objects[old_ptr.idx()].tombstone = new_ptr.idx();
    }

    // We have three more steps:
    // -    We need to update the roots to have the new indices. Fairly simple.
    // -    We need to update all the heap pointers to reflect their
    //      new indices - a second walk.
    // -    And we need to copy the string contents.
    // First case is easy, let's do it right quick,
    // while also forming the "new old pointers" list we'll need to update later.
    queue.clear();
    let mut new_roots = Vec::with_capacity(roots.len());
    for old_ptr in roots.iter() {
        queue.push_back(*old_ptr);
        // All "live" objects in the old arena now contain a tombstone entry,
        // their index in the new arena.
        let new_idx = unsafe { last_gen.objects[old_ptr.idx()].tombstone };
        new_roots.push(StoredPtr::new(new_idx, old_ptr.tag()));
    }

    // Now we have a list of "old" pointers in the heap to go through.
    next_gen.string_data.reserve_exact(string_length);
    while let Some(old_ptr) = queue.pop_front() {
        if live_objects.get(old_ptr.idx()) {
            // We haven't visited this on the second pass yet.
            live_objects.clear(old_ptr.idx());
        } else {
            continue;
        }

        if old_ptr.is_pair() {
            // This is a pair; we need to update its inner pointers,
            let new_idx = unsafe { last_gen.objects[old_ptr.idx()].tombstone };
            let pair = unsafe { &mut next_gen.objects[new_idx].pair };
            // This object still contains the old pointers, because we haven't visited this node on this pass.
            // We need to recurse; we can put the old pointers in this queue.
            for rp in [&mut pair.car, &mut pair.cdr] {
                queue.push_back(*rp);
                // And lookup + update the children - to the _new_ pointers:
                let new_cr = unsafe { last_gen.objects[rp.idx()].tombstone };
                *rp = StoredPtr::new(new_cr, rp.tag());
            }
        }
        if old_ptr.is_string() {
            // Copy the string to the new string buffer.
            let new_idx = unsafe { last_gen.objects[old_ptr.idx()].tombstone };
            let s = unsafe { &mut next_gen.objects[new_idx].string };

            let content = &last_gen.string_data[s.range()];
            s.offset = next_gen.string_data.len() as u32;
            next_gen.string_data.extend_from_slice(content);
        }
    }

    (next_gen, new_roots)
}

#[derive(Clone, Copy)]
#[repr(align(8))]
union StoredValue {
    integer: Integer,
    float: Float,

    pair: StoredPair,
    symbol: Symbol,
    string: StoredString,

    /// Pointer into the "next" arena, for copied-out objects.
    tombstone: usize,
}

impl StoredValue {
    fn as_pair(&self, ptr: StoredPtr) -> Option<StoredPair> {
        if ptr.is_pair() {
            Some(unsafe { self.pair })
        } else {
            None
        }
    }
    fn as_string(&self, ptr: StoredPtr) -> Option<StoredString> {
        if ptr.is_string() {
            Some(unsafe { self.string })
        } else {
            None
        }
    }
}

/// A "raw" pointer, without lifetime data.
/// This is the internal type for Storage; outside of storage,
/// the Ptr type provides a lifetime bound.
#[derive(Clone, Copy)]
struct StoredPtr {
    combined_tag: u32,
}

impl Default for StoredPtr {
    fn default() -> Self {
        Self::new(0, Self::TAG_NIL)
    }
}

impl StoredPtr {
    const TAG_NIL: u8 = 0;
    const TAG_INTEGER: u8 = 1;
    const TAG_STRING: u8 = 2;
    const TAG_FLOAT: u8 = 3;
    const TAG_SYMBOL: u8 = 4;
    const TAG_PAIR: u8 = 5;

    fn new(idx: usize, tag: u8) -> Self {
        StoredPtr {
            combined_tag: ((idx as u32) << 3) | (tag as u32),
        }
    }

    #[inline]
    fn tag(&self) -> u8 {
        (self.combined_tag & 0b111) as u8
    }

    #[inline]
    fn idx(&self) -> usize {
        (self.combined_tag & !0b111) as usize >> 3
    }

    #[inline]
    fn is_nil(&self) -> bool {
        self.tag() == Self::TAG_NIL
    }

    #[inline]
    fn is_integer(&self) -> bool {
        self.tag() == StoredPtr::TAG_INTEGER
    }
    #[inline]
    fn is_symbol(&self) -> bool {
        self.tag() == StoredPtr::TAG_SYMBOL
    }
    #[inline]
    fn is_float(&self) -> bool {
        self.tag() == StoredPtr::TAG_FLOAT
    }
    #[inline]
    fn is_string(&self) -> bool {
        self.tag() == StoredPtr::TAG_STRING
    }
    #[inline]
    fn is_pair(&self) -> bool {
        self.tag() == StoredPtr::TAG_PAIR
    }
}

impl std::fmt::Debug for StoredPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StoredPtr")
            .field("idx", &self.idx())
            .field("tag", &self.tag())
            .finish()
    }
}

#[derive(Copy, Clone, Debug)]
struct StoredPair {
    car: StoredPtr,
    cdr: StoredPtr,
}

#[derive(Copy, Clone, Debug)]
struct StoredString {
    offset: u32,
    length: u32,
}

impl StoredString {
    fn len(&self) -> u32 {
        self.length
    }
    fn range(&self) -> Range<usize> {
        let start = self.offset as usize;
        let end = (self.offset + self.length) as usize;
        start..end
    }
}

#[cfg(test)]
mod tests {
    use core::panic;

    use crate::data::{Pair, Ptr};

    use super::{Object, Storage};

    #[test]
    fn gc_numbers() {
        let mut store = Storage::default();

        let one = store.put(Object::Integer(1));
        let _ = store.put(Object::Float(3.0));
        let two = store.put(Object::Float(2.0));
        assert_eq!(store.current_stats().objects, 3);

        let ptrs : Vec<_> = run_gc!(store, [one, two].into_iter()).collect();
        assert_eq!(store.current_stats().objects, 2);
        let got_one = store.get(ptrs[0]);
        if let Object::Integer(1) = got_one {
        } else {
            panic!("unexpected object: {:?}", got_one);
        }

        let got_two = store.get(ptrs[1]);
        if let Object::Float(v) = got_two {
            if v != 2.0f64 {
                panic!("unexpected float value: {}", v)
            }
        } else {
            panic!("unexpected object: {:?}", got_two);
        }
    }

    #[test]
    fn gc_strings() {
        let mut store = Storage::default();

        const A: &[u8] = b"this is string A";
        const B: &[u8] = b"this is what I call string B";
        const C: &[u8] = b"this is what I call podracing!";

        let ptrs: [Ptr; 3] = [A, B, C].map(|b| store.put_string(b));
        assert_eq!(store.current_stats().objects, 3);
        assert_eq!(
            store.current_stats().string_data,
            A.len() + B.len() + C.len()
        );

        let ptrs : Vec<_> = run_gc!(store, ptrs.into_iter()).collect();
        assert_eq!(store.current_stats().objects, 3);
        if let Object::String(s) = store.get(ptrs[1]) {
            assert_eq!(store.get_string(&s).as_ref(), B);
        } else {
            panic!("unexpected object: {:?}", store.get(ptrs[1]));
        }
        let new_ptrs : Vec<_> = run_gc!(store, ptrs.into_iter().skip(1)).collect();
        assert_eq!(store.current_stats().objects, 2);
        assert_eq!(store.current_stats().string_data, B.len() + C.len());

        if let Object::String(s) = store.get(new_ptrs[1]) {
            assert_eq!(store.get_string(&s).as_ref(), C);
        } else {
            panic!("unexpected object: {:?}", store.get(new_ptrs[1]));
        }
    }

    #[test]
    fn gc_pairs() {
        let mut store = Storage::default();

        // Here's the real challenge for the GC!
        const A: &[u8] = b"Now this is podracing!";
        const B: &[u8] = b"This is...not really podracing.";
        let a = store.put_string(A);
        let b = store.put_string(B);

        // '(a a b) in one list; '(b b) in another, using the same final cell.
        let stack = {
            let ls1 = store.put(Pair::cons(b, Object::nil()));
            let lsa1 = store.put(Pair::cons(a, ls1));
            let lsa = store.put(Pair::cons(a, lsa1));

            let lsb = store.put(Pair::cons(b, ls1));

            [lsb, lsa]
        };
        assert_eq!(store.current_stats().objects, 6);
        assert_eq!(store.current_stats().string_data, A.len() + B.len());

        let pre_stats = store.current_stats();
        let stack : Vec<_> = run_gc!(store, stack.into_iter()).collect();
        assert_eq!(store.current_stats(), pre_stats);

        let stack_top = run_gc!(store, [stack[0]].into_iter()).next().unwrap();
        // ('b b ()): objects are b, (b ()), and (b (b ()))
        assert_eq!(store.current_stats().string_data, B.len());
        assert_eq!(store.current_stats().objects, 3);

        // Look, this will fail to compile- the lifetime of stack[] has to have ended:
        // let _ = store.get(stack[0]);

        let top = store.get(stack_top);
        // This should be the root of the B tree:
        let (car, cdr) = match top {
            Object::Pair(Pair { car, cdr }) => (car, cdr),
            _ => panic!("unexpected object: {:?}", top),
        };
        let (car, cdr) = match (store.get(car), store.get(cdr)) {
            (Object::String(ls), Object::Pair(Pair { car, cdr })) => {
                let s = store.get_string(&ls);
                assert_eq!(s.as_ref(), B);
                (car, cdr)
            }
            _ => panic!("unexpected object: {:?}", top),
        };
        match (store.get(car), store.get(cdr)) {
            (Object::String(ls), Object::Nil) => {
                let s = store.get_string(&ls);
                assert_eq!(s.as_ref(), B);
            }
            _ => panic!("unexpected object: {:?}", top),
        };
    }
}
