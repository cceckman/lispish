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
//!     TODO: Use intern ID instead of a separate object.
//! -   String _objects_ provide ownership semantics over string _ranges_.
//!     Strings use a ~typical allocator, with sizes rounded up to the nearest 8B.
//!

mod bitset;

use std::cell::{Ref, RefCell, RefMut};
use std::ops::DerefMut;
use std::{cmp::max, collections::VecDeque, ops::Range};
mod objects;
pub use objects::*;
use string_interner::DefaultSymbol;
use string_interner::Symbol as _;

use crate::eval::Builtin;

use self::bitset::BitSet;
pub use self::render::ObjectFormat;
use self::render::ObjectFormats;

#[cfg(feature = "render")]
mod render;

/// Storage allows representing all persistent objects.
#[derive(Default)]
pub struct Storage {
    generation: RefCell<Generation>,

    // TODO: Understand & implement this myself.
    // Because symbols are interned, they are not generationed/lifetime-bound.
    symbols: RefCell<string_interner::DefaultStringInterner>,

    root: RefCell<StoredPtr>,

    high_water: StorageStats,

    /// Node metadata.
    /// These provide useful debugging info, like "this is the root of the stack".
    labels: RefCell<ObjectFormats>,
}

/// Data that exists for a single "generation" (between GCs).
struct Generation {
    objects: Vec<StoredValue>,
    string_data: Vec<u8>,
}

impl Default for Generation {
    fn default() -> Self {
        Self {
            // Always reserve the 0 index.
            objects: vec![StoredValue { tombstone: 0 }],
            string_data: Default::default(),
        }
    }
}

impl Generation {
    fn with_capacity(len: usize) -> Self {
        let mut objects = Vec::with_capacity(len);
        // Reserve 0:
        objects.push(StoredValue { tombstone: 0 });
        Self {
            // Always reserve the 0 index.
            objects,
            string_data: Default::default(),
        }
    }

    /// Gets the "next" pointer for this object.
    fn get_next(&self, old_ptr: StoredPtr) -> StoredPtr {
        if old_ptr.is_nil() || old_ptr.is_symbol() {
            old_ptr
        } else {
            let idx = unsafe { self.objects[old_ptr.idx()].tombstone };
            StoredPtr::new(idx, old_ptr.tag())
        }
    }
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Eq)]
pub struct StorageStats {
    pub objects: usize,
    pub string_data: usize,
    pub symbols: usize,
}

impl StorageStats {
    fn max(&self, other: &StorageStats) -> StorageStats {
        StorageStats {
            // Update stats before compaction:
            objects: max(self.objects, other.objects),
            string_data: max(self.string_data, other.string_data),
            symbols: max(self.symbols, other.symbols),
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
        let idx = ptr.idx();
        assert!(idx < self.objects.len());
        self.objects[idx]
    }

    fn update(&mut self, ptr: StoredPtr, pair: StoredPair) {
        let idx = ptr.idx();
        assert!(idx < self.objects.len());
        self.objects[idx].pair = pair;
    }
}

/// Bind is a trait for binding stored types to the storage that holds them:
/// applying the Storage object lifetime to the underlying object.
trait Bind<'a> {
    type Free;

    fn bind(store: &'a Storage, free: Self::Free) -> Self;
}

impl Storage {
    /// Set the formatting metadata for the given node.
    #[cfg(feature = "render")]
    pub fn format<'a>(&'a self, p: Ptr<'_>) -> impl 'a + DerefMut<Target = ObjectFormat> {
        RefMut::map(self.labels.borrow_mut(), |m| -> &mut ObjectFormat {
            let entry = m.entry(p.raw);
            entry.or_default()
        })
    }

    fn bind<'a, T: Bind<'a>>(&'a self, raw: T::Free) -> T {
        T::bind(self, raw)
    }

    pub fn current_stats(&self) -> StorageStats {
        let gen = self.generation.borrow();
        StorageStats {
            // Discount one object, the reserved nil index.
            objects: gen.objects.len() - 1,
            string_data: gen.string_data.len(),
            symbols: self.symbols.borrow().len(),
        }
    }
    pub fn max_stats(&self) -> StorageStats {
        self.current_stats().max(&self.high_water)
    }

    /// Add a symbol to the symbol table.
    pub fn put_symbol(&self, symbol: &str) -> Ptr {
        let s = self
            .symbols
            .borrow_mut()
            .get_or_intern(symbol.to_uppercase());
        self.bind(StoredPtr::new(s.to_usize(), StoredPtr::TAG_SYMBOL))
    }

    /// Retrieve a symbol to the symbol table.
    pub fn get_symbol(&self, idx: Symbol) -> Ref<'_, str> {
        let symtab = self.symbols.borrow();
        Ref::map(symtab, |v| {
            v.resolve(idx.0).expect("retrieved nonexistent symbol")
        })
    }

    /// Retrieve a symbol to the symbol table.
    pub fn get_symbol_ptr(&self, ptr: Ptr) -> Ref<'_, str> {
        let symbol = DefaultSymbol::try_from_usize(ptr.idx()).unwrap();
        let symtab = self.symbols.borrow();
        Ref::map(symtab, |v| {
            v.resolve(symbol).expect("retrieved nonexistent symbol")
        })
    }

    /// Replace the given pair with a new one.
    /// This is the only form of update permitted,
    /// since it is sufficient to rebind variables.
    pub fn update(&self, ptr: Ptr, object: Pair) {
        assert!(ptr.is_pair());
        self.generation.borrow_mut().update(ptr.raw, object.into());
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
            Object::Nil
        } else if ptr.is_symbol() {
            Object::Symbol(Symbol(DefaultSymbol::try_from_usize(ptr.idx()).unwrap()))
        } else {
            let stored = self.generation.borrow().get(ptr.raw);
            Object::new(ptr, stored)
        }
    }

    /// Get the current GC root.
    /// Only one root may exist; the caller creates / destroys its own structure for this.
    pub fn root(&self) -> Ptr {
        self.bind(*self.root.borrow())
    }

    pub fn set_root<'a>(&'a self, root: Ptr<'a>) {
        *self.root.borrow_mut() = root.raw;
    }

    /// Run a garbage-collection pass, based on the provided roots.
    pub fn gc(&mut self) {
        let current_stats = self.current_stats();
        self.high_water = current_stats.max(&self.high_water);

        // Soft-destructure:
        let last_gen = self.generation.take();
        let mut root = self.root.borrow_mut();
        let mut labels = self.labels.borrow_mut();

        let mut roots = [root.deref_mut()];
        *self.generation.get_mut() = gc_internal(last_gen, &mut roots, &mut labels);
    }

    /// Get a displayable representation of the item.
    pub fn display(&self, it: Object) -> String {
        match it {
            Object::Nil => "nil".to_owned(),
            Object::Integer(i) => format!("{}", i),
            Object::Float(i) => format!("{}", i),
            Object::String(j) => format!("\"{}\"", &String::from_utf8_lossy(&self.get_string(&j))),
            Object::Symbol(j) => format!("{}", self.get_symbol(j)),
            Object::Pair(Pair { car, cdr }) => format!("({car}, {cdr})"),
            Object::Builtin(f) => format!("fn {f:p}"),
        }
    }

    pub fn lookup(&self, object_id: &str) -> Result<Ptr<'_>, String> {
        let stored: StoredPtr = object_id.parse()?;
        let max_obj = self.generation.borrow().objects.len();
        let max_sym = self.symbols.borrow().len();

        if stored.is_symbol() && stored.idx() < max_sym || stored.idx() < max_obj {
            Ok(self.bind(stored))
        } else {
            Err(format!("object {} is invalid - out of range", stored))
        }
    }
}

/// Internal GC routine.
///
/// This is a "pure" function of the generations.
///
/// All pointers in the environment should be passed in via roots.
/// Pointers can change across a GC pass; the GC routine will fix up those in storage and those in `roots`.
fn gc_internal(
    mut last_gen: Generation,
    roots: &mut [&mut StoredPtr],
    labels: &mut ObjectFormats,
) -> Generation {
    // TODO: Add trace output for debug

    let mut live_objects = BitSet::new();
    let mut queue: VecDeque<StoredPtr> = roots
        .iter()
        .filter_map(|v| if !v.is_nil() { Some(**v) } else { None })
        .collect();

    // We'll never shrink below our number of live objects at _last_ GC.
    // We could apply some hysteresis here, but... eh, TODO.
    let mut next_gen = Generation::with_capacity(last_gen.objects.len());
    let mut string_length = 0usize;

    // First pass:
    // -    Move all objects to the new arena.
    // -    Total up how much space we'll need for strings.
    // TODO: Consider a stack rather than a queue. Measure: do we run faster with one or the other?
    // (Hypothesis: stack will result in better data locality.)
    while let Some(old_ptr) = queue.pop_front() {
        // Internal check: we shouldn't traverse to nil pointers or to symbols,
        // they're the same in the new generation.
        assert!(!old_ptr.is_nil() && !old_ptr.is_symbol());

        let old_idx = old_ptr.idx();
        if live_objects.get(old_idx) {
            continue;
        }
        live_objects.set(old_idx);

        let got = last_gen.get(old_ptr);
        if let Some(p) = got.recursable(old_ptr) {
            for rp in [p.car, p.cdr] {
                // Skip over nil (always 0) and symbols (different indices,
                // perpetual).
                if !rp.is_nil() && !rp.is_symbol() && !live_objects.get(rp.idx()) {
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

    // Now that we've moved everything, we can update labels, dropping any unused.
    *labels = labels
        .drain()
        .filter_map(|(old_ptr, v)| {
            if !live_objects.get(old_ptr.idx()) {
                None
            } else {
                Some((last_gen.get_next(old_ptr), v))
            }
        })
        .collect();

    // Three more steps:
    // -    We need to update the roots and stored-ptrs to have the new indices. Fairly simple.
    // -    We need to update all the heap pointers to reflect their
    //      new indices - a second walk.
    // -    And we need to copy the string contents.
    // First case is easy, let's do it right quick,
    // while also forming the "new old pointers" list we'll need to update later.
    for old_root in roots.iter_mut() {
        if old_root.is_nil() {
            continue;
        }
        queue.push_back(**old_root);
        // All "live" objects in the old arena now contain a tombstone entry,
        // their index in the new arena.
        **old_root = last_gen.get_next(**old_root);
    }

    // Now we have a list of "old" pointers in the heap to go through.
    next_gen.string_data.reserve_exact(string_length);
    while let Some(old_ptr) = queue.pop_front() {
        // Internal check: we shouldn't traverse to nil pointers.
        assert!(!old_ptr.is_nil());

        if !live_objects.get(old_ptr.idx()) {
            // We cleared the liveness on a previous pass.
            continue;
        }
        // We haven't visited this on the second pass yet.
        live_objects.clear(old_ptr.idx());

        let new_ptr = last_gen.get_next(old_ptr);
        if let Some(mut pair) = next_gen.get(new_ptr).recursable(new_ptr) {
            // This is a pair/function we need to update its inner pointers, in the new arena.
            // This object still contains the old pointers, because we haven't visited this node on this pass.
            // Put the old pointers in the queue, and update the new location.
            for rp in [&mut pair.car, &mut pair.cdr] {
                let new_ptr = last_gen.get_next(*rp);
                if !(new_ptr.is_nil() || new_ptr.is_symbol()) {
                    queue.push_back(*rp);
                }
                *rp = new_ptr;
            }
            next_gen.objects[new_ptr.idx()].pair = pair;
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

    next_gen
}

#[derive(Clone, Copy)]
#[repr(align(8))]
union StoredValue {
    integer: Integer,
    float: Float,

    pair: StoredPair,
    string: StoredString,

    builtin: Builtin,

    /// Pointer into the "next" arena, for copied-out objects.
    tombstone: usize,
}

impl StoredValue {
    fn recursable(&self, ptr: StoredPtr) -> Option<StoredPair> {
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
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
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
    // TODO: Can we use tag 6 for "compiled function"?
    // Or do we even need that, once we get strings into the lisp store?
    const TAG_BUILTIN: u8 = 7;

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

    #[inline]
    fn is_builtin(&self) -> bool {
        self.tag() == StoredPtr::TAG_BUILTIN
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

impl From<Pair<'_>> for StoredPair {
    fn from(pair: Pair) -> Self {
        StoredPair {
            car: pair.car.raw,
            cdr: pair.cdr.raw,
        }
    }
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

        {
            let root = store.put(Pair::cons(one, two));
            store.set_root(root);
        }
        store.gc();

        assert_eq!(store.current_stats().objects, 3);

        let Pair { car, cdr } = store
            .get(store.root())
            .try_into()
            .expect("root should be a pair");
        let got_one = store.get(car);
        if let Object::Integer(1) = got_one {
        } else {
            panic!("unexpected object: {:?}", got_one);
        }

        let got_two = store.get(cdr);
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

        if let Object::String(s) = store.get(ptrs[1]) {
            assert_eq!(store.get_string(&s).as_ref(), B);
        } else {
            panic!("unexpected object: {:?}", store.get(ptrs[1]));
        }

        store.set_root(store.put(Pair::cons(ptrs[1], ptrs[2])));
        store.gc();

        assert_eq!(store.current_stats().objects, 3);
        assert_eq!(store.current_stats().string_data, B.len() + C.len());

        let Pair { cdr: got_c, .. } = store
            .get(store.root())
            .try_into()
            .expect("root should be a pair");
        if let Object::String(s) = store.get(got_c) {
            assert_eq!(store.get_string(&s).as_ref(), C);
        } else {
            panic!("unexpected object: {:?}", store.get(got_c));
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

            Pair::cons(lsa, lsb)
        };
        assert_eq!(store.current_stats().objects, 6);
        assert_eq!(store.current_stats().string_data, A.len() + B.len());

        store.set_root(store.put(stack));
        let pre_stats = store.current_stats();
        store.gc();
        assert_eq!(store.current_stats(), pre_stats);

        let Pair { cdr: lsb, .. } = store
            .get(store.root())
            .try_into()
            .expect("root should be a pair");
        store.set_root(lsb);
        store.gc();
        let stack_top = store.root();
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

    #[test]
    fn gc_symbols() {
        let mut store = Storage::default();

        // Set up some symbols.
        // Symbols have a separate index space!
        let define = store.put_symbol("define");
        let lambda = store.put_symbol("lambda");
        let _cool = store.put_symbol("cool");
        let a = store.put(1i64);
        let _b = store.put(2i64);

        // We won't hold on to object b or symbol cool.
        let x = store.put(Pair::cons(define, Ptr::nil()));
        let y = store.put(Pair::cons(lambda, x));
        let root = store.put(Pair::cons(a, y));
        store.set_root(root);

        assert_eq!(store.current_stats().objects, 5);
        store.gc();
        // Keep: a, y, x, root.
        assert_eq!(store.current_stats().objects, 4);
    }
}
