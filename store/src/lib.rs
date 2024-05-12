//! Lisp data types and allocators.
//!
//!
//! ## Revised design
//!
//! The Lisp store is backed by an arena allocator of up to ~4000MiB.
//! (Yes, not 4GiB- the difference allows for certain overheads.)
//!
//! The store provides pointer-tagged storage:
//! - `put` methods store objects, and return pointers tagged with the relevant type.
//! - `get` methods retrieve objects based on the pointer.
//!
//! The supported objects are:
//! -   Nil: The nil pointer.
//! -   Integer: a 64-bit integer.
//! -   Float: a 64-bit floating-point number (IEEE 754).
//! -   Pair: a pair of pointers to objects.
//! -   Bytes: 8 bytes.
//! -   Vector: A reference to a set of contiguously-allocated _objects_,
//!     all of the same type, which are neither nil nor symbol.
//! -   Symbol: an entry in the designated, interned symbol table.
//!
//! In addition, there are some distinguished _constructs_ that the storage
//! layer uses.
//! -   A ByteVector consists of a (length, vector-of-bytes) tuple.
//! -   The symbol table is a vector of Strings.
//!     The storage layer preserves and maintains its root independent of
//!     the stack pointer(s).
//! -   TODO: A String is a ByteVector that contains only UTF-8 codepoints.
//!
//! ## Old notes
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
//! -   String _objects_ provide ownership semantics over string _ranges_.
//!     Strings use a ~typical allocator, with sizes rounded up to the nearest 8B.
//!

mod bitset;

use std::cell::{RefCell, RefMut};
use std::ops::DerefMut;
use std::{cmp::max, collections::VecDeque};
mod objects;
pub use objects::*;
use strings::to_bytes;
mod strings;
mod symbols;
mod vectors;
pub use vectors::ByteVector;

use self::bitset::BitSet;
pub use self::render::ObjectFormat;
use self::render::ObjectFormats;

#[cfg(feature = "render")]
mod render;

mod tag;
pub use tag::*;

/// A zero-allocation error type.
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

impl std::fmt::Debug for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "for object {}: {}", self.ptr, self.message)
    }
}

impl std::fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "for object {}: {}", self.ptr, self.message)
    }
}

/// Storage allows representing all persistent objects.
pub struct Storage {
    generation: RefCell<Generation>,

    /// Root of the main object tree.
    root: RefCell<StoredPtr>,

    /// Auxiliary object tree: the symbol table.
    /// A vector of strings.
    /// (Note: try to re-GC after declaring each symbol!)
    symbols: RefCell<StoredPtr>,

    high_water: StorageStats,

    /// Node metadata.
    /// These provide useful debugging info, like "this is the root of the stack".
    labels: RefCell<ObjectFormats>,
}

impl Default for Storage {
    fn default() -> Self {
        let s = Self {
            generation: Default::default(),
            root: Default::default(),
            symbols: Default::default(),
            high_water: Default::default(),
            labels: Default::default(),
        };
        let symbols = s.put_vector::<Pair>(std::iter::empty());
        *s.symbols.borrow_mut() = symbols.raw;
        s
    }
}

/// Data that exists for a single "generation" (between GCs).
struct Generation {
    objects: Vec<StoredValue>,
}

impl Default for Generation {
    fn default() -> Self {
        Self {
            // Always reserve the 0 index.
            objects: vec![StoredValue { tombstone: 0 }],
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
    pub symbols: usize,
}

impl StorageStats {
    fn max(&self, other: &StorageStats) -> StorageStats {
        StorageStats {
            // Update stats before compaction:
            objects: max(self.objects, other.objects),
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
    fn put(&mut self, stored: StoredValue, tag: Tag) -> StoredPtr {
        let slot = self.objects.len();
        self.objects.push(stored);
        StoredPtr::new(slot, tag)
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
        let sym_ptr: Ptr = self.bind(*self.symbols.borrow());
        let symbols = sym_ptr.get().as_vector().map(|v| v.length).unwrap_or(0) as usize;

        let gen = self.generation.borrow();
        StorageStats {
            // Discount one object, the reserved nil index.
            objects: gen.objects.len() - 1,
            symbols,
        }
    }
    pub fn max_stats(&self) -> StorageStats {
        self.current_stats().max(&self.high_water)
    }

    /// Add a symbol to the symbol table,
    /// or return the pointer to this symbol if already present.
    pub fn put_symbol(&self, symbol: impl symbols::SymbolInput) -> Ptr {
        symbols::put(self, symbol)
    }

    /// Insert a uniform vector into the storage.
    #[allow(private_bounds)]
    pub fn put_vector<T>(&self, v: impl Iterator<Item = T>) -> Ptr
    where
        T: UniformVector,
    {
        // We have to acquire & release borrow_mut repeatedly here,
        // because "get the object" on the iterator may require borrowing
        // the generation to resolve the object.
        let start_idx = self.generation.borrow().objects.len();
        for object in v {
            let storeable = object.store();
            self.generation.borrow_mut().put(storeable, T::tag());
        }
        let mut gen = self.generation.borrow_mut();
        let length = gen.objects.len() - start_idx;
        let ptr = StoredPtr::new(start_idx, T::tag());
        let vec = StoredVector {
            length: length as u32,
            start: ptr,
        };
        let p = gen.put(StoredValue { vector: vec }, Tag::Vector);
        self.bind(p)
    }

    /// Get a pointer-to-an-element from a vector.
    /// Returns none if v is not a vector or if the index is out-of-range.
    pub fn get_element_ptr(&self, v: Ptr, idx: u32) -> Option<Ptr> {
        let stored_vector = self.generation.borrow().get(v.raw).as_vector(v.raw)?;
        let ptr = stored_vector.offset(idx)?;
        Some(self.bind(ptr))
    }

    /// Replace the given pair with a new one.
    /// This is the only form of update permitted,
    /// since it is sufficient to rebind variables.
    pub fn update(&self, ptr: Ptr, object: Pair) {
        assert!(ptr.is_pair());
        self.generation.borrow_mut().update(ptr.raw, object.into());
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
            Object::Symbol(Symbol::bind(self, ptr.idx()))
        } else {
            let stored = self.generation.borrow().get(ptr.raw);
            Object::bind(self, (ptr.raw, stored))
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

    /// Get the symbol table.
    fn symbols(&self) -> Vector {
        self.bind::<Ptr>(*self.symbols.borrow())
            .get()
            .as_vector()
            .unwrap()
    }

    /// Update the symbol table.
    fn set_symbols(&self, new: Ptr) {
        assert!(new.is_vector());
        *self.symbols.borrow_mut() = new.raw;
    }

    pub fn put_string(&self, input: impl Iterator<Item = char>) -> Ptr<'_> {
        self.put_bytes(to_bytes(input))
    }

    pub fn put_bytes(&self, input: impl Iterator<Item = u8>) -> Ptr<'_> {
        vectors::make_byte_vector(self, input)
    }

    /// Run a garbage-collection pass, based on the provided roots.
    pub fn gc(&mut self) {
        let current_stats = self.current_stats();
        tracing::trace!("starting GC with stats: {:?}", current_stats);
        self.high_water = current_stats.max(&self.high_water);

        // Soft-destructure:
        let last_gen = self.generation.take();
        let mut root = self.root.borrow_mut();
        let mut symbols = self.symbols.borrow_mut();
        let mut labels = self.labels.borrow_mut();

        // We intentionally put the symbol table first,
        // so that nice ~stable vector can land early.
        let mut roots = [symbols.deref_mut(), root.deref_mut()];
        *self.generation.get_mut() = gc_internal(last_gen, &mut roots, &mut labels);

        tracing::trace!("stats after GC: {:?}", self.current_stats());
    }

    /// Get a displayable representation of the item.
    pub fn display(&self, it: Object) -> String {
        match it {
            Object::Nil => "nil".to_owned(),
            Object::Integer(i) => format!("{}", i),
            Object::Float(i) => format!("{}", i),
            Object::Symbol(j) => j.get().collect(),
            Object::Pair(Pair { car, cdr }) => format!("({car}, {cdr})"),
            Object::Bytes(b) => format!("0x{b:02x?}"),
            Object::Vector(b) => {
                let mut out = "[".to_string();
                // As with Pair, we don't display the objects themselves, just the
                // pointers. A vector may contain itself!
                let ptrs: Vec<_> = b.into_iter().map(|p| format!("{p}")).collect();
                out += &ptrs.join(", ");
                out += "]";
                out
            }
        }
    }

    /// Look up an object in storage by a stringified pointer.
    ///
    /// `Ptr` cannot "just" implement `FromStr` because it cannot correctly infer
    /// the lifetime. This function validates the pointer's range and binds it to
    /// this arena's lifetime.
    ///
    /// Note, though, this does not and cannot check the type of the pointer;
    /// we're trusting that the tag in the string matches the actual object.
    pub fn lookup(&self, object_id: impl AsRef<str>) -> Result<Ptr<'_>, String> {
        let stats = self.current_stats();
        let stored: StoredPtr = object_id.as_ref().parse()?;
        let max_obj = self.generation.borrow().objects.len();
        let max_sym = stats.symbols;

        let symbol_ok = stored.is_symbol() && stored.idx() < max_sym;
        let object_ok = !stored.is_symbol() && stored.idx() < max_obj;

        if symbol_ok || object_ok {
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
    let mut live_objects = BitSet::new();
    let mut queue: VecDeque<StoredPtr> = roots
        .iter()
        .filter_map(|v| if !v.is_nil() { Some(**v) } else { None })
        .collect();

    // First pass:
    // -    Move all objects to the new arena.
    // -    Total up how much space we'll need for strings.
    // TODO: Consider a stack rather than a queue. Measure: do we run faster with one or the other?
    // (Hypothesis: stack will result in better data locality.)
    while let Some(old_ptr) = queue.pop_front() {
        let old_idx = old_ptr.idx();
        if old_ptr.is_nil() || old_ptr.is_symbol() || live_objects.get(old_idx) {
            // Iether a non-moving value, or already have visited.
            // Skip.
            continue;
        }
        live_objects.set(old_idx);

        let got = last_gen.get(old_ptr);
        if let Some(p) = got.as_pair(old_ptr) {
            for rp in [p.car, p.cdr] {
                // Skip over nil (always 0) and symbols (different indices,
                // perpetual).
                if !rp.is_nil() && !rp.is_symbol() && !live_objects.get(rp.idx()) {
                    queue.push_back(rp);
                }
            }
        }
        if let Some(v) = got.as_vector(old_ptr) {
            // Visit each of the children
            // (that is neither nil nor a symbol- skip them up-front rather than enqueueing).
            queue.extend(v.filter(|p| !(p.is_symbol() || p.is_nil())))
        }
    }

    // We've marked all the objects.
    // Copy them to the new generation, and leave a tombstone.
    let mut next_gen = Generation::with_capacity(live_objects.count());
    for old_idx in live_objects.bits_set() {
        let new_idx = next_gen.objects.len();
        next_gen.objects.push(last_gen.objects[old_idx]);
        last_gen.objects[old_idx].tombstone = new_idx;
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
    while let Some(old_ptr) = queue.pop_front() {
        // Internal check: we shouldn't traverse to nil pointers.
        assert!(!old_ptr.is_nil());
        assert!(!old_ptr.is_symbol());

        if !live_objects.get(old_ptr.idx()) {
            // We cleared the liveness on a previous pass.
            continue;
        }
        // We haven't visited this on the second pass yet.
        live_objects.clear(old_ptr.idx());

        let new_ptr = last_gen.get_next(old_ptr);
        if let Some(mut pair) = next_gen.get(new_ptr).as_pair(new_ptr) {
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
        if let Some(old_vector) = next_gen.get(new_ptr).as_vector(new_ptr) {
            // First, remap the start:
            let new_start = last_gen.get_next(old_vector.start);
            next_gen.objects[new_ptr.idx()].vector = StoredVector {
                length: old_vector.length,
                start: new_start,
            };

            // And - we need to visit all the _old_ locations.
            queue.extend(old_vector.filter(|p| !(p.is_symbol() || p.is_nil())))
        }
    }

    next_gen
}

#[derive(Clone, Copy)]
#[repr(align(8))]
union StoredValue {
    integer: Integer,
    float: Float,

    /// Representation for a bytevector chunk, or a string-of-bytes chunk.
    bytes: [u8; 8],

    /// Representation for a single pair.
    pair: StoredPair,
    /// Descriptor for a vector.
    /// If the type of the pointer to this StoredVector is "vector",
    /// the type of the StoredVector's content pointer indicates the inner type.
    vector: StoredVector,

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

    fn as_vector(&self, ptr: StoredPtr) -> Option<StoredVector> {
        if ptr.is_vector() {
            let v = unsafe { self.vector };
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct StoredVector {
    length: u32,
    start: StoredPtr,
}

impl StoredVector {
    /// Get an offsetted pointer into this vector.
    pub fn offset(&self, i: u32) -> Option<StoredPtr> {
        if i < self.length {
            Some(StoredPtr::new(
                self.start.idx() + i as usize,
                self.start.tag(),
            ))
        } else {
            None
        }
    }
}

impl Iterator for StoredVector {
    type Item = StoredPtr;
    fn next(&mut self) -> Option<Self::Item> {
        if self.length > 0 {
            let result = Some(self.start);
            self.length -= 1;
            self.start = StoredPtr::new(self.start.idx() + 1, self.start.tag());
            result
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
        Self::new(0, Tag::Nil)
    }
}

/// The types that can be stored in a (uniform) vector.
///
/// These are only:
/// - Integers
/// - Floats
/// - Bytes
/// - Pairs
/// - TODO: Vectors
/// - TODO: Strings
///
/// Other types, such as "symbol",
/// or non-uniform types, i.e. a vector of mixed types,
/// can be encoded as a vector of pairs
/// (optionally / by default, with chaining, so list algorithms still operate on them).
trait UniformVector {
    /// Get the tag to use for this type.
    fn tag() -> Tag;

    /// Convert to the stored representation.
    fn store(self) -> StoredValue;
}

impl UniformVector for Integer {
    fn tag() -> Tag {
        Tag::Integer
    }
    fn store(self) -> StoredValue {
        StoredValue { integer: self }
    }
}

impl UniformVector for Float {
    fn tag() -> Tag {
        Tag::Float
    }
    fn store(self) -> StoredValue {
        StoredValue { float: self }
    }
}

impl UniformVector for Pair<'_> {
    fn tag() -> Tag {
        Tag::Pair
    }
    fn store(self) -> StoredValue {
        StoredValue {
            pair: StoredPair {
                car: self.car.raw,
                cdr: self.cdr.raw,
            },
        }
    }
}

impl UniformVector for Bytes {
    fn tag() -> Tag {
        Tag::Bytes
    }
    fn store(self) -> StoredValue {
        StoredValue { bytes: self }
    }
}

impl StoredPtr {
    fn new(idx: usize, tag: Tag) -> Self {
        StoredPtr {
            combined_tag: ((idx as u32) << 3) | (tag as u32),
        }
    }

    #[inline]
    fn tag(&self) -> Tag {
        ((self.combined_tag & 0b111) as u8).into()
    }

    #[inline]
    fn idx(&self) -> usize {
        (self.combined_tag as usize & !0b111) >> 3
    }

    #[inline]
    fn is_nil(&self) -> bool {
        self.tag() == Tag::Nil
    }

    #[inline]
    fn is_integer(&self) -> bool {
        self.tag() == Tag::Integer
    }
    #[inline]
    fn is_symbol(&self) -> bool {
        self.tag() == Tag::Symbol
    }
    #[inline]
    fn is_float(&self) -> bool {
        self.tag() == Tag::Float
    }
    #[inline]
    fn is_pair(&self) -> bool {
        self.tag() == Tag::Pair
    }
    #[inline]
    fn is_vector(&self) -> bool {
        self.tag() == Tag::Vector
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

#[cfg(test)]
mod tests {
    use core::panic;

    use crate::Bytes;

    use super::{Object, Pair, Ptr, Storage};

    #[test]
    fn gc_numbers() {
        let mut store = Storage::default();

        let one = store.put(Object::Integer(1));
        let _ = store.put(Object::Float(3.0));
        let two = store.put(Object::Float(2.0));
        let pre_stats = store.current_stats();

        {
            let root = store.put(Pair::cons(one, two));
            store.set_root(root);
        }
        store.gc();

        assert_eq!(store.current_stats(), pre_stats);

        let Pair { car, cdr } = store
            .root()
            .get()
            .try_into()
            .expect("root should be a pair");
        let got_one = car.get();
        if let Object::Integer(1) = got_one {
        } else {
            panic!("unexpected object: {:?}", got_one);
        }

        let got_two = cdr.get();
        if let Object::Float(v) = got_two {
            if v != 2.0f64 {
                panic!("unexpected float value: {}", v)
            }
        } else {
            panic!("unexpected object: {:?}", got_two);
        }
    }

    #[test]
    fn gc_pairs() {
        let mut store = Storage::default();

        // Here's the real challenge for the GC!
        const A: i64 = 14325343;
        const B: f64 = 1.3324;
        let a = store.put(A);
        let b = store.put(B);

        // '(a a b) in one list; '(b b) in another, using the same final cell.
        // Objects are:
        // a
        // b
        // (b ())
        // (a (b ()))
        // (a (a (b ())))
        // (b (b ()))
        // and the root combining those two trees.
        let stack = {
            let ls1 = store.put(Pair::cons(b, Object::nil()));
            let lsa1 = store.put(Pair::cons(a, ls1));
            let lsa = store.put(Pair::cons(a, lsa1));

            let lsb = store.put(Pair::cons(b, ls1));

            Pair::cons(lsa, lsb)
        };

        store.set_root(store.put(stack));
        let pre_stats = store.current_stats();
        store.gc();
        assert_eq!(store.current_stats(), pre_stats);

        let Pair { cdr: lsb, .. } = store
            .get(store.root())
            .try_into()
            .expect("root should be a pair");
        store.set_root(lsb);
        // Objects are:
        // b
        // (b ())
        // (b (b ()))
        // with no additional root (we kept one of the branches as the root.)
        store.gc();
        let stack_top = store.root();
        // ('b b ()): objects are b, (b ()), and (b (b ()))
        assert_eq!(pre_stats.objects - store.current_stats().objects, 4);

        // Look, this will fail to compile- the lifetime of stack[] has to have ended:
        // let _ = store.get(stack[0]);

        let top = stack_top.get();
        // This should be the root of the B tree:
        let (car, cdr) = match top {
            Object::Pair(Pair { car, cdr }) => (car, cdr),
            _ => panic!("unexpected object: {:?}", top),
        };
        let (car, cdr) = match (car.get(), cdr.get()) {
            (Object::Float(f), Object::Pair(Pair { car, cdr })) => {
                assert_eq!(f, B);
                (car, cdr)
            }
            _ => panic!("unexpected object: {:?}", top),
        };
        match (car.get(), cdr.get()) {
            (Object::Float(f), Object::Nil) => {
                assert_eq!(f, B);
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
        let cool = store.put_symbol("cool").to_string();
        let a = store.put(1i64);
        let b = store.put(2i64).to_string();

        // We won't hold on to object b or symbol cool.
        let x = store.put(Pair::cons(define, Ptr::nil()));
        let y = store.put(Pair::cons(lambda, x));
        let root = store.put(Pair::cons(a, y));
        store.set_root(root);

        store.gc();
        // Lost b:
        store.lookup(b).unwrap_err();
        // But not cool:
        store.lookup(cool).unwrap();
    }

    #[test]
    fn bytes() {
        let mut store = Storage::default();

        let b: Bytes = [1, 2, 3, 4, 5, 6, 7, 8];
        let ptr = store.put(b);
        assert_eq!(b, ptr.get().as_bytes().unwrap());

        let pair = store.put(Pair::cons(ptr, Ptr::nil()));
        store.set_root(pair);
        store.gc();
        let pair = store.root().get().as_pair().unwrap();
        let bytes = pair.car.get().as_bytes().unwrap();
        assert_eq!(bytes, b);
    }

    #[test]
    fn byte_vector() {
        let mut store = Storage::default();

        let b1: Bytes = [1, 0, 0, 0, 2, 0, 0, 0];
        let b2: Bytes = [3, 0, 0, 0, 4, 0, 0, 0];
        let vptr = store.put_vector([b1, b2].into_iter());

        let pair = store.put(Pair::cons(vptr, Ptr::nil()));
        store.set_root(pair);

        // Lookup before GC:
        {
            let bx = store.get_element_ptr(vptr, 1).unwrap();
            let b22 = bx.get().as_bytes().unwrap();
            assert_eq!(b2, b22);
        }

        store.gc();

        // Lookup after GC; should be preserved:
        {
            let Pair { car: vptr, .. } = store.root().get().as_pair().unwrap();
            let v = store.get(vptr).as_vector().unwrap();
            assert_eq!(v.length, 2);
            let bx = store.get_element_ptr(vptr, 1).unwrap();
            let b22 = store.get(bx).as_bytes().unwrap();
            assert_eq!(b2, b22);
        }
    }

    #[test]
    fn pair_vector() {
        let mut store = Storage::default();

        let one = store.put(1);
        let two = store.put(2);
        let vptr = store
            .put_vector([Pair::cons(one, Ptr::nil()), Pair::cons(Ptr::nil(), two)].into_iter());

        store.set_root(vptr);

        // Lookup before GC:
        {
            let bx = store.get_element_ptr(vptr, 1).unwrap();
            let p = bx.get().as_pair().unwrap();
            assert_eq!(p.car, Ptr::nil());
            assert_eq!(p.cdr, two);
        }

        store.gc();

        // Lookup after GC, one and two should be preserved:
        {
            let v = (store.root().get()).as_vector().unwrap();
            assert_eq!(v.length, 2);
            let onecell = (v.offset(0).unwrap().get()).as_pair().unwrap();
            let twocell = (v.offset(1).unwrap().get()).as_pair().unwrap();

            assert_eq!(onecell.cdr, Ptr::nil());
            assert_eq!(twocell.car, Ptr::nil());
            let got_one = (onecell.car.get()).as_integer().unwrap();
            assert_eq!(got_one, 1);
            let got_two = (twocell.cdr.get()).as_integer().unwrap();
            assert_eq!(got_two, 2);

            // And we'll check: we can hold on to an individual element, even after the vector is
            // discarded.
            store.set_root(v.offset(1).unwrap());
        }
        store.gc();

        let twocell = (store.root().get()).as_pair().unwrap();
        let got_two = (twocell.cdr.get()).as_integer().unwrap();
        assert_eq!(got_two, 2);
    }

    #[test]
    fn display_int() {
        let store = Storage::default();
        let v = store.put(10);
        assert_eq!(store.display(v.get()), "10");
    }

    #[test]
    fn display_float() {
        let store = Storage::default();
        let v = store.put(10.2);
        assert_eq!(store.display(v.get()), "10.2");
    }

    #[test]
    fn display_symbol() {
        let store = Storage::default();
        let v = store.put_symbol("hello");
        // Symbols are canonicalized to uppercase:
        assert_eq!(store.display(v.get()), "HELLO");
    }

    #[test]
    fn display_pair() {
        let store = Storage::default();
        let one = store.put(1);
        let two = store.put(2);
        let v = store.put(Pair::cons(one, two));
        // Symbols are canonicalized to uppercase:
        assert_eq!(store.display(v.get()), format!("({}, {})", one, two));
    }

    #[test]
    fn display_bytes() {
        let store = Storage::default();
        let v = store.put([1, 2, 3, 4, 0xa, 0xb, 0xc, 0xd]);
        // Symbols are canonicalized to uppercase:
        assert_eq!(store.display(v.get()), "0x[01, 02, 03, 04, 0a, 0b, 0c, 0d]",);
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
        assert_eq!(store.display(vo), format!("[{}, {}]", p0, p1));
    }

    #[test]
    fn display_nil() {
        let store = Storage::default();
        let vo = Ptr::nil().get();
        // Symbols are canonicalized to uppercase:
        assert_eq!(store.display(vo), "nil");
    }

    #[test]
    fn lookup_nil_ok() {
        let store = Storage::default();
        let ptr = store.lookup("nil#0").unwrap();
        assert_eq!(ptr, Ptr::nil());
    }

    #[test]
    fn lookup_object_ok() {
        let store = Storage::default();
        let v = store.put(1);
        let ptr = store.lookup(v.to_string()).unwrap();
        assert_eq!(ptr, v);
    }

    #[test]
    fn lookup_symbol_ok() {
        let store = Storage::default();
        let v = store.put_symbol("hello");
        let ptr = store.lookup(v.to_string()).unwrap();
        assert_eq!(ptr, v);
    }

    #[test]
    fn lookup_invalid_object() {
        let store = Storage::default();
        const INTS: &[char] = &['0', '1', '2', '3', '4', '5', '6', '7', '8'];
        let v = format!("{}", store.put(1)).replace(INTS, "9");
        store.lookup(v).unwrap_err();
    }

    #[test]
    fn lookup_invalid_symbol() {
        let v = Storage::default().put_symbol("hello").to_string();
        let new_store = Storage::default();
        new_store.lookup(v).unwrap_err();
    }
}
