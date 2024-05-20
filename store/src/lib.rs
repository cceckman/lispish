#![cfg_attr(not(feature = "std"), no_std)]
//! Lisp data types and allocators.
//!
//!
//! ## Revised design
//!
//! The Lisp store is backed by an arena allocator of up to ~4000MiB.
//! (Yes, not 4GiB- the difference allows for certain overheads.)
//!
//! The store provides:
//! - pointer-tagged storage:
//!     - `put` methods store objects, and return pointers (Ptr).
//!        Pointers carry the type of the object.
//!        `Ptr::get()` retrieves the stored object.
//! - A symbol table: a persistent, uniquified list of uppercase strings.
//! - A stack.
//! - Garbage collection, only when no pointers are outstanding.
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

mod arena;
mod bitset;
mod bitset2;
mod gc;
mod objects;
#[cfg(feature = "render")]
mod render;
mod symbols;
mod tag;
mod utility;
mod vectors;

pub mod strings;
pub use self::objects::*;
#[cfg(feature = "render")]
pub use self::render::ObjectFormat;
pub use self::tag::*;
pub use self::vectors::ByteVector;

use self::arena::Arenas;
#[cfg(feature = "render")]
use self::render::ObjectFormats;
use self::strings::to_bytes;

use core::cell::{RefCell, RefMut};
use core::cmp::max;
use core::ops::DerefMut;

/// A zero-allocation error type.
pub struct Error<'a> {
    message: &'static str,
    ptr: Ptr<'a>,
}

impl<'a> Error<'a> {
    pub const fn new(format: &'static str, ptr: Ptr<'a>) -> Self {
        Error {
            message: format,
            ptr,
        }
    }
}

impl core::fmt::Debug for Error<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "for object {}: {}", self.ptr, self.message)
    }
}

impl core::fmt::Display for Error<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "for object {}: {}", self.ptr, self.message)
    }
}

/// Storage allows representing all persistent objects.
pub struct Storage {
    /// Root of the main object tree.
    root: RefCell<StoredPtr>,

    /// Auxiliary object tree: the symbol table.
    /// A vector of strings.
    /// (Note: try to re-GC after declaring each symbol!)
    symbols: RefCell<StoredPtr>,

    high_water: StorageStats,

    /// Node metadata.
    /// These provide useful debugging info, like "this is the root of the stack".
    #[cfg(feature = "render")]
    labels: RefCell<ObjectFormats>,

    arenas: RefCell<Arenas>,
}

impl Default for Storage {
    fn default() -> Self {
        let s = Self {
            root: Default::default(),
            symbols: Default::default(),
            high_water: Default::default(),
            #[cfg(feature = "render")]
            labels: Default::default(),
            arenas: Default::default(),
        };
        let symbols = s.put_vector::<Pair>(core::iter::empty());
        *s.symbols.borrow_mut() = symbols.raw;
        s
    }
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Eq)]
pub struct StorageStats {
    pub objects: usize,
    pub symbols: usize,
    pub generation: usize,
}

impl StorageStats {
    fn max(&self, other: &StorageStats) -> StorageStats {
        StorageStats {
            // Update stats before compaction:
            objects: max(self.objects, other.objects),
            symbols: max(self.symbols, other.symbols),
            generation: max(self.generation, other.generation),
        }
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

        let arenas = self.arenas.borrow();
        let objects = arenas.current().len();
        let generation = arenas.generation();

        StorageStats {
            objects,
            symbols,
            generation,
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
    pub fn put_vector<T>(&self, mut v: impl Iterator<Item = T>) -> Ptr
    where
        T: UniformVector,
    {
        // We have to acquire & release borrow_mut repeatedly here,
        // because "get the object" on the iterator may require borrowing
        // the generation to resolve the object.
        let mut count = 0;
        let first_idx = v
            .next()
            .map(|x| {
                count += 1;
                self.arenas.borrow_mut().current_mut().put(x.store())
            })
            .unwrap_or(0);
        for object in v {
            count += 1;
            self.arenas.borrow_mut().current_mut().put(object.store());
        }
        let mut arenas = self.arenas.borrow_mut();
        let gen = arenas.current_mut();
        let vec = StoredVector {
            length: count as u32,
            start: StoredPtr::new(first_idx, T::tag()),
        };
        let p = StoredPtr::new(gen.put(StoredValue { vector: vec }), Tag::Vector);
        self.bind(p)
    }

    /// Get a pointer-to-an-element from a vector.
    /// Returns none if v is not a vector or if the index is out-of-range.
    pub fn get_element_ptr(&self, v: Ptr, idx: u32) -> Option<Ptr> {
        let mut arena = self.arenas.borrow_mut();
        let stored_vector = arena.current_mut().get(v.raw.idx()).as_vector(v.raw)?;
        let ptr = stored_vector.offset(idx)?;
        Some(self.bind(ptr))
    }

    /// Replace the given pair with a new one.
    /// This is the only form of update permitted,
    /// since it is sufficient to rebind variables.
    pub fn update(&self, ptr: Ptr, object: Pair) {
        assert!(ptr.is_pair());
        let mut arena = self.arenas.borrow_mut();
        arena.current_mut().update(ptr.raw, object.into());
    }

    /// Stores the Lisp object in storage.
    pub fn put<'a>(&'a self, value: impl Into<Object<'a>>) -> Ptr<'a> {
        let value = value.into();
        if let Object::Nil = value {
            return Ptr::default();
        }
        let mut arena = self.arenas.borrow_mut();
        let raw = arena.current_mut().put_object(value);
        self.bind(raw)
    }

    pub fn get<'a>(&'a self, ptr: Ptr<'a>) -> Object<'a> {
        if ptr.is_nil() {
            Object::Nil
        } else if ptr.is_symbol() {
            Object::Symbol(Symbol::bind(self, ptr.idx()))
        } else {
            let stored = self.arenas.borrow_mut().current().get(ptr.raw.idx());
            Object::bind(self, (ptr.raw, stored))
        }
    }

    /// Peek at the top of the stack.
    pub fn push(&self, ptr: Ptr) {
        let p: Ptr = self.bind(*self.root.borrow());
        let pair = self.put(Pair::cons(ptr, p));
        *self.root.borrow_mut() = pair.raw;
    }

    /// Peek at the top of the stack.
    pub fn pop(&self) -> Ptr {
        let p: Ptr = self.bind(*self.root.borrow());
        let pair = p.get().as_pair().unwrap();
        *self.root.borrow_mut() = pair.cdr.raw;
        pair.car
    }

    /// Peek at the top of the stack.
    pub fn peek(&self) -> Ptr {
        let p: Ptr = self.bind(*self.root.borrow());
        let pair = p.get().as_pair().unwrap();
        pair.car
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
        let mut arenas = self.arenas.borrow_mut();
        let (last, next) = arenas.increment_generation();
        let mut root = self.root.borrow_mut();
        let mut symbols = self.symbols.borrow_mut();
        let mut labels = self.labels.borrow_mut();

        // We intentionally put the symbol table first,
        // so that nice ~stable vector can land early.
        let mut roots = [symbols.deref_mut(), root.deref_mut()];

        gc::gc(
            last,
            next,
            &mut roots,
            #[cfg(feature = "render")]
            &mut labels,
        );

        tracing::trace!("stats after GC: {:?}", self.current_stats());
    }

    /// Look up an object in storage by a stringified pointer.
    ///
    /// `Ptr` cannot "just" implement `FromStr` because it cannot correctly infer
    /// the lifetime. This function validates the pointer's range and binds it to
    /// this arena's lifetime.
    ///
    /// Note, though, this does not and cannot check the type of the pointer;
    /// we're trusting that the tag in the string matches the actual object.
    #[cfg(feature = "std")]
    pub fn lookup(&self, object_id: impl AsRef<str>) -> Result<Ptr<'_>, String> {
        let stats = self.current_stats();
        let stored: StoredPtr = object_id.as_ref().parse()?;
        let max_obj = self.arenas.borrow().current().len();
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

#[cfg(feature = "std")]
impl core::str::FromStr for StoredPtr {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some((tag, number)) = s.split_once('#') {
            let tag = match tag {
                "nil" => Tag::Nil,
                "int" => Tag::Integer,
                "flt" => Tag::Float,
                "sym" => Tag::Symbol,
                "obj" => Tag::Pair,
                "vec" => Tag::Vector,
                "byt" => Tag::Bytes,
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

impl core::fmt::Display for StoredPtr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let tag = match self.tag() {
            Tag::Nil => "nil",
            Tag::Integer => "int",
            Tag::Float => "flt",
            Tag::Symbol => "sym",
            Tag::Pair => "obj",
            Tag::Bytes => "byt",
            Tag::Vector => "vec",
        };
        write!(f, "{}#{}", tag, self.idx())
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

impl core::fmt::Debug for StoredPtr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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

#[cfg(all(test, feature = "std"))]
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

        store.push(store.put(Pair::cons(one, two)));
        let pre_stats = store.current_stats();
        store.gc();

        assert_eq!(store.current_stats().objects, pre_stats.objects - 1);

        let Pair { car, cdr } = store
            .peek()
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

        store.push(store.put(stack));
        let pre_stats = store.current_stats();
        store.gc();
        assert_eq!(store.current_stats().objects, pre_stats.objects);
        assert_eq!(store.current_stats().symbols, pre_stats.symbols);

        let Pair { cdr: lsb, .. } = store
            .get(store.pop())
            .try_into()
            .expect("root should be a pair");
        store.push(lsb);
        // Objects are:
        // b
        // (b ())
        // (b (b ()))
        // with no additional root (we kept one of the branches as the root.)
        store.gc();
        let stack_top = store.peek();
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
        store.push(root);

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
        store.push(pair);
        store.gc();
        let pair = store.peek().get().as_pair().unwrap();
        let bytes = pair.car.get().as_bytes().unwrap();
        assert_eq!(bytes, b);
    }

    #[test]
    fn byte_vector() {
        let mut store = Storage::default();

        let b1: Bytes = [1, 0, 0, 0, 2, 0, 0, 0];
        let b2: Bytes = [3, 0, 0, 0, 4, 0, 0, 0];
        let vptr = store.put_vector([b1, b2].into_iter());

        store.push(vptr);

        // Lookup before GC:
        {
            let bx = store.get_element_ptr(vptr, 1).unwrap();
            let b22 = bx.get().as_bytes().unwrap();
            assert_eq!(b2, b22);
        }

        store.gc();

        // Lookup after GC; should be preserved:
        {
            let vptr = store.peek();
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

        store.push(vptr);

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
            let v = (store.peek().get()).as_vector().unwrap();
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
            store.push(v.offset(1).unwrap());
        }
        store.gc();

        let twocell = (store.peek().get()).as_pair().unwrap();
        let got_two = (twocell.cdr.get()).as_integer().unwrap();
        assert_eq!(got_two, 2);
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
