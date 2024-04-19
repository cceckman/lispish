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
};
mod objects;
pub use objects::*;

use self::bitset::BitSet;

/// Storage allows representing all persistent objects.
#[derive(Default)]
pub struct Storage {
    generation: RefCell<Generation>,

    high_water: StorageStats,
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
    fn put(&mut self, value: impl Into<Object>) -> Ptr {
        let object = value.into();
        let (stored, tag) = object.into();
        {
            // Canonicalize nil to 0; don't store.
            let zerop = Ptr::new(0, tag);
            if zerop.is_nil() {
                return zerop;
            }
        }

        let slot = self.objects.len();
        self.objects.push(stored);
        Ptr::new(slot, tag)
    }

    fn put_string(&mut self, content: &[u8]) -> Ptr {
        let offset = self.string_data.len() as u32;
        self.string_data.extend_from_slice(content);
        let s = LString {
            offset,
            length: content.len() as u32,
        };
        self.put(Object::String(s))
    }

    fn get(&self, ptr: Ptr) -> Object {
        if ptr.is_nil() {
            return Object::Nil;
        }

        let idx = ptr.idx() as usize;
        assert!(idx < self.objects.len());
        (self.objects[idx], ptr.tag()).into()
    }
}

impl Storage {
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
    pub fn put_symbol(&self, symbol: &str) -> Ptr {
        let mut gen = self.generation.borrow_mut();
        let s = Symbol {
            symbol: gen.symbols.get_or_intern(symbol),
        };
        gen.put(Object::Symbol(s))
    }

    /// Add a string to the string content.
    pub fn put_string(&self, content: &[u8]) -> Ptr {
        let mut gen = self.generation.borrow_mut();
        gen.put_string(content)
    }

    /// Resolve a string to its binary contents.
    pub fn get_string<'a>(&'a self, s: &LString) -> Ref<'a, [u8]> {
        let gen = self.generation.borrow();
        Ref::map(gen, |v| &v.string_data[s.range()])
    }

    /// Stores the Lisp object in storage.
    pub fn put(&self, value: impl Into<Object>) -> Ptr {
        self.generation.borrow_mut().put(value)
    }

    pub fn get(&self, ptr: Ptr) -> Object {
        self.generation.borrow().get(ptr)
    }

    /// Run a garbage-collection pass, based on the provided roots.
    ///
    /// All pointers in the environment should be passed in via roots.
    /// Pointers can change across a GC pass; the GC routine will fix up those in storage and those in `roots`.
    pub fn gc<const NROOTS: usize>(self, roots: [Ptr; NROOTS]) -> (Storage, [Ptr; NROOTS]) {
        let mut last_gen = self.generation.into_inner();
        // TODO: Add trace output for debug

        let high_water = StorageStats {
            // Update stats before compaction:
            objects: max(self.high_water.objects, last_gen.objects.len()),
            string_data: max(self.high_water.string_data, last_gen.string_data.len()),
            symbols: max(self.high_water.symbols, last_gen.symbols.len()),
        };

        let mut live_objects = BitSet::new();
        let mut queue: VecDeque<Ptr> = roots.iter().cloned().collect();

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
        while let Some(old_ptr) = queue.pop_front() {
            let old_idx = old_ptr.idx();
            if live_objects.get(old_idx) {
                continue;
            }
            live_objects.set(old_idx);

            let got = last_gen.get(old_ptr);
            match got {
                // Check recursive structures:
                Object::Pair(p) => {
                    for rp in [p.car, p.cdr] {
                        if !rp.is_nil() && !live_objects.get(rp.idx()) {
                            queue.push_back(rp);
                        }
                    }
                }
                Object::String(s) => {
                    string_length += s.length as usize;
                }
                _ => (),
            }

            // We've gotten what data we need.
            // Copy over, and leave a tombstone:
            let new_ptr = next_gen.put(got);
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
        let mut new_roots: [Ptr; NROOTS] = [Ptr::default(); NROOTS];
        for (old_ptr, new_ptr) in roots.iter().zip(new_roots.iter_mut()) {
            queue.push_back(*old_ptr);
            // All "live" objects in the old arena now contain a tombstone entry,
            // their index in the new arena.
            let new_idx = unsafe { last_gen.objects[old_ptr.idx()].tombstone };
            *new_ptr = Ptr::new(new_idx, old_ptr.tag());
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
                for rp in [&mut pair.car, &mut pair.cdr] {
                    // We'll need to recurse, based on the _old_ pointer:
                    queue.push_back(*rp);
                    // And lookup + update the children - to the _new_ pointers:
                    let new_cr = unsafe { last_gen.objects[rp.idx()].tombstone };
                    *rp = Ptr::new(new_cr, rp.tag());
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

        // OK; we've done our two-passes-over-every-object. Whew!
        (
            Storage {
                high_water,
                generation: RefCell::new(next_gen),
            },
            new_roots,
        )
    }
}

#[derive(Clone, Copy)]
#[repr(align(8))]
union StoredValue {
    integer: Integer,
    float: Float,

    pair: Pair,
    symbol: Symbol,
    string: LString,

    /// Pointer into the "next" arena, for copied-out objects.
    tombstone: usize,
}

#[cfg(test)]
mod tests {
    use core::panic;

    use crate::data::{Pair, Ptr};

    use super::{Object, Storage};

    #[test]
    fn gc_numbers() {
        let store = Storage::default();

        let one = store.put(Object::Integer(1));
        let _ = store.put(Object::Float(3.0));
        let two = store.put(Object::Float(2.0));
        assert_eq!(store.current_stats().objects, 3);

        let (store, ptrs) = store.gc([one, two]);
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
        let store = Storage::default();

        const A: &[u8] = b"this is string A";
        const B: &[u8] = b"this is what I call string B";
        const C: &[u8] = b"this is what I call podracing!";

        let ptrs: [Ptr; 3] = [A, B, C].map(|b| store.put_string(b));
        assert_eq!(store.current_stats().objects, 3);
        assert_eq!(
            store.current_stats().string_data,
            A.len() + B.len() + C.len()
        );

        let (store, ptrs) = store.gc(ptrs);
        assert_eq!(store.current_stats().objects, 3);
        if let Object::String(s) = store.get(ptrs[1]) {
            assert_eq!(store.get_string(&s).as_ref(), B);
        } else {
            panic!("unexpected object: {:?}", store.get(ptrs[1]));
        }
        let (store, new_ptrs) = store.gc([ptrs[1], ptrs[2]]);
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
        let store = Storage::default();

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
        let (store, stack) = {
            let pre_stats = store.current_stats();
            let (store, stack) = store.gc(stack);
            assert_eq!(store.current_stats(), pre_stats);
            (store, stack)
        };

        let (store, [stack_top]) = store.gc([stack[0]]);
        // ('b b ()): objects are b, (b ()), and (b (b ()))
        // ...why is this not working :(
        assert_eq!(store.current_stats().string_data, B.len());
        assert_eq!(store.current_stats().objects, 3);

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
