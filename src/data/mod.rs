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

use std::{cmp::max, collections::VecDeque};
mod objects;
pub use objects::*;

use self::bitset::BitSet;

/// Storage allows representing all persistent objects.
#[derive(Default)]
pub struct Storage {
    objects: Vec<StoredValue>,
    string_data: Vec<u8>,

    // TODO: Understand & implement this myself.
    symbols: string_interner::DefaultStringInterner,

    high_water: StorageStats,
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

impl Storage {
    pub fn current_stats(&self) -> StorageStats {
        StorageStats {
            objects: self.objects.len(),
            string_data: self.string_data.len(),
            symbols: self.symbols.len(),
        }
    }
    pub fn max_stats(&self) -> StorageStats {
        self.high_water
    }

    /// Add a symbol to the symbol table.
    pub fn put_symbol(&mut self, symbol: &str) -> Ptr {
        let s = Symbol {
            symbol: self.symbols.get_or_intern(symbol),
        };
        self.put(Object::Symbol(s))
    }

    /// Add a string to the string content.
    pub fn put_string(&mut self, content: &[u8]) -> Ptr {
        let offset = self.string_data.len() as u32;
        self.string_data.extend_from_slice(content);
        let s = LString {
            offset,
            length: content.len() as u32,
        };
        self.put(Object::String(s))
    }

    /// Resolve a string to its binary contents.
    pub fn get_string(&self, s: &LString) -> &[u8] {
        &self.string_data[s.range()]
    }

    /// Stores the Lisp object in storage.
    pub fn put(&mut self, value: impl Into<Object>) -> Ptr {
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

    pub fn get(&self, ptr: Ptr) -> Object {
        if ptr.is_nil() {
            return Object::Nil;
        }

        let idx = ptr.idx() as usize;
        assert!(idx < self.objects.len());
        (self.objects[idx], ptr.tag()).into()
    }

    /// Run a garbage-collection pass, based on the provided roots.
    ///
    /// All pointers in the environment should be passed in via roots.
    /// Pointers can change across a GC pass; the GC routine will fix up those in storage and those in `roots`.
    pub fn gc(&mut self, roots: &mut [Ptr]) {
        // TODO: Add trace output for debug

        // Update stats before compaction:
        self.high_water.objects = max(self.high_water.objects, self.objects.len());
        self.high_water.string_data = max(self.high_water.string_data, self.string_data.len());
        self.high_water.symbols = max(self.high_water.symbols, self.symbols.len());

        let mut live_objects = BitSet::new();
        let mut queue: VecDeque<Ptr> = roots.iter().cloned().collect();

        // We'll never shrink below our number of live objects at _last_ GC.
        // We could apply some hysteresis here, but... eh, TODO.
        let mut new_arena = Vec::with_capacity(self.objects.len());
        let mut string_length = 0usize;

        // First pass:
        // -    Move all objects to the new arena.
        // -    Total up how much space we'll need for strings.
        while let Some(old_ptr) = queue.pop_front() {
            let old_idx = old_ptr.idx();
            if live_objects.get(old_idx) {
                continue
            }
            live_objects.set(old_idx);

            // Check all recursive structures:
            if let Object::Pair(p) = self.get(old_ptr) {
                for rp in [p.car, p.cdr] {
                    if !rp.is_nil() && !live_objects.get(rp.idx()) {
                        queue.push_back(rp);
                    }
                }
            }
            // ...but strings form an external reference.
            if let Object::String(s) = self.get(old_ptr) {
                string_length += s.length as usize;
            }

            // We've gotten what data we need.
            // Copy over, and leave a tombstone:
            let new_idx = new_arena.len();
            new_arena.push(self.objects[old_ptr.idx()]);
            self.objects[old_ptr.idx()].tombstone = new_idx;
        }

        // We have three more steps:
        // -    We need to update the argument, the Vec<Ptr>,
        //      to have the new indices. Fairly simple.
        // -    We need to update all the heap pointers to reflect their
        //      new indices - a second walk.
        // -    And we need to copy the string contents.
        // First case is easy, let's do it right quick,
        // while also forming the "new old pointers" list we'll need to update later.
        queue.clear();
        for old_ptr in roots.iter_mut() {
            queue.push_back(*old_ptr);
            // All "live" objects in the old arena now contain a tombstone entry,
            // their index in the new arena.
            let new_idx = unsafe { self.objects[old_ptr.idx()].tombstone };
            let new_ptr = Ptr::new(new_idx, old_ptr.tag());
            *old_ptr = new_ptr;
        }

        // Now we have a list of "old" pointers in the heap to go through.
        let mut new_string = Vec::with_capacity(string_length);
        while let Some(old_ptr) = queue.pop_front() {
            if live_objects.get(old_ptr.idx()) {
                // We haven't visited this on the second pass yet.
                live_objects.clear(old_ptr.idx());
            } else {
                continue;
            }

            if old_ptr.is_pair() {
                // This is a pair; we need to update its inner pointers,
                let new_idx = unsafe { self.objects[old_ptr.idx()].tombstone };
                let pair = unsafe { &mut new_arena[new_idx].pair };
                for rp in [&mut pair.car, &mut pair.cdr] {
                    // We'll need to recurse, based on the _old_ pointer:
                    queue.push_back(*rp);
                    // And lookup + update the children - to the _new_ pointers:
                    let new_cr = unsafe { self.objects[rp.idx()].tombstone };
                    *rp = Ptr::new(new_cr, rp.tag());
                }
            }
            if old_ptr.is_string() {
                // Copy the string to the new string buffer.
                let new_idx = unsafe { self.objects[old_ptr.idx()].tombstone };
                let s = unsafe { &mut new_arena[new_idx].string };
                let content = &self.string_data[s.range()];
                s.offset = new_string.len() as u32;
                new_string.extend_from_slice(content);
            }
        }

        // OK; we've done our two-passes-over-every-object. Whew!
        self.objects = new_arena;
        self.string_data = new_string;
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
        let mut store = Storage::default();

        let one = store.put(Object::Integer(1));
        let _ = store.put(Object::Float(3.0));
        let two = store.put(Object::Float(2.0));
        assert_eq!(store.current_stats().objects, 3);

        let mut ptrs = vec![one, two];
        store.gc(&mut ptrs);
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

        const A : &[u8] = b"this is string A";
        const B : &[u8] = b"this is what I call string B";
        const C : &[u8] = b"this is what I call podracing!";

        let mut ptrs : Vec<Ptr> = [A, B, C].iter().map(|b| store.put_string(b)).collect();
        assert_eq!(store.current_stats().objects, 3);
        assert_eq!(store.current_stats().string_data, A.len() + B.len() + C.len());

        store.gc(&mut ptrs);
        assert_eq!(store.current_stats().objects, 3);
        if let Object::String(s) = store.get(ptrs[1]) {
            assert_eq!(store.get_string(&s), B);
        } else {
            panic!("unexpected object: {:?}", store.get(ptrs[1]));
        }
        let new_ptrs = &mut ptrs[1..];
        store.gc(new_ptrs);
        assert_eq!(store.current_stats().objects, 2);
        assert_eq!(store.current_stats().string_data, B.len() + C.len());

        if let Object::String(s) = store.get(new_ptrs[1]) {
            assert_eq!(store.get_string(&s), C);
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

        let mut stack = Vec::new();

        // '(a a b) in one list; '(b b) in another, using the same final cell.
        {
            let ls1 = store.put(Pair::cons(b, Object::nil()));
            let lsa1 = store.put(Pair::cons(a, ls1));
            let lsa = store.put(Pair::cons(a, lsa1));

            let lsb = store.put(Pair::cons(b, ls1));

            stack.push(lsb);
            stack.push(lsa);
        }
        assert_eq!(store.current_stats().objects, 6);
        assert_eq!(store.current_stats().string_data, A.len() + B.len());
        {
            let pre_stats = store.current_stats();
            store.gc(&mut stack);
            assert_eq!(store.current_stats(), pre_stats);
        }

        stack.pop();
        store.gc(&mut stack);
        // ('b b ()): objects are b, (b ()), and (b (b ()))
        // ...why is this not working :(
        assert_eq!(store.current_stats().string_data, B.len());
        assert_eq!(store.current_stats().objects, 3);

        let top = store.get(stack.pop().unwrap());
        // This should be the root of the B tree:
        let (car, cdr) = match top {
            Object::Pair(Pair{car, cdr}) => (car, cdr),
            _ => panic!("unexpected object: {:?}", top),
        };
        let (car, cdr) = match (store.get(car), store.get(cdr)) {
            (Object::String(ls), Object::Pair(Pair{car, cdr})) => {
                let s = store.get_string(&ls);
                assert_eq!(s, B);
                (car, cdr)
            }
            _ => panic!("unexpected object: {:?}", top),
        };
        match (store.get(car), store.get(cdr)) {
            (Object::String(ls), Object::Nil) => {
                let s = store.get_string(&ls);
                assert_eq!(s, B);
            }
            _ => panic!("unexpected object: {:?}", top),
        };
    }
}
