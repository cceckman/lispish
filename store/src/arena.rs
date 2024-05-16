//! The arena for Lisp objects.
//!
//! This implementation uses a 4GiB arena:
//! 32-bit pointers, 8B-aligned, with 3b of tag.

use crate::{Object, StoredPair, StoredPtr, StoredValue};

const OBJECT_SIZE: usize = core::mem::size_of::<StoredValue>();
const PTR_SIZE: usize = core::mem::size_of::<StoredPtr>();

// Subtract out overheads from the arena size:
const ARENA_SIZE: u64 = 1u64 << (PTR_SIZE * 8);
// Space for `count`
const ARENA_OVERHEAD: u64 = core::mem::size_of::<u32>() as u64;
const EFFECTIVE_ARENA_SIZE: u64 = ARENA_SIZE - ARENA_OVERHEAD;
const MAX_OBJECT_COUNT: usize = (EFFECTIVE_ARENA_SIZE / OBJECT_SIZE as u64) as usize;

/// Pick a more modest size to begin with.
const OBJECT_COUNT: usize = 4096;

type ArenaStore = [StoredValue; OBJECT_COUNT];

pub struct Arena {
    objects: ArenaStore,
    count: u32,
}

impl Arena {
    const fn new() -> Self {
        // Index 0 is always reserved for the nil pointer.
        // ...which has a _valid_ tombstone, that also points to index 0
        // in the next generation - semantically accurate too!
        Self {
            objects: [StoredValue { tombstone: 0 }; OBJECT_COUNT],
            count: 1,
        }
    }
}

impl Arena {
    /// Stores the Lisp object in storage.
    pub fn put_object(&mut self, object: Object) -> StoredPtr {
        let (stored, tag) = object.into();
        let idx = self.put(stored);
        StoredPtr::new(idx, tag)
    }

    /// Stores the Lisp object in storage.
    pub fn put(&mut self, stored: StoredValue) -> usize {
        let slot = self.count as usize;
        self.objects[slot] = stored;
        self.count += 1;
        slot
    }

    pub fn get(&self, idx: usize) -> StoredValue {
        assert_ne!(idx, 0);
        assert!(idx < self.count as usize);
        self.objects[idx]
    }

    /// Get a reference to the slot with the given index.
    pub fn get_ref(&mut self, idx: usize) -> &mut StoredValue {
        assert_ne!(idx, 0);
        assert!(idx < self.count as usize);
        &mut self.objects[idx]
    }

    /// Retrieve the tombstone value.
    pub fn get_next(&self, idx: usize) -> usize {
        // Allow 0: it's a valid `tombstone` entry.
        assert!(idx < self.count as usize);
        unsafe { self.objects[idx].tombstone }
    }

    /// Retrieve the tombstone value, forwarding the pointer tag.
    pub fn get_next_ptr(&self, ptr: StoredPtr) -> StoredPtr {
        let idx = self.get_next(ptr.idx());
        StoredPtr::new(idx, ptr.tag())
    }

    pub fn update(&mut self, ptr: StoredPtr, pair: StoredPair) {
        let idx = ptr.idx();
        assert!(idx < self.count as usize);
        self.objects[idx].pair = pair;
    }

    pub fn len(&self) -> usize {
        // Discount one object: the reserved 'nil' index
        self.count as usize
    }

    /// Replace this object with a tombstone entry.
    pub fn set_next(&mut self, old_idx: usize, new_idx: usize) {
        assert!(old_idx < self.count as usize);
        self.objects[old_idx].tombstone = new_idx
    }
}

/// The generic Arenas object,
/// which works over either allocated or static Arena objects.
pub struct GenericArenas<T> {
    // The arenas are distinct to please the borrow-checker,
    // which understands split borrows of _fields_ but not _slices_.
    arena_0: T,
    arena_1: T,
    generation: usize,
}

#[cfg(feature = "std")]
pub type Arenas = GenericArenas<Box<Arena>>;

/// Trait for getting a new Arena to start off with.
pub trait ArenaInit {
    fn new(idx: usize) -> Self;
}

impl ArenaInit for Box<Arena> {
    fn new(_idx: usize) -> Self {
        Box::new(Arena::new())
    }
}

impl<T> Default for GenericArenas<T>
where
    T: ArenaInit,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> GenericArenas<T>
where
    T: ArenaInit,
{
    fn new() -> Self {
        Self {
            generation: 0,
            arena_0: T::new(0),
            arena_1: T::new(1),
        }
    }
}

impl<T> GenericArenas<T>
where
    T: AsRef<Arena> + AsMut<Arena>,
{
    pub fn current_mut(&mut self) -> &mut Arena {
        if self.generation % 2 == 0 {
            self.arena_0.as_mut()
        } else {
            self.arena_1.as_mut()
        }
    }

    pub fn current(&self) -> &Arena {
        if self.generation % 2 == 0 {
            self.arena_0.as_ref()
        } else {
            self.arena_1.as_ref()
        }
    }

    pub fn generation(&self) -> usize {
        self.generation
    }

    /// Move to the next generation, and get the previous/current generations.
    pub fn increment_generation(&mut self) -> (&mut Arena, &mut Arena) {
        self.generation += 1;
        if self.generation % 2 == 0 {
            self.arena_0.as_mut().count = 1;
            (self.arena_1.as_mut(), self.arena_0.as_mut())
        } else {
            self.arena_1.as_mut().count = 1;
            (self.arena_0.as_mut(), self.arena_1.as_mut())
        }
    }
}
