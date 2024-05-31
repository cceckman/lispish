//! The arena for Lisp objects.
//!
//! This implementation uses a 4GiB arena:
//! 32-bit pointers, 8B-aligned, with 3b of tag.

use crate::bitset::BitSet;
#[cfg(feature = "std")]
use crate::ObjectFormats;
use core::mem::MaybeUninit;

use crate::{
    bitset::{words_for_bits, ArrayBitSet},
    Object, StoredPair, StoredPtr, StoredValue,
};

mod gc;

mod static_cell;

#[cfg(not(feature = "std"))]
mod static_data;

#[cfg(not(feature = "std"))]
pub use static_data::*;

#[cfg(feature = "std")]
mod dynamic_data;
#[cfg(feature = "std")]
pub use dynamic_data::*;

/// The interface to Generations,
/// the backing store for Storage without lifetime constraints.
pub trait GenerationsAccess {
    /// Get the current generation mutably.
    fn current_mut(&mut self) -> &mut Generation;

    /// Get the current generation immutably.
    fn current(&self) -> &Generation;

    /// Get the generation count.
    fn generation(&self) -> usize;
}

#[cfg(feature = "std")]
pub trait Generations: GenerationsAccess {
    fn gc(
        &mut self,
        roots: &mut [&mut StoredPtr],
        #[cfg(feature = "render")] labels: &mut ObjectFormats,
    );
}

#[cfg(not(feature = "std"))]
pub trait Generations {
    fn gc(&mut self, roots: &mut [&mut StoredPtr]);
}

const OBJECT_SIZE: usize = core::mem::size_of::<StoredValue>();
const BITS_PER_BYTE: usize = u8::BITS as usize;

/// Compute the number of objects available per generation,
/// based on the amount of memory available.
///
/// Given M bytes of memory, we allocate them as follows:
/// - N objects per generation
/// - bpb bits per byte
/// - osize bytes per object
/// $$
/// 2 * osize * n + ceil(N / bpb) = M
/// (2 * osize * bpb) * N  / bpb + ceil(N / bpb) = M
/// (2 * osize * bpb + 1) * N / bpb = M
/// N = floor(bpb * M / (2 * osize * bpb + 1)
const fn objects_per_generation(memory: usize) -> usize {
    BITS_PER_BYTE * memory / (2 * OBJECT_SIZE * BITS_PER_BYTE + 1)
}

/// A relatively conservative allocation to begin with.
// TODO: Make this configurable.
const MEMORY_SIZE: usize = 1 * 1024 * 1024;

const OBJECT_COUNT: usize = objects_per_generation(MEMORY_SIZE);
const BITSET_WORDS: usize = words_for_bits(OBJECT_COUNT);

pub type GenerationStore = [StoredValue; OBJECT_COUNT];
type Bitset = ArrayBitSet<BITSET_WORDS>;

pub struct Generation {
    objects: GenerationStore,
    count: u32,
}

/// Trait that allows relatively-lazy initialization of memory.
/// A type implementing Init can turn a MaybeUninit into a real ~~boy~~ Self.
trait Init: Sized {
    fn init(this: &mut MaybeUninit<Self>) -> &mut Self;
}

impl Init for Generation {
    fn init(this: &mut MaybeUninit<Self>) -> &mut Self {
        let m = unsafe { this.assume_init_mut() };
        // Reserve index 0 for nil;
        // it's always a tombstone pointing to 0.
        m.objects[0].tombstone = StoredPtr::default();
        m.count = 1;
        m
    }
}

impl Init for Bitset {
    fn init(this: &mut MaybeUninit<Self>) -> &mut Self {
        let bitset = unsafe { this.assume_init_mut() };
        bitset.clear_all();
        bitset
    }
}

impl Generation {
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
        assert!(idx < self.count as usize);
        self.objects[idx]
    }

    /// Get a reference to the slot with the given index.
    pub fn get_ref(&mut self, idx: usize) -> &mut StoredValue {
        assert!(idx < self.count as usize);
        &mut self.objects[idx]
    }

    /// Retrieve the tombstone value.
    pub fn get_next(&self, idx: usize) -> StoredPtr {
        // Allow 0: it's a valid `tombstone` entry.
        assert!(idx < self.count as usize);
        unsafe { self.objects[idx].tombstone }
    }

    pub fn update(&mut self, ptr: StoredPtr, pair: StoredPair) {
        let idx = ptr.idx();
        assert!(idx < self.count as usize);
        self.objects[idx].pair = pair;
    }

    pub fn len(&self) -> usize {
        self.count as usize
    }
}

/// The generic Generations collection,
/// which works over either allocated or static objects.
/// (This allows us to have a GenericGenerations on the stack
/// in a hosted environment.)
pub struct GenericGenerations<GenerationT, BitsetT> {
    // The generations are distinct to please the borrow-checker,
    // which understands split borrows of _fields_ but not _slices_.
    gen_0: GenerationT,
    gen_1: GenerationT,
    bitset: BitsetT,
    generation: usize,
}

impl<T, B> GenerationsAccess for GenericGenerations<T, B>
where
    T: AsRef<Generation> + AsMut<Generation>,
    B: AsRef<Bitset> + AsMut<Bitset>,
{
    fn current_mut(&mut self) -> &mut Generation {
        if self.generation % 2 == 0 {
            self.gen_0.as_mut()
        } else {
            self.gen_1.as_mut()
        }
    }

    fn current(&self) -> &Generation {
        if self.generation % 2 == 0 {
            self.gen_0.as_ref()
        } else {
            self.gen_1.as_ref()
        }
    }

    fn generation(&self) -> usize {
        self.generation
    }
}
