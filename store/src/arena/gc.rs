/// GC implementation for the Cheney-derived arena.
///
/// ## Queue pass
///
/// In the first pass, perform a breadth-first traversal of the tree,
/// placing _old pointers_ into the _new generation_, and marking the bitset.
///
/// ## Swap pass
///
/// For each object in the new generation,
/// swap the object into the new generation,
/// and leave a pointer to the new generation in the old generation.
///
/// ## Fixup pass
///
/// For each bit in the bitset, find a pointer in the corresponding slot
/// in the old generation; it is a pointer to the new generation.
/// Patch the object in the new generation by looking at the object in the
/// new generation, resolving any contained pointers to tombstones,
/// and replacing them.
use super::*;
use crate::{bitset::BitSet, Tag};

#[cfg(feature = "render")]
use crate::render::ObjectFormats;

impl<T, B> Generations for GenericGenerations<T, B>
where
    T: AsRef<Generation> + AsMut<Generation>,
    B: AsRef<Bitset> + AsMut<Bitset>,
{
    fn gc(
        &mut self,
        roots: &mut [&mut StoredPtr],
        #[cfg(feature = "std")] labels: &mut ObjectFormats,
    ) {
        self.queue_pass(roots);
        self.swap_pass();

        #[cfg(feature = "std")]
        self.fixup_labels(labels);

        self.fixup_pass(roots);

        // TODO: here:
        // - Fix labels

        self.generation += 1;
        todo!();
    }
}

impl<T, B> GenericGenerations<T, B>
where
    T: AsRef<Generation> + AsMut<Generation>,
    B: AsRef<Bitset> + AsMut<Bitset>,
{
    fn queue_pass(&mut self, roots: &mut [&mut StoredPtr]) {
        let (current, next) = if self.generation % 2 == 0 {
            (self.gen_0.as_mut(), self.gen_1.as_mut())
        } else {
            (self.gen_1.as_mut(), self.gen_0.as_mut())
        };
        let bitset = self.bitset.as_mut();
        next.count = 0;
        for root in roots {
            if !bitset.get(root.idx()) {
                let idx = next.count as usize;
                next.objects[idx].tombstone = **root;
                next.count += 1;
                bitset.set(root.idx());
            }
        }

        let mut cursor = 0;
        while cursor < next.count {
            // For anything in the new generation, we have only written to the tombstone
            // at this point.
            // And we have written to every tombstone before next.count.
            let old_ptr = unsafe { next.objects[cursor as usize].tombstone };
            let old_object = current.get(old_ptr.idx());
            match old_ptr.tag() {
                Tag::Pair => {
                    // Safe: the tag for this pointer indicates a pair.
                    let pair = unsafe { old_object.pair };
                    for ptr in [pair.car, pair.cdr] {
                        if !bitset.get(ptr.idx()) {
                            let idx = next.count as usize;
                            next.objects[idx].tombstone = ptr;
                            next.count += 1;
                            bitset.set(ptr.idx());
                        }
                    }
                }
                Tag::Vector => {
                    let vector = unsafe { old_object.vector };
                    for i in 0..vector.length {
                        if let Some(ptr) = vector.offset(i) {
                            //
                            // we do not check the bitset here;
                            // if an object is in a vector and is also referred to
                            // directly, two cases:
                            // 1. The direct pointer(s) run first, then the vector.
                            //    In this case, in the swap pass,
                            //    the vector will overwrite the tombstone
                            //    set by the direct pointer; the resulting tombstone
                            //    will be the vector one.
                            //    This will leave a hole in the new generation-
                            //    the "first place" the vector-element went to,
                            //    from the pair.
                            //    At most one hole per object, since only the first
                            //    pair will generate a hole.
                            // 2. The vector runs first, in which case no hole is created.
                            //
                            // TODO: WARNING DIRE:
                            // A node _must not_ be a member of multiple vectors.
                            // Then...they'll get split up and everything will go to shit.
                            let idx = next.count as usize;
                            next.objects[idx].tombstone = ptr;
                            next.count += 1;
                            bitset.set(ptr.idx());
                        }
                    }
                }
                Tag::Nil | Tag::Integer | Tag::Float | Tag::Bytes | Tag::Symbol => (),
            };
            cursor += 1;
        }
    }

    fn swap_pass(&mut self) {
        let (current, next) = if self.generation % 2 == 0 {
            (self.gen_0.as_mut(), self.gen_1.as_mut())
        } else {
            (self.gen_1.as_mut(), self.gen_0.as_mut())
        };

        for cursor in 0..(next.count as usize) {
            // We only wrote to tombstone in the last pass,
            // for every element up to next.count-1.
            let ptr = unsafe { next.objects[cursor].tombstone };
            let object = current.objects[ptr.idx()];
            next.objects[cursor] = object;
            current.objects[ptr.idx()].tombstone = StoredPtr::new(cursor, ptr.tag());
        }
    }
    fn fixup_pass(&mut self, roots: &mut [&mut StoredPtr]) {
        let (current, next) = if self.generation % 2 == 0 {
            (self.gen_0.as_mut(), self.gen_1.as_mut())
        } else {
            (self.gen_1.as_mut(), self.gen_0.as_mut())
        };
        let bitset = self.bitset.as_mut();
        for bit in bitset.bits_set() {
            // We updated all of the tombstones in the swap pass.
            let new_ptr = current.get_next(bit);
            let new_object = next.get_ref(new_ptr.idx());
            match new_ptr.tag() {
                Tag::Pair => {
                    // Safe: the tag for this pointer indicates a pair.
                    let pair = unsafe { &mut new_object.pair };
                    for ptr in [&mut pair.car, &mut pair.cdr] {
                        *ptr = current.get_next(ptr.idx());
                    }
                }
                Tag::Vector => {
                    let vector = unsafe { &mut new_object.vector };
                    vector.start = current.get_next(vector.start.idx());
                }
                Tag::Nil | Tag::Integer | Tag::Float | Tag::Bytes | Tag::Symbol => (),
            };
        }
        bitset.clear_all();

        // Fixup roots too:
        for root in roots {
            **root = current.get_next(root.idx());
        }
    }

    #[cfg(feature = "std")]
    fn fixup_labels(&self, labels: &mut ObjectFormats) {
        let current = self.current();
        let bitset = self.bitset.as_ref();

        let new_labels = labels
            .clone()
            .into_iter()
            .filter_map(|(k, v)| {
                if bitset.get(k.idx()) {
                    Some((current.get_next(k.idx()), v))
                } else {
                    None
                }
            })
            .collect();
        *labels = new_labels;
    }
}
