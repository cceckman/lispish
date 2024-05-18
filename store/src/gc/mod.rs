use crate::{arena::Arena, StoredPtr, StoredVector};

#[cfg(feature = "render")]
use crate::render::ObjectFormats;

#[cfg(feature = "std")]
use std::collections::VecDeque;

#[cfg(feature = "std")]
use crate::bitset::BitSet;

/// Internal GC routine.
///
/// This is a "pure" function of the generations.
///
/// All pointers in the environment should be passed in via roots.
/// Pointers can change across a GC pass; the GC routine will fix up those in storage and those in `roots`.
pub fn gc(
    last_gen: &mut Arena,
    next_gen: &mut Arena,
    roots: &mut [&mut StoredPtr],
    #[cfg(feature = "render")] labels: &mut ObjectFormats,
) {
    // TODO: Sketch of "no alloc" version:
    // - Whenever we allocate an Arena,
    //   we reserve the first N chunks for the BitSet,
    //   after 0.
    //   0.2% overhead.
    // - The next generation holds the queue; used, unvisited nodes are marked.
    // - The current generation holds the done; visited nodes are marked.
    // This means the next generation winds up with an empty bitset.

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

        let got = last_gen.get(old_ptr.idx());
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
    // TODO: Handle bit-sets
    for old_idx in live_objects.bits_set() {
        let new_idx = next_gen.put(last_gen.get(old_idx));
        last_gen.set_next(old_idx, new_idx);
    }

    // Now that we've moved everything, we can update labels, dropping any unused.
    *labels = labels
        .drain()
        .filter_map(|(old_ptr, v)| {
            if !live_objects.get(old_ptr.idx()) {
                None
            } else {
                Some((
                    StoredPtr::new(last_gen.get_next(old_ptr.idx()), old_ptr.tag()),
                    v,
                ))
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
        let new_idx = last_gen.get_next(old_root.idx());
        let new_ptr = StoredPtr::new(new_idx, old_root.tag());
        **old_root = new_ptr;
    }

    // Now we have a list of "old" pointers in the heap to go through
    // and fix to the new ones.
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

        let new_ptr = last_gen.get_next_ptr(old_ptr);
        if let Some(mut pair) = next_gen.get(new_ptr.idx()).as_pair(new_ptr) {
            // This is a pair/function we need to update its inner pointers, in the new arena.
            // This object still contains the old pointers, because we haven't visited this node on this pass.
            // Put the old pointers in the queue, and update the new location.
            for rp in [&mut pair.car, &mut pair.cdr] {
                let new_rp = last_gen.get_next_ptr(*rp);
                if !(new_rp.is_nil() || new_rp.is_symbol()) {
                    queue.push_back(*rp);
                }
                *rp = new_rp;
            }
            next_gen.get_ref(new_ptr.idx()).pair = pair;
        }
        if let Some(old_vector) = next_gen.get(new_ptr.idx()).as_vector(new_ptr) {
            // Remap the start, if nonzero:
            let new_start = old_vector
                .clone()
                .next()
                .map(|p| last_gen.get_next_ptr(p))
                .unwrap_or(old_vector.start);
            next_gen.get_ref(new_ptr.idx()).vector = StoredVector {
                length: old_vector.length,
                start: new_start,
            };
            // We need to visit all the _old_ locations.
            queue.extend(old_vector.filter(|p| !(p.is_symbol() || p.is_nil())))
        }
    }
}
