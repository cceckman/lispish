# Lispish garbage collection

Our goal is to perform a mark-and-sweep garbage collection _without dynamic memory allocation_.
A strategy such as [tri-color marking](https://en.wikipedia.org/wiki/Tracing_garbage_collection)
would be attractive, but for the fact that Lispish uses _external tags_.

Lispish _pointers_ encode the type of their _pointees_.
This means "just visit an object" isn't necessarily feasible -- we also have to "know"
the type of the pointee.

Below, we discuss approaches.

## Four-color marking

[Based on tri-color marking](https://en.wikipedia.org/wiki/Tracing_garbage_collection#Tri-color_marking).

2-bits per object:

- Unknown / unallocated (0 / 0)
- Live (1 / 0)
- Need to visit, recurse as pair (0 / 1)
- Need to visit, recurse as vector (1 / 1).

Add the roots to the tracking set, as pair/vector/visited (as appropriate).
Repeatedly scan over the tracking set for "need to visit" values.

When visiting a "need to visit" node:
- If it is visit-as-pair, _mark_ car and cdr.
- If the target is visit-as-vector, _mark_ each node in the vector.

_mark_ is an operation that takes a pointer and:

- If the pointee is a self-representing type (integer, float, symbol, bytes, etc.),
  mark it as live.
- If the pointee is a recursive type (vector, pair),
  and is not "live" (already visited),
  mark it as "need to visit" with the appropriate recursive type.

### microoptimizations

We track "need to visit" and "live" in separate arrays.
- Scan for "next to visit" with bitwise / vector ops.
- Scan for "next space" (for allocation) with bitwise / vector ops.

Amortize scanning by tracking the high-water-mark after GC,
maintain it if we allocate beyond it.

### Performance

Memory overhead: 2/64 of memory.

Allocation: Scan for "empty slot", linear in the worst case.
But it amortizes fine.

GC has, in the worst case, N scans over the "next to analyze" list.
- On each pass, at least one "next to analyze" bit is marked.
- On each pass, at least one "next to analyze" bit is consumed.
- At most, each bit is marked / unmarked once.

## Reverse pointers

Extend each stored object with a "GC" pointer.

The GC state includes a "last visited object" pointer
in the live (transient) state.

Keep a "last processed object" pointer to allow in-place depth-first traversal.

- When visiting a pair,
  - If the last-visited is not CAR or CDR, and the node is marked, visit the last-visited.
  - If the last-visited is not CAR or CDR, and the node is not marked, set the GC pointer to last-visited, mark, and visit CAR.
  - If the last-visited is CAR, visit CDR.
  - If the last-visited is CDR, visit the GC pointer.
- When visiting a vector,
  - If the last-visited is not an element of the vector, and the node is not marked, set the GC pointer to last-visited, mark, and visit the first element.
  - If the last-visited is an element of the vector that is not the last, visit the next element.
  - If the last-visited is the last element of the vector, visit the GC pointer.
- When visiting any other node,
  - Mark the node, then visit the last-visited.

The resulting bit-set tracks all allocated elements,
to avoid repetition.

### Performance

Visits pairs twice, visits vectors N times (for the number of elements).
Which I guess is equivalent to saying "linear".

Overhead: 1 bit per object (1/64), plus one pointer per object (4/8),
so 33 overhead bits per 64 bits of object.

The memory overhead is bitset + 1 ptr/object, i.e. 50% for 2-ptr objects,
which is less than the modified Cheney.

Linear allocation (bitwise), so it takes a while.

## Modified Cheyney's algorithm

A modified version of [Cheney's Algorithm](https://en.wikipedia.org/wiki/Cheney%27s_algorithm)
with additional passes and (static) memory overheads, in order to run in a fixed amount of memory.

### Procedure 

We divide the allocatable memory into:
- Arenas 0/1, with N objects each
- A bitset of N bits

We track the following variables:
- Active arena (one bit)
- M roots: pointers into the active arena.
- Arena allocation: a count, less than N

#### Queue pass

First, copy _old pointers_ into the new arena.

1. Initialize `count = 0, bitset[..] = 0`.
2. For each root,
   1. Insert root at `new[count]`.
   2. Set `bitset[root.idx]`.
   3. Increment `count`.
3. Initialize local `cursor` = 0.
4. While `cursor < count`,
   1. Retrieve a pointer to the old arena: `old_ptr := new[cursor]`.
   2. If `old_ptr` points to an object that contains pointers,
      1. Retrieve the object: `obj := old[old_ptr.idx]`.
      2. For each pointer `ptr`, if `!bitset[ptr.idx]`,
         1. Insert `new[count] = ptr`.
         2. Set `bitset[ptr.idx]`.
         3. Increment `count`.
   3. Increment `cursor`.

At the end of this, the new arena contains pointers to the old
arena, in breadth-first traversal order, without loops.

#### Swap pass

1. Initialize `cursor := 0`.
2. While `cursor < count`,
   1. Retrieve a pointer to the old arena: `old_ptr := new[cursor]`.
   2. Copy the object to the new arena: `new[cursor] = old[old_ptr.idx]`.
   3. Leave a tombstone pointing to the new object: `old[old_ptr.idx] = pointer(cursor, old_ptr.tag)`
   4. Increment `cursor`.

#### Fixup pass

Note that at this point, `new` contains no type information for its contents,
and `old` contains a mix of invalid objects -- either collected, or tombstones.

However, `bitset` contains _the indices of all tombstones_: those objects
which were patched.

1. Initialize `cursor := 0`.
2. While `cursor < N`,
   1. If `bitset[cursor]`, patch the pointers in the new arena:
      1. Retrieve the new pointer: `new_ptr = old[cursor]`
      2. If `new_ptr` points to an object that contains pointers,
         1. Retrieve the object: `obj := new[new_ptr.idx]`
         2. For each pointer `old_sub_ptr`,
             1. Retrieve the new pointer: `new_sub_ptr := old[old_sub_ptr.idx]`
             2. Replace `old_sub_ptr` with `new_sub_ptr` in `obj`.
         3. Replace the object with one with updated pointers: `new[new_ptr.idx] = obj`.
   2. Increment `cursor`.

Cheney's algorithm doubles the memory cost by only using half the arena,
plus we have the bitset overhead. A "reverse pointer", or "next pointer",
would be only 50% overhead- plus a bitset, I'm sure, to avoid dupes.

## Performance

Memory overhead: 65/64 of memory; 64 bits of overhead plus one bit.

Allocation is constant-time (yay!)

GC only has to do one pass over the bitset.
