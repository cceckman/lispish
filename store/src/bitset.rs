use core::mem::size_of;

/// Implementation of a bit set.
/// The WORDS count is in the number of usizes.
///
/// We'll start with a pretty basic implementation,
/// then see if Roaring or something helps.
#[derive(Clone, Debug)]
pub struct ArrayBitSet<const WORDS: usize> {
    /// Count is the number of bits set.
    count: usize,
    data: [usize; WORDS],
}

/// Returns the number of words required to hold the given number of bits.
pub const fn words_for_bits(bits: usize) -> usize {
    bits.div_ceil(size_of::<usize>() * 8)
}

pub trait BitSet {
    fn get(&self, idx: usize) -> bool;
    fn set(&mut self, idx: usize);
    fn clear(&mut self, idx: usize);
    fn bits_set(&self) -> impl '_ + Iterator<Item = usize>;
    fn clear_all(&mut self);
    fn max(&self) -> usize;
}

impl<const WORDS: usize> ArrayBitSet<WORDS> {
    /// Creates a new, empty bitset.
    pub fn new() -> Self {
        Default::default()
    }
    const BITS_PER_WORD: usize = core::mem::size_of::<usize>() * 8;
}

impl<const WORDS: usize> Default for ArrayBitSet<WORDS> {
    fn default() -> Self {
        ArrayBitSet {
            count: 0,
            data: [0usize; WORDS],
        }
    }
}

impl<const WORDS: usize> BitSet for ArrayBitSet<WORDS> {
    /// Gets the value of the given bit
    fn get(&self, idx: usize) -> bool {
        let word = idx / Self::BITS_PER_WORD;
        let bit = idx % Self::BITS_PER_WORD;
        if word >= self.data.len() {
            return false;
        }
        let bit = self.data[word] & (1 << bit);
        bit != 0
    }

    /// Sets the given bit.
    fn set(&mut self, idx: usize) {
        let word = idx / Self::BITS_PER_WORD;
        let bit = idx % Self::BITS_PER_WORD;
        {
            let masked = self.data[word] & (1 << bit);
            if masked == 0 {
                self.count += 1;
            }
        }
        self.data[word] |= 1 << bit;
    }

    /// Clears the given bit.
    fn clear(&mut self, idx: usize) {
        let word = idx / Self::BITS_PER_WORD;
        let bit = idx % Self::BITS_PER_WORD;
        if word >= self.data.len() {
            // Nothing to do, it's already cleared.
            return;
        }
        {
            let masked = self.data[word] & (1 << bit);
            if masked != 0 {
                self.count -= 1;
            }
        }

        self.data[word] &= !(1 << bit);
    }

    /// Iterator over the bits that are set.
    fn bits_set(&self) -> impl '_ + Iterator<Item = usize> {
        BitIterator {
            idx: 0,
            observed_count: 0,
            bitset: self,
        }
    }

    /// Zero the bitset.
    fn clear_all(&mut self) {
        for datum in self.data.iter_mut() {
            *datum = 0;
        }
        self.count = 0;
    }

    fn max(&self) -> usize {
        Self::BITS_PER_WORD * WORDS
    }
}

struct BitIterator<'a, B> {
    idx: usize,
    observed_count: usize,
    bitset: &'a B,
}

impl<B> Iterator for BitIterator<'_, B>
where
    B: BitSet,
{
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        // TODO: Write a vectorizeable version of this.
        while self.idx < self.bitset.max() && !self.bitset.get(self.idx) {
            self.idx += 1;
        }
        if self.idx >= self.bitset.max() {
            return None;
        }
        let result = self.idx;
        self.idx += 1;
        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::{ArrayBitSet, BitSet};

    #[test]
    fn exhaustive_single_bits() {
        let mut bs = ArrayBitSet::<64>::new();
        for i in 0..255usize {
            assert!(!bs.get(i));
            bs.set(i);
            for j in 0..255usize {
                assert_eq!(bs.get(j), i == j);
            }

            bs.clear(i)
        }
    }

    #[test]
    fn even_bits() {
        let mut bs = ArrayBitSet::<64>::new();
        for i in (0..255usize).filter(|i| i % 2 == 0) {
            bs.set(i);
        }
        bs.set(1);
        bs.clear(2);
    }

    #[test]
    fn iterator() {
        let indices = {
            let mut v = vec![1, 2, 5, 14354, 764756, 25436];
            v.sort();
            v
        };

        let mut bs = ArrayBitSet::<64>::new();
        for i in indices.iter() {
            bs.set(*i);
        }

        for (a, &b) in bs.bits_set().zip(indices.iter()) {
            assert_eq!(a, b);
        }
    }

    #[test]
    fn iterator_with_zero() {
        let indices = {
            let mut v = vec![0, 2, 5];
            v.sort();
            v
        };

        let mut bs = ArrayBitSet::<64>::new();
        for i in indices.iter() {
            bs.set(*i);
        }

        for (a, &b) in bs.bits_set().zip(indices.iter()) {
            assert_eq!(a, b);
        }
    }
}
