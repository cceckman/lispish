/// Implementation of a bit set.
///
/// We'll start with a pretty basic implementation,
/// then see if Roaring or something helps.
#[derive(Clone, Debug, Default)]
pub struct BitSet {
    count: usize,
    data: Vec<usize>,
}

impl BitSet {
    /// Creates a new, empty bitset.
    pub fn new() -> Self {
        Default::default()
    }

    const BITS_PER_WORD: usize = core::mem::size_of::<usize>() * 8;

    /// Gets the value of the given bit
    pub fn get(&self, idx: usize) -> bool {
        let word = idx / Self::BITS_PER_WORD;
        let bit = idx % Self::BITS_PER_WORD;
        if word >= self.data.len() {
            return false;
        }
        let bit = self.data[word] & (1 << bit);
        bit != 0
    }

    /// Sets the given bit.
    pub fn set(&mut self, idx: usize) {
        let word = idx / Self::BITS_PER_WORD;
        let bit = idx % Self::BITS_PER_WORD;
        if word >= self.data.len() {
            self.data.resize(word + 1, 0);
        }
        {
            let masked = self.data[word] & (1 << bit);
            if masked == 0 {
                self.count += 1;
            }
        }
        self.data[word] |= 1 << bit;
    }

    /// Clears the given bit.
    pub fn clear(&mut self, idx: usize) {
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

    pub fn count(&self) -> usize {
        self.count
    }

    /// Iterator over the bits that are set.
    pub fn bits_set(&self) -> impl '_ + Iterator<Item = usize> {
        BitIterator {
            idx: 0,
            bitset: self,
        }
    }
}

struct BitIterator<'a> {
    idx: usize,
    bitset: &'a BitSet,
}

impl Iterator for BitIterator<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        while !self.bitset.get(self.idx) {
            if self.idx >= (self.bitset.data.len() * BitSet::BITS_PER_WORD) {
                return None;
            }
            self.idx += 1;
        }
        let result = self.idx;
        self.idx += 1;
        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::BitSet;

    #[test]
    fn exhaustive_single_bits() {
        let mut bs = BitSet::new();
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
        let mut bs = BitSet::new();
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

        let mut bs = BitSet::new();
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

        let mut bs = BitSet::new();
        for i in indices.iter() {
            bs.set(*i);
        }

        for (a, &b) in bs.bits_set().zip(indices.iter()) {
            assert_eq!(a, b);
        }
    }
}
