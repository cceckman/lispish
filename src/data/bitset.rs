/// Implementation of a bit set.
///
/// We'll start with a pretty basic implementation,
/// then see if Roaring or something helps.
#[derive(Clone, Debug, Default)]
pub struct BitSet {
    data: Vec<usize>,
}

impl BitSet {
    /// Creates a new, empty bitset.
    pub fn new() -> Self {
        Default::default()
    }

    const BITS_PER_WORD: usize = std::mem::size_of::<usize>() * 8;

    /// Find the first zero is the key operation for a bitset-based allocator.
    pub fn find_first_zero(&self) -> usize {
        for (idx, word) in self.data.iter().enumerate() {
            let z: usize = word.trailing_ones() as usize;
            if z < Self::BITS_PER_WORD {
                // There's a zero in this bitmask; get it.
                return (idx * Self::BITS_PER_WORD) + z;
            }
        }
        return self.data.len() * Self::BITS_PER_WORD;
    }

    /// Gets the value of the given bit
    pub fn get(&self, idx: usize) -> bool {
        let word = idx / Self::BITS_PER_WORD;
        let bit = idx % Self::BITS_PER_WORD;
        if word >= self.data.len() {
            return false;
        }
        let bit = self.data[word] & (1 << bit);
        return bit != 0;
    }

    /// Sets the given bit.
    pub fn set(&mut self, idx: usize) {
        let word = idx / Self::BITS_PER_WORD;
        let bit = idx % Self::BITS_PER_WORD;
        if word >= self.data.len() {
            self.data.resize(word + 1, 0);
        }
        self.data[word] |= 1 << bit;
    }

    /// Clears the given bit.
    pub fn clear(&mut self, idx: usize) {
        let word = idx / Self::BITS_PER_WORD;
        let bit = idx % Self::BITS_PER_WORD;
        if word >= self.data.len() {
            self.data.resize(word + 1, 0);
        }
        self.data[word] &= !(1 << bit);
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

            if i == 0 {
                assert_eq!(bs.find_first_zero(), 1);
            } else {
                assert_eq!(bs.find_first_zero(), 0);
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
        assert_eq!(bs.find_first_zero(), 1);
        bs.set(1);
        assert_eq!(bs.find_first_zero(), 3);
        bs.clear(2);
        assert_eq!(bs.find_first_zero(), 2);
    }
}
