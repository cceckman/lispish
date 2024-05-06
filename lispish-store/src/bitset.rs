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
}
