pub struct BitSet {
    unset: usize,
    store: Box<[usize]>,
}

impl BitSet {
    pub fn new(size: usize) -> BitSet {
        let width = usize::BITS as usize;
        let words = size.div_ceil(width);
        let mut store = vec![0; words].into_boxed_slice();
        let rem = size % width;
        if rem > 0 {
            store[words - 1] = (!0usize) << rem;
        }
        BitSet { unset: size, store }
    }

    pub fn unset(&self) -> usize {
        self.unset
    }

    pub fn contains(&self, x: usize) -> bool {
        let (word, mask) = word_mask(x);
        self.store[word] & mask != 0
    }

    pub fn insert(&mut self, x: usize) -> bool {
        let (word, mask) = word_mask(x);
        let inserted = self.store[word] & mask == 0;
        self.unset -= inserted as usize;
        self.store[word] |= mask;
        inserted
    }
}

fn word_mask(x: usize) -> (usize, usize) {
    let width = usize::BITS as usize;
    let pos = x / width;
    let mask = 1 << (x % width);
    (pos, mask)
}
