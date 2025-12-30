pub struct BitSet {
    store: Box<[usize]>,
}

impl BitSet {
    pub fn new(size: usize) -> BitSet {
        let width = usize::BITS as usize;
        let words = size.div_ceil(width);
        let store = vec![0; words].into_boxed_slice();
        BitSet { store }
    }

    pub fn insert(&mut self, x: usize) -> bool {
        let (word, mask) = word_mask(x);
        let inserted = self.store[word] & mask == 0;
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
