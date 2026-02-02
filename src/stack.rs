use std::collections::HashMap;
use std::hash::Hash;

/// A stack divided into two regions: a frame and a scratch area.
///
/// The frame holds items that cannot be moved or removed. The scratch area sits on top and
/// can be freely manipulated. Frame items are indexed for O(1) depth lookup.
///
/// Slots in the scratch area may be `None` to represent "temporary" items with no
/// associated value. Frame slots must always contain a value.
#[derive(Debug)]
pub struct Stack<T> {
    contents: Vec<Option<T>>,
    index: HashMap<T, usize>,
    framed: usize,
}

impl<T: Copy + Eq + Hash> Stack<T> {
    pub fn new() -> Self {
        Self {
            index: HashMap::new(),
            contents: Vec::new(),
            framed: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.contents.len()
    }

    pub fn len_scratch(&self) -> usize {
        self.len() - self.framed
    }

    pub fn len_framed(&self) -> usize {
        self.framed
    }

    pub fn push(&mut self, x: Option<T>) {
        self.contents.push(x);
    }

    pub fn popn(&mut self, count: usize) {
        assert!(count <= self.len_scratch());
        self.contents.truncate(self.len() - count);
    }

    pub fn swap(&mut self, depth: usize) {
        assert!(depth < self.len_scratch());
        let contents_top = self.contents.len() - 1;
        let contents_index = contents_top - depth;
        self.contents.swap(contents_index, contents_top);
    }

    pub fn read(&self, depth: usize) -> T {
        let contents_top = self.contents.len() - 1;
        let contents_index = contents_top - depth;
        self.contents[contents_index].unwrap()
    }

    /// Returns the depth of the first occurrence of `x` from the top.
    pub fn depth(&self, x: T) -> usize {
        if let Some(index) = self.contents[self.framed..].iter()
            .rposition(|y| y.as_ref().is_some_and(|&y| y == x))
        {
            self.len() - self.framed - 1 - index
        } else {
            self.len() - 1 - self.index[&x]
        }
    }

    pub fn drain_scratch(&mut self) -> impl ExactSizeIterator<Item = T> + '_ {
        self.contents.drain(self.framed..).map(Option::unwrap)
    }

    pub fn push_to_frame(&mut self, count: usize) {
        for i in 0..count {
            let x = self.contents[self.framed + i].unwrap();
            self.index.insert(x, self.framed + i);
        }
        self.framed += count;
    }

    pub fn pop_from_frame(&mut self, count: usize) {
        self.framed -= count;
        for i in 0..count {
            let x = self.contents[self.framed + i].unwrap();
            self.index.remove(&x);
        }
    }

}

impl<T: Copy + Eq + Hash> Extend<T> for Stack<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.contents.extend(iter.into_iter().map(Some));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_stack_is_empty() {
        let s: Stack<u8> = Stack::new();
        assert_eq!(s.len(), 0);
        assert_eq!(s.len_scratch(), 0);
    }

    #[test]
    fn push_increases_len() {
        let mut s: Stack<u8> = Stack::new();
        s.push(Some(1));
        s.push(None);
        assert_eq!(s.len(), 2);
        assert_eq!(s.len_scratch(), 2);
    }

    #[test]
    fn extend_pushes_multiple() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2, 3]);
        assert_eq!(s.len(), 3);
    }

    #[test]
    fn popn_removes_from_top() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2, 3]);
        s.popn(2);
        assert_eq!(s.len(), 1);
        assert_eq!(s.read(0), 1);
    }

    #[test]
    #[should_panic]
    fn popn_panics_if_exceeds_scratch() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2]);
        s.push_to_frame(2);
        s.popn(1);
    }

    #[test]
    fn read_returns_item_at_depth() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([10, 20, 30]);
        assert_eq!(s.read(0), 30); // top
        assert_eq!(s.read(1), 20);
        assert_eq!(s.read(2), 10); // bottom
    }

    #[test]
    fn swap_exchanges_top_with_depth() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2, 3]);
        s.swap(2);
        assert_eq!(s.read(0), 1);
        assert_eq!(s.read(2), 3);
    }

    #[test]
    fn depth_finds_item_in_scratch() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2, 3]);
        assert_eq!(s.depth(3), 0);
        assert_eq!(s.depth(2), 1);
        assert_eq!(s.depth(1), 2);
    }

    #[test]
    fn push_to_frame_moves_items_to_frame() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2, 3, 4]);
        s.push_to_frame(2);
        assert_eq!(s.len(), 4);
        assert_eq!(s.len_scratch(), 2);
        assert_eq!(s.depth(1), 3);
        assert_eq!(s.depth(2), 2);
    }

    #[test]
    fn pop_from_frame_clears_index() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2, 3]);
        s.push_to_frame(2);
        s.pop_from_frame(1);
        assert_eq!(s.len_scratch(), 2);
        assert_eq!(s.depth(2), 1);
        assert_eq!(s.depth(3), 0);
        s.swap(1);
        assert_eq!(s.depth(2), 0);
        assert_eq!(s.depth(3), 1);
    }

    #[test]
    fn drain_scratch_leaves_frame_intact() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2, 3, 4]);
        s.push_to_frame(2);
        let drained: Vec<_> = s.drain_scratch().collect();
        assert_eq!(drained, vec![3, 4]);
        assert_eq!(s.len(), 2);
        assert_eq!(s.len_scratch(), 0);
    }

    #[test]
    fn swap_zero_is_noop() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2]);
        s.swap(0);
        assert_eq!(s.read(0), 2);
        assert_eq!(s.read(1), 1);
    }

    #[test]
    fn swap_with_none() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2]);
        s.push(None);
        s.swap(2);
        assert_eq!(s.read(0), 1);
    }

    #[test]
    #[should_panic]
    fn push_to_frame_panics_on_none() {
        let mut s: Stack<u8> = Stack::new();
        s.push(None);
        s.push_to_frame(1);
    }
}
