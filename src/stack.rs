#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stack<T> {
    contents: Vec<T>,
}

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Self {
            contents: Vec::new(),
        }
    }
}

impl<T: Copy + Eq> Stack<T> {
    pub fn new() -> Self {
        Self {
            contents: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.contents.len()
    }

    pub fn push(&mut self, x: T) {
        self.contents.push(x);
    }

    pub fn popn(&mut self, count: usize) {
        assert!(count <= self.len());
        self.contents.truncate(self.len() - count);
    }

    pub fn read(&self, depth: usize) -> T {
        let top = self.len() - 1;
        let index = top - depth;
        self.contents[index]
    }

    pub fn depth(&self, x: T) -> usize {
        let index = self.contents
            .iter()
            .rposition(|&y| y == x)
            .unwrap();
        self.len() - 1 - index
    }

    pub fn swap(&mut self, depth: usize) {
        assert!(depth < self.len());
        let top = self.len() - 1;
        let index = top - depth;
        self.contents.swap(index, top);
    }

    pub fn contents(&self) -> &[T] {
        &self.contents
    }
}

impl<T: Copy + Eq> Extend<T> for Stack<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.contents.extend(iter.into_iter());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn new_stack_is_empty() {
        let s: Stack<u8> = Stack::new();
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn push_increases_len() {
        let mut s: Stack<u8> = Stack::new();
        s.push(1);
        s.push(2);
        assert_eq!(s.len(), 2);
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
    fn swap_zero_is_noop() {
        let mut s: Stack<u8> = Stack::new();
        s.extend([1, 2]);
        s.swap(0);
        assert_eq!(s.read(0), 2);
        assert_eq!(s.read(1), 1);
    }

    #[test]
    fn swap_with_none() {
        let mut s: Stack<Option<u8>> = Stack::new();
        s.extend([Some(1), Some(2)]);
        s.push(None);
        s.swap(2);
        assert_eq!(s.read(0), Some(1));
    }

}
