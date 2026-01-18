use std::collections::{HashMap, VecDeque};
use crate::Id;

#[derive(Debug, PartialEq, Eq)]
pub struct Stack<B> {
    base: Vec<(B, Box<[Id]>)>,
    index: HashMap<Id, usize>,
    scratch: VecDeque<Option<Id>>,
    len: usize,
}

impl<B: Copy> Stack<B> {
    pub fn new() -> Self {
        Self {
            base: Vec::new(),
            index: HashMap::new(),
            scratch: VecDeque::new(),
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn len_base(&self) -> usize {
        self.len - self.scratch.len()
    }

    pub fn push(&mut self, x: Option<Id>) {
        self.scratch.push_back(x);
        self.len += 1;
    }

    pub fn popn(&mut self, count: usize) {
        assert!(count <= self.scratch.len());
        let new_scratch_len = self.scratch.len() - count;
        self.scratch.truncate(new_scratch_len);
        self.len -= count;
    }

    pub fn swap(&mut self, depth: usize) {
        assert!(depth < self.scratch.len());
        let scratch_top = self.scratch.len() - 1;
        let scratch_index = scratch_top - depth;
        self.scratch.swap(scratch_index, scratch_top);
    }

    pub fn read(&self, depth: usize) -> Id {
        assert!(depth < self.scratch.len());
        let scratch_top = self.scratch.len() - 1;
        let scratch_index = scratch_top - depth;
        self.scratch[scratch_index].unwrap()
    }

    pub fn depth(&self, x: Id) -> usize {
        if let Some(index) = self.scratch.iter()
            .rposition(|y| y.as_ref().is_some_and(|&y| y == x))
        {
            self.scratch.len() - 1 - index
        } else {
            self.len - 1 - self.index[&x]
        }
    }

    pub fn drain_scratch(&mut self) -> impl ExactSizeIterator<Item = Id> {
        self.len -= self.scratch.len();
        self.scratch.drain(..).map(Option::unwrap)
    }

    pub fn push_base(&mut self, b: B, count: usize) {
        assert!(count <= self.scratch.len());
        let base_index = self.len - self.scratch.len();
        let xs = self.scratch.drain(..count).enumerate().map(|(i, x)| {
            let x = x.unwrap();
            self.index.insert(x, base_index + i);
            x
        });
        self.base.push((b, xs.collect()));
    }

    pub fn top_base(&self) -> Option<B> {
        self.base.last().map(|&(b, _)| b)
    }

    pub fn pop_base(&mut self) {
        let (_, new_scratch) = self.base.pop().unwrap();
        for &x in new_scratch.iter().rev() {
            self.index.remove(&x);
            self.scratch.push_front(Some(x));
        }
    }
}

impl<B> Extend<Id> for Stack<B> {
    fn extend<T: IntoIterator<Item = Id>>(&mut self, iter: T) {
        let prev_scratch_len = self.scratch.len();
        self.scratch.extend(iter.into_iter().map(Some));
        self.len += self.scratch.len() - prev_scratch_len;
    }
}
