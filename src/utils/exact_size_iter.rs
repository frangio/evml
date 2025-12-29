use std::{iter::{self, Chain, FusedIterator}};

pub fn exact_size_chain<A, B>(a: A, b: B) -> ExactSizeChain<A::IntoIter, B::IntoIter>
where
    A: IntoIterator,
    B: IntoIterator<Item = A::Item>,
    A::IntoIter: ExactSizeIterator,
    B::IntoIter: ExactSizeIterator,
{
    let a = a.into_iter();
    let b = b.into_iter();
    assert!(a.len().checked_add(b.len()).is_some());
    ExactSizeChain(iter::chain(a, b))
}

#[derive(Debug, Clone, Default)]
pub struct ExactSizeChain<A, B>(Chain<A, B>);

impl<A, B> Iterator for ExactSizeChain<A, B>
where
    A: Iterator,
    B: Iterator<Item = A::Item>,
{
    type Item = A::Item;

    #[inline]
    fn next(&mut self) -> Option<A::Item> {
        self.0.next()
    }

    #[inline]
    fn count(self) -> usize {
        self.0.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n)
    }

    #[inline]
    fn last(self) -> Option<A::Item> {
        self.0.last()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<A, B> DoubleEndedIterator for ExactSizeChain<A, B>
where
    A: Iterator,
    B: Iterator<Item = A::Item>,
    Chain<A, B>: DoubleEndedIterator<Item = A::Item>,
{
    #[inline]
    fn next_back(&mut self) -> Option<A::Item> {
        self.0.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth_back(n)
    }
}

impl<A, B> FusedIterator for ExactSizeChain<A, B>
where
    A: Iterator,
    B: Iterator<Item = A::Item>,
    Chain<A, B>: FusedIterator,
{}

impl<A, B> ExactSizeIterator for ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = A::Item>,
{}

pub fn iter_some<I: Iterator>(iter: Option<I>) -> OptionIter<I> {
    OptionIter(iter)
}

#[derive(Debug, Clone, Default)]
pub struct OptionIter<I>(Option<I>);

impl<I: Iterator> Iterator for OptionIter<I> {
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut().and_then(Iterator::next)
    }

    #[inline]
    fn count(self) -> usize {
        self.0.map_or(0, Iterator::count)
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.as_mut().and_then(|iter| iter.nth(n))
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        self.0.and_then(Iterator::last)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.as_ref().map_or((0, Some(0)), Iterator::size_hint)
    }
}

impl<I: DoubleEndedIterator> DoubleEndedIterator for OptionIter<I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.as_mut().and_then(DoubleEndedIterator::next_back)
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.as_mut().and_then(|iter| iter.nth_back(n))
    }
}

impl<I: FusedIterator> FusedIterator for OptionIter<I> {}

impl<I: ExactSizeIterator> ExactSizeIterator for OptionIter<I> {
    #[inline]
    fn len(&self) -> usize {
        self.0.as_ref().map_or(0, ExactSizeIterator::len)
    }
}
