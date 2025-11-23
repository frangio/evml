use std::{collections::{hash_map::Entry, HashMap}, hash::Hash, iter::{chain, successors, zip}, mem, ops::Deref};

pub struct Edges<T> {
    inner: Vec<(T, T)>,
}

impl<T> Deref for Edges<T> {
    type Target = Vec<(T, T)>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: Copy + Ord> Edges<T> {
    pub fn new(mut edges: Vec<(T, T)>) -> Edges<T> {
        edges.sort_unstable();
        Edges { inner: edges }
    }

    fn first(&self) -> Option<OutEdgeIter<T>> {
        self.inner.first().map(|&(x, _)|
            OutEdgeIter { source: x, next: 0 }
        )
    }

    fn out_from(&self, x: T) -> OutEdgeIter<T> {
        let i = self.inner.partition_point(|&(y, _)| y < x);
        OutEdgeIter { source: x, next: i }
    }
}

struct OutEdgeIter<T> {
    source: T,
    next: usize,
}

impl<T: Copy + Eq> OutEdgeIter<T> {
    fn next(&mut self, edges: &Edges<T>) -> Option<T> {
        let &(x, y) = edges.get(self.next)?;
        (x == self.source).then(|| {
            self.next += 1;
            y
        })
    }

    fn reset(mut self, edges: &Edges<T>) -> Option<Self> {
        let &(x, _) = edges.get(self.next)?;
        self.source = x;
        Some(self)
    }
}

pub struct Scc<T> {
    comps: Vec<Option<T>>,
    count: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub enum SccEntry<T> {
    Member(usize, T),
    Done(usize),
}

impl<T: Copy> Scc<T> {
    pub fn count(&self) -> usize {
        self.count
    }

    pub fn iter(&self) -> impl Iterator<Item = SccEntry<T>> {
        let mut i = 0;
        self.comps.iter().map(move |&x| {
            if let Some(x) = x {
                SccEntry::Member(i, x)
            } else {
                let j = i;
                i += 1;
                SccEntry::Done(j)
            }
        })
    }
}

pub fn scc<T: Copy + Ord + Hash>(edges: &Edges<T>) -> Scc<T> {
    struct State<T> {
        rep: usize,
        link: Option<T>,
    }

    let mut pre = (0..).into_iter();
    let mut state = HashMap::new();
    let mut stack = Vec::new();
    let mut sink = None;
    let mut offset = 0;

    let mut make_state = |x| State {
        rep: pre.next().unwrap(),
        link: Some(x),
    };

    if let Some(next_root) = edges.first() {
        let x = next_root.source;
        state.insert(x, make_state(x));
        stack.push(next_root);
    }

    while let Some(x_out) = stack.last_mut() {
        let x = x_out.source;

        if let Some(y) = x_out.next(edges) {
            match state.entry(y) {
                Entry::Vacant(y_state) => {
                    y_state.insert(make_state(y));
                    stack.push(edges.out_from(y));
                }

                Entry::Occupied(y_state) => {
                    let y_rep = y_state.get().rep;
                    let x_state = state.get_mut(&x).unwrap();
                    if y_rep < x_state.rep {
                        x_state.rep = y_rep;
                        x_state.link = None;
                    }
                }
            }
        } else {
            let x_out = stack.pop().unwrap();
            let x_state = state.get_mut(&x).unwrap();
            let x_rep = x_state.rep;

            let p = stack.last().map(|p_out| p_out.source);

            if x_state.link == Some(x) {
                x_state.rep = edges.len() + 1 + offset;
                x_state.link = sink;
                offset += 2;

                while let Some(y) = sink {
                    let y_state = state.get_mut(&y).unwrap();
                    sink = y_state.link;
                    if y_state.rep < x_rep {
                        break;
                    } else {
                        y_state.rep = edges.len();
                        offset += 1;
                    }
                }
            } else if let Some(p) = p {
                x_state.link = sink;
                sink = Some(x);

                let p_state = state.get_mut(&p).unwrap();

                if x_rep < p_state.rep {
                    p_state.rep = x_rep;
                    p_state.link = None;
                }
            }

            if p.is_none() {
                let mut prev_root = x_out;
                while let Some(mut next_root) = prev_root.reset(edges) {
                    if state.contains_key(&next_root.source) {
                        while next_root.next(edges).is_some() {}
                        prev_root = next_root;
                    } else {
                        let y = next_root.source;
                        state.insert(y, make_state(y));
                        stack.push(next_root);
                        break;
                    }
                }
            }
        }
    }

    let mut comps = vec![None; offset];
    let mut count = 0;

    for (&x, x_state) in state.iter() {
        if x_state.rep > edges.len() {
            count += 1;
            let comp_offset = x_state.rep - edges.len() - 1;
            let comp_members = comps[comp_offset..].iter_mut();
            let links = successors(x_state.link, |y| state[&y].link);
            for (member, x) in zip(comp_members, chain([x], links)) {
                *member = Some(x);
            }
        }
    }

    Scc { comps, count }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let edges = Edges::<()>::new(vec![]);
        let result = scc(&edges);
        assert_eq!(result.count, 0);
        let entries: Vec<_> = result.iter().collect();
        assert!(entries.is_empty());
    }

    #[test]
    fn test_self_loop() {
        let edges = Edges::new(vec![(10, 10)]);
        let result = scc(&edges);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![SccEntry::Member(0, 10), SccEntry::Done(0)]);
    }

    #[test]
    fn test_simple() {
        let edges = Edges::new(vec![(10, 11)]);
        let result = scc(&edges);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![SccEntry::Member(0, 11), SccEntry::Done(0), SccEntry::Member(1, 10), SccEntry::Done(1)]);
    }

    #[test]
    fn test_cycle_two() {
        let edges = Edges::new(vec![(10, 11), (11, 10)]);
        let result = scc(&edges);
        assert_eq!(result.count, 1);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![SccEntry::Member(0, 10), SccEntry::Member(0, 11), SccEntry::Done(0)]);
    }

    #[test]
    fn test_cycle_three() {
        let edges = Edges::new(vec![(10, 11), (11, 12), (12, 10)]);
        let result = scc(&edges);
        assert_eq!(result.count, 1);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![SccEntry::Member(0, 10), SccEntry::Member(0, 11), SccEntry::Member(0, 12), SccEntry::Done(0)]);
    }

    #[test]
    fn test_chain() {
        let edges = Edges::new(vec![(10, 11), (11, 12), (12, 13)]);
        let result = scc(&edges);
        assert_eq!(result.count, 4);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![
            SccEntry::Member(0, 13), SccEntry::Done(0),
            SccEntry::Member(1, 12), SccEntry::Done(1),
            SccEntry::Member(2, 11), SccEntry::Done(2),
            SccEntry::Member(3, 10), SccEntry::Done(3)
        ]);
    }

    #[test]
    fn test_diamond() {
        let edges = Edges::new(vec![(10, 11), (10, 12), (11, 13), (12, 13)]);
        let result = scc(&edges);
        assert_eq!(result.count, 4);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![
            SccEntry::Member(0, 13), SccEntry::Done(0),
            SccEntry::Member(1, 11), SccEntry::Done(1),
            SccEntry::Member(2, 12), SccEntry::Done(2),
            SccEntry::Member(3, 10), SccEntry::Done(3)
        ]);
    }

    #[test]
    fn test_two_with_edge_between() {
        let edges = Edges::new(vec![
            (10, 11), (11, 12), (12, 10),
            (13, 14), (14, 13),
            (12, 13),
        ]);
        let result = scc(&edges);
        assert_eq!(result.count, 2);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![
            SccEntry::Member(0, 13), SccEntry::Member(0, 14), SccEntry::Done(0),
            SccEntry::Member(1, 10), SccEntry::Member(1, 11), SccEntry::Member(1, 12), SccEntry::Done(1)
        ]);
    }

    #[test]
    fn test_backedge() {
        let edges = Edges::new(vec![(10, 11), (11, 12), (12, 13), (13, 11)]);
        let result = scc(&edges);
        assert_eq!(result.count, 2);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![
            SccEntry::Member(0, 11), SccEntry::Member(0, 12), SccEntry::Member(0, 13), SccEntry::Done(0),
            SccEntry::Member(1, 10), SccEntry::Done(1)
        ]);
    }

    #[test]
    fn test_duplicate_edges() {
        let edges = Edges::new(vec![(10, 11), (10, 11), (11, 12), (12, 11), (11, 12)]);
        let result = scc(&edges);
        assert_eq!(result.count, 2);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(entries, vec![
            SccEntry::Member(0, 11), SccEntry::Member(0, 12), SccEntry::Done(0),
            SccEntry::Member(1, 10), SccEntry::Done(1)
        ]);
    }

    #[test]
    fn test_disconnected() {
        let edges = Edges::new(vec![(10, 11), (15, 16)]);
        let result = scc(&edges);
        let entries: Vec<_> = result.iter().collect();
        assert_eq!(result.count, 4);
        assert_eq!(entries, vec![
            SccEntry::Member(0, 11), SccEntry::Done(0),
            SccEntry::Member(1, 10), SccEntry::Done(1),
            SccEntry::Member(2, 16), SccEntry::Done(2),
            SccEntry::Member(3, 15), SccEntry::Done(3)
        ]);
    }
}
