use std::{cmp::max, collections::{hash_map::Entry, HashMap}, convert::identity, hash::Hash, iter::{chain, successors, zip}, mem, ops::Deref};

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
    pub runs: Vec<Option<T>>,
    pub count: usize,
    pub largest: usize,
}

pub fn scc<T: Copy + Ord + Hash>(edges: &Edges<T>, vertices: &[T], vertex_capacity: usize) -> Scc<T> {
    struct State<T> {
        rep: usize,
        link: Option<T>,
    }

    let mut pre = (0..).into_iter();
    let mut state = HashMap::with_capacity(vertex_capacity);
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

    for &v in vertices {
        if let Entry::Vacant(v_state) = state.entry(v) {
            v_state.insert(State {
                rep: edges.len() + 1 + offset,
                link: None,
            });
            offset += 2;
        }
    }

    let mut comps = vec![None; offset];
    let mut count = 0;
    let mut largest = 0;
    let mut member_count = 0;

    for (&x, x_state) in state.iter() {
        if x_state.rep > edges.len() {
            let comp_offset = x_state.rep - edges.len() - 1;
            let comp_members = comps[comp_offset..].iter_mut();
            let mut links = successors(x_state.link, |y| state[y].link);
            let mut size = 0;

            for (member, y) in zip(comp_members, chain([x], &mut links)) {
                assert!(member.is_none());
                *member = Some(y);
                size += 1;
            }

            assert!(links.next().is_none());

            count += 1;
            member_count += size;
            largest = max(largest, size);
        }
    }

    assert!(count + member_count == comps.len());

    Scc { runs: comps, count, largest }
}

pub fn next_run<T>(iter: &mut impl Iterator<Item = Option<T>>) -> Option<impl Iterator<Item = T>> {
    iter.next().map(|x| chain([x], iter).filter_map(identity))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let edges = Edges::<()>::new(vec![]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 0);
        assert!(result.runs.is_empty());
    }

    #[test]
    fn test_self_loop() {
        let edges = Edges::new(vec![(10, 10)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.runs, vec![Some(10), None]);
    }

    #[test]
    fn test_simple() {
        let edges = Edges::new(vec![(10, 11)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.runs, vec![Some(11), None, Some(10), None]);
    }

    #[test]
    fn test_cycle_two() {
        let edges = Edges::new(vec![(10, 11), (11, 10)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 1);
        assert_eq!(result.runs, vec![Some(10), Some(11), None]);
    }

    #[test]
    fn test_cycle_three() {
        let edges = Edges::new(vec![(10, 11), (11, 12), (12, 10)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 1);
        assert_eq!(result.runs, vec![Some(10), Some(11), Some(12), None]);
    }

    #[test]
    fn test_chain() {
        let edges = Edges::new(vec![(10, 11), (11, 12), (12, 13)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 4);
        assert_eq!(result.runs, vec![
            Some(13), None,
            Some(12), None,
            Some(11), None,
            Some(10), None
        ]);
    }

    #[test]
    fn test_diamond() {
        let edges = Edges::new(vec![(10, 11), (10, 12), (11, 13), (12, 13)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 4);
        assert_eq!(result.runs, vec![
            Some(13), None,
            Some(11), None,
            Some(12), None,
            Some(10), None
        ]);
    }

    #[test]
    fn test_two_with_edge_between() {
        let edges = Edges::new(vec![
            (10, 11), (11, 12), (12, 10),
            (13, 14), (14, 13),
            (12, 13),
        ]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 2);
        assert_eq!(result.runs, vec![
            Some(13), Some(14), None,
            Some(10), Some(11), Some(12), None
        ]);
    }

    #[test]
    fn test_backedge() {
        let edges = Edges::new(vec![(10, 11), (11, 12), (12, 13), (13, 11)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 2);
        assert_eq!(result.runs, vec![
            Some(11), Some(12), Some(13), None,
            Some(10), None
        ]);
    }

    #[test]
    fn test_duplicate_edges() {
        let edges = Edges::new(vec![(10, 11), (10, 11), (11, 12), (12, 11), (11, 12)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 2);
        assert_eq!(result.runs, vec![
            Some(11), Some(12), None,
            Some(10), None
        ]);
    }

    #[test]
    fn test_disconnected() {
        let edges = Edges::new(vec![(10, 11), (15, 16)]);
        let result = scc(&edges, &[], 0);
        assert_eq!(result.count, 4);
        assert_eq!(result.runs, vec![
            Some(11), None,
            Some(10), None,
            Some(16), None,
            Some(15), None
        ]);
    }

    #[test]
    fn test_isolated_vertex() {
        let edges = Edges::<i32>::new(vec![]);
        let result = scc(&edges, &[42], 0);
        assert_eq!(result.count, 1);
        assert_eq!(result.runs, vec![Some(42), None]);
    }

    #[test]
    fn test_isolated_vertices_multiple() {
        let edges = Edges::<i32>::new(vec![]);
        let result = scc(&edges, &[10, 20, 30], 0);
        assert_eq!(result.count, 3);
        assert_eq!(result.runs, vec![
            Some(10), None,
            Some(20), None,
            Some(30), None
        ]);
    }

    #[test]
    fn test_vertex_already_in_edges() {
        let edges = Edges::new(vec![(10, 11)]);
        let result = scc(&edges, &[10, 11], 0);
        assert_eq!(result.count, 2);
        assert_eq!(result.runs, vec![
            Some(11), None,
            Some(10), None
        ]);
    }

    #[test]
    fn test_mixed_isolated_and_connected() {
        let edges = Edges::new(vec![(10, 11)]);
        let result = scc(&edges, &[42], 0);
        assert_eq!(result.count, 3);
        assert_eq!(result.runs, vec![
            Some(11), None,
            Some(10), None,
            Some(42), None
        ]);
    }
}
