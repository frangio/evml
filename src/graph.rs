use std::{collections::VecDeque, hash::Hash, mem::replace, num::NonZero};

use crate::utils::BitSet;

pub trait Graph {
    type Node: Copy + Eq;

    fn node_count(&self) -> usize;
    fn nodes(&self) -> impl Iterator<Item = Self::Node>;
}

pub trait EntryNode: Graph {
    fn entry(&self) -> Self::Node;
}

pub trait ExitNode: Graph {
    fn exit(&self) -> Self::Node;
}


pub trait Predecessors: Graph {
    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node>;
}

pub trait Successors: Graph {
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node>;
}

pub trait Postorder: Graph {
    fn postorder(&self, node: Self::Node) -> usize;
    fn at_postorder(&self, index: usize) -> Self::Node;

    fn postorder_iter(&self) -> impl DoubleEndedIterator<Item = Self::Node> {
        (0..self.node_count()).map(|i| self.at_postorder(i))
    }
}

pub trait Numbered: Graph {
    fn number(&self, node: Self::Node) -> usize;
    fn numbered(&self, number: usize) -> Self::Node;
}

impl<G: Graph + ?Sized> Graph for &G {
    type Node = G::Node;

    fn node_count(&self) -> usize {
        (*self).node_count()
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        (*self).nodes()
    }
}

impl<G: EntryNode + ?Sized> EntryNode for &G {
    fn entry(&self) -> Self::Node {
        (*self).entry()
    }
}

impl<G: ExitNode + ?Sized> ExitNode for &G {
    fn exit(&self) -> Self::Node {
        (*self).exit()
    }
}

impl<G: Predecessors + ?Sized> Predecessors for &G {
    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        (*self).predecessors(node)
    }
}

impl<G: Successors + ?Sized> Successors for &G {
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        (*self).successors(node)
    }
}

impl<G: Postorder + ?Sized> Postorder for &G {
    fn at_postorder(&self, index: usize) -> Self::Node {
        (*self).at_postorder(index)
    }

    fn postorder(&self, node: Self::Node) -> usize {
        (*self).postorder(node)
    }

    fn postorder_iter(&self) -> impl DoubleEndedIterator<Item = Self::Node> {
        (*self).postorder_iter()
    }
}

impl<G: Numbered + ?Sized> Numbered for &G {
    fn number(&self, node: Self::Node) -> usize {
        (*self).number(node)
    }

    fn numbered(&self, number: usize) -> Self::Node {
        (*self).numbered(number)
    }
}

pub fn idom<G: EntryNode + Predecessors + Postorder + Numbered>(g: &G) -> Box<[G::Node]> {
    let enc = |v: G::Node| NonZero::new(g.postorder(v) + 1);
    let dec = |x: Option<NonZero<usize>>| g.at_postorder(x.map_or(0, NonZero::get) - 1);

    let mut parents = vec![None; g.node_count()];

    let entry = g.entry();
    parents[g.number(entry)] = enc(entry);

    let mut changed = true;
    while changed {
        changed = false;

        for v in g.postorder_iter().rev().skip(1) {
            let mut x = None;

            for u in g.predecessors(v) {
                if parents[g.number(u)].is_some() {
                    let mut y = enc(u);
                    if x.is_none() {
                        x = y;
                    } else {
                        while x != y {
                            if x < y {
                                x = parents[g.number(dec(x))];
                            } else {
                                y = parents[g.number(dec(y))];
                            }
                        }
                    }
                }
            }

            if x != replace(&mut parents[g.number(v)], x) {
                changed = true;
            }
        }
    }

    parents.into_iter().map(dec).collect()
}

pub fn transpose<G>(g: G) -> Transpose<G> {
    Transpose { inner: g }
}

pub struct Transpose<G> {
    inner: G,
}

impl<G: Graph> Graph for Transpose<G> {
    type Node = G::Node;

    fn node_count(&self) -> usize {
        self.inner.node_count()
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        self.inner.nodes()
    }
}

impl<G: ExitNode> EntryNode for Transpose<G> {
    fn entry(&self) -> Self::Node {
        self.inner.exit()
    }
}

impl<G: EntryNode> ExitNode for Transpose<G> {
    fn exit(&self) -> Self::Node {
        self.inner.entry()
    }
}

impl<G: Successors> Predecessors for Transpose<G> {
    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.inner.successors(node)
    }
}

impl<G: Predecessors> Successors for Transpose<G> {
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.inner.predecessors(node)
    }
}

impl<G: Numbered> Numbered for Transpose<G> {
    fn number(&self, node: Self::Node) -> usize {
        self.inner.number(node)
    }

    fn numbered(&self, number: usize) -> Self::Node {
        self.inner.numbered(number)
    }
}

pub fn cache_predecessors<G: Numbered + Successors>(g: G) -> CachedPredecessors<G> {
    let mut pred_start = vec![0; g.node_count()].into_boxed_slice();

    for v in g.nodes() {
        for w in g.successors(v) {
            let wi = g.number(w);
            pred_start[wi] += 1;
        }
    }

    let mut total = 0;
    for count in pred_start.iter_mut() {
        total += *count;
        *count = total;
    }

    let mut pred_nodes = Box::new_uninit_slice(total);

    for v in g.nodes() {
        for w in g.successors(v) {
            let wi = g.number(w);
            pred_start[wi] -= 1;
            pred_nodes[pred_start[wi]].write(v);
        }
    }

    let pred_nodes = unsafe { pred_nodes.assume_init() };

    CachedPredecessors { inner: g, pred_start, pred_nodes }
}

pub struct CachedPredecessors<G: Graph> {
    inner: G,
    pred_start: Box<[usize]>,
    pred_nodes: Box<[G::Node]>,
}

impl<G: Graph> Graph for CachedPredecessors<G> {
    type Node = G::Node;

    fn node_count(&self) -> usize {
        self.inner.node_count()
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        self.inner.nodes()
    }
}

impl<G: ExitNode> ExitNode for CachedPredecessors<G> {
    fn exit(&self) -> G::Node {
        self.inner.exit()
    }
}

impl<G: Numbered> Numbered for CachedPredecessors<G> {
    fn number(&self, node: G::Node) -> usize {
        self.inner.number(node)
    }

    fn numbered(&self, number: usize) -> G::Node {
        self.inner.numbered(number)
    }
}

impl<G: Numbered> Predecessors for CachedPredecessors<G> {
    fn predecessors(&self, node: G::Node) -> impl Iterator<Item = G::Node> {
        let index = self.inner.number(node);
        let start = self.pred_start[index];
        let end = self.pred_start.get(index + 1).copied().unwrap_or(self.pred_nodes.len());
        self.pred_nodes[start..end].iter().copied()
    }
}

pub fn postorder<G: EntryNode + Successors + Numbered>(g: &G) -> Box<[G::Node]> {
    let n = g.node_count();

    let mut flags = BitSet::new(2 * n);
    let visited = |v| g.number(v);
    let seen = |v| n + g.number(v);

    let mut buffer = Box::new_uninit_slice(n);
    let mut input = n;
    let mut output = 0;

    let entry = g.entry();

    flags.insert(seen(entry));
    input -= 1;
    buffer[input].write(entry);

    while flags.unset() > 0 {
        let v = unsafe { buffer[input].assume_init_read() };
        if flags.insert(visited(v)) {
            for w in g.successors(v) {
                if flags.insert(seen(w)) {
                    input -= 1;
                    buffer[input].write(w);
                }
            }
        } else {
            buffer.swap(input, output);
            input += 1;
            output += 1;
        }
    }

    unsafe { buffer.assume_init() }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet};
    use std::iter::zip;

    pub struct TestGraph<T> {
        edges: Vec<(T, T)>,
        postorder: Vec<T>,
    }

    impl<T: Copy + Eq + Hash> TestGraph<T> {
        pub fn new(start: T, edges: &[(T, T)]) -> Self {
            let edges = edges.to_vec();
            let mut postorder = vec![];
            let mut visited: HashSet<T> = HashSet::new();
            let mut stack = vec![(start, false)];
            while let Some((node, post)) = stack.pop() {
                if post {
                    postorder.push(node);
                } else if visited.insert(node) {
                    stack.push((node, true));
                    for &(u, v) in &edges {
                        if u == node {
                            stack.push((v, false));
                        }
                    }
                }
            }

            Self { edges, postorder }
        }
    }

    impl<T: Copy + Eq + Hash> Graph for TestGraph<T> {
        type Node = T;

        fn node_count(&self) -> usize {
            self.postorder.len()
        }

        fn nodes(&self) -> impl Iterator<Item = Self::Node> {
            self.postorder.iter().copied()
        }
    }

    impl<T: Copy + Eq + Hash> Predecessors for TestGraph<T> {
        fn predecessors(&self, node: T) -> impl Iterator<Item = T> {
            self.edges.iter().filter_map(move |&(u, v)| (v == node).then_some(u))
        }
    }

    impl<T: Copy + Eq + Hash> EntryNode for TestGraph<T> {
        fn entry(&self) -> T {
            *self.postorder.last().unwrap()
        }
    }

    impl<T: Copy + Eq + Hash> ExitNode for TestGraph<T> {
        fn exit(&self) -> T {
            *self.postorder.first().unwrap()
        }
    }

    impl<T: Copy + Eq + Hash> Successors for TestGraph<T> {
        fn successors(&self, node: T) -> impl Iterator<Item = T> {
            self.edges.iter().filter_map(move |&(u, v)| (u == node).then_some(v))
        }
    }

    impl<T: Copy + Eq + Hash> Postorder for TestGraph<T> {
        fn at_postorder(&self, index: usize) -> T {
            self.postorder[index]
        }

        fn postorder(&self, node: T) -> usize {
            self.postorder.iter().position(|&n| n == node).unwrap()
        }
    }

    impl<T: Copy + Eq + Hash> Numbered for TestGraph<T> {
        fn number(&self, node: T) -> usize {
            self.postorder.iter().position(|&n| n == node).unwrap()
        }

        fn numbered(&self, number: usize) -> T {
            self.postorder[number]
        }
    }

    #[test]
    fn test_cache_predecessors() {
        // A → B → C
        //     ↓
        //     D
        let g = TestGraph::new("A", &[
            ("A", "B"),
            ("B", "C"),
            ("B", "D"),
        ]);
        let cached = cache_predecessors(g);

        let preds_a: Vec<_> = cached.predecessors("A").collect();
        let preds_b: Vec<_> = cached.predecessors("B").collect();
        let preds_c: Vec<_> = cached.predecessors("C").collect();
        let preds_d: Vec<_> = cached.predecessors("D").collect();

        assert!(preds_a.is_empty());
        assert_eq!(preds_b, vec!["A"]);
        assert_eq!(preds_c, vec!["B"]);
        assert_eq!(preds_d, vec!["B"]);
    }

    #[test]
    fn test_idom_single_node() {
        // A
        let g = TestGraph::new("A", &[]);
        let result = idom(&g);
        let result: HashMap<_, _> = zip(g.postorder, result).collect();
        assert_eq!(result["A"], "A");
    }

    #[test]
    fn test_idom_linear() {
        // A → B → C
        let g = TestGraph::new("A", &[
            ("A", "B"),
            ("B", "C"),
        ]);
        let result = idom(&g);
        let result: HashMap<_, _> = zip(g.postorder, result).collect();
        assert_eq!(result["B"], "A");
        assert_eq!(result["C"], "B");
    }

    #[test]
    fn test_idom_diamond() {
        //   A
        //  ↙ ↘
        // B   C
        //  ↘ ↙
        //   D
        let g = TestGraph::new("A", &[
            ("A", "B"),
            ("A", "C"),
            ("B", "D"),
            ("C", "D"),
        ]);
        let result = idom(&g);
        let result: HashMap<_, _> = zip(g.postorder, result).collect();
        assert_eq!(result["B"], "A");
        assert_eq!(result["C"], "A");
        assert_eq!(result["D"], "A");
    }

    #[test]
    fn test_idom_simple_loop() {
        // A → B → C
        //     ↑   ↓
        //     └───┘
        let g = TestGraph::new("A", &[
            ("A", "B"),
            ("B", "C"),
            ("C", "B"),
        ]);
        let result = idom(&g);
        let result: HashMap<_, _> = zip(g.postorder, result).collect();
        assert_eq!(result["B"], "A");
        assert_eq!(result["C"], "B");
    }

    #[test]
    fn test_idom_nested_loops() {
        // A → B → C → D
        //     ↑   ↑   ↓
        //     │   └───┘
        //     └───────┘
        let g = TestGraph::new("A", &[
            ("A", "B"),
            ("B", "C"),
            ("C", "D"),
            ("D", "C"),
            ("D", "B"),
        ]);
        let result = idom(&g);
        let result: HashMap<_, _> = zip(g.postorder, result).collect();
        assert_eq!(result["B"], "A");
        assert_eq!(result["C"], "B");
        assert_eq!(result["D"], "C");
    }

    #[test]
    fn test_idom_irreducible() {
        //   A
        //  ↙ ↘
        // B ↔ C
        let g = TestGraph::new("A", &[
            ("A", "B"),
            ("A", "C"),
            ("B", "C"),
            ("C", "B"),
        ]);
        let result = idom(&g);
        let result: HashMap<_, _> = zip(g.postorder, result).collect();
        assert_eq!(result["B"], "A");
        assert_eq!(result["C"], "A");
    }
}
