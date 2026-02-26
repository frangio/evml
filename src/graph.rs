use std::{mem::replace, num::NonZero};
use crate::utils::{BitSet, ShiftStack};

pub trait Idx: Copy + Eq {
    fn new(index: usize) -> Self;
    fn index(self) -> usize;
}

impl Idx for usize {
    fn new(index: usize) -> Self {
        index
    }

    fn index(self) -> usize {
        self
    }
}

pub trait Graph {
    type Node: Idx;

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

pub trait NodeOrdering<N> {
    fn position(&self, node: N) -> usize;
    fn node_at(&self, position: usize) -> N;
    fn iter(&self) -> impl DoubleEndedIterator<Item = N> + ExactSizeIterator;
}

pub struct ArrayNodeOrdering<N: Idx> {
    nodes: Box<[N]>,
    positions: Box<[usize]>,
}

impl<N: Idx> ArrayNodeOrdering<N> {
    pub fn new(nodes: Box<[N]>) -> Self {
        let mut positions = vec![0; nodes.len()].into_boxed_slice();
        for (pos, &node) in nodes.iter().enumerate() {
            positions[node.index()] = pos;
        }
        Self { nodes, positions }
    }
}

impl<N: Idx> NodeOrdering<N> for ArrayNodeOrdering<N> {
    fn position(&self, node: N) -> usize {
        self.positions[node.index()]
    }

    fn node_at(&self, position: usize) -> N {
        self.nodes[position]
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = N> + ExactSizeIterator {
        self.nodes.iter().copied()
    }
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

pub fn idom<G: EntryNode + Predecessors>(g: &G, postorder: &impl NodeOrdering<G::Node>) -> Box<[G::Node]> {
    let enc = |v: G::Node| NonZero::new(postorder.position(v) + 1);
    let dec = |x: Option<NonZero<usize>>| postorder.node_at(x.map_or(0, NonZero::get) - 1);

    let mut parents = vec![None; g.node_count()];

    let entry = g.entry();
    parents[entry.index()] = enc(entry);

    let mut changed = true;
    while changed {
        changed = false;

        for v in postorder.iter().rev().skip(1) {
            let mut x = None;

            for u in g.predecessors(v) {
                if parents[u.index()].is_some() {
                    let mut y = enc(u);
                    if x.is_none() {
                        x = y;
                    } else {
                        while x != y {
                            if x < y {
                                x = parents[dec(x).index()];
                            } else {
                                y = parents[dec(y).index()];
                            }
                        }
                    }
                }
            }

            if x != replace(&mut parents[v.index()], x) {
                changed = true;
            }
        }
    }

    parents.into_iter().map(dec).collect()
}

pub fn ipdom<G: ExitNode + Successors>(cfg: &G) -> Box<[G::Node]> {
    let rev_cfg = transpose(cache_predecessors(cfg));
    let rev_postorder = postorder(&rev_cfg);
    idom(&transpose(cfg), &rev_postorder)
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

pub fn cache_predecessors<G: Successors>(g: G) -> CachedPredecessors<G> {
    let mut pred_start = vec![0; g.node_count()].into_boxed_slice();

    for v in g.nodes() {
        for w in g.successors(v) {
            let wi = w.index();
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
            let wi = w.index();
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

impl<G: Successors> Successors for CachedPredecessors<G> {
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.inner.successors(node)
    }
}

impl<G: Graph> Predecessors for CachedPredecessors<G> {
    fn predecessors(&self, node: G::Node) -> impl Iterator<Item = G::Node> {
        let index = node.index();
        let start = self.pred_start[index];
        let end = self.pred_start.get(index + 1).copied().unwrap_or(self.pred_nodes.len());
        self.pred_nodes[start..end].iter().copied()
    }
}

pub fn postorder<G: EntryNode + Successors>(g: G) -> ArrayNodeOrdering<G::Node> {
    let n = g.node_count();

    let mut flags = BitSet::new(2 * n);
    let visited = |v: G::Node| v.index();
    let seen = |v: G::Node| n + v.index();

    let mut buffer = ShiftStack::new(n);

    let entry = g.entry();
    flags.insert(seen(entry));
    buffer.push(entry);

    while let Some(&v) = buffer.top() {
        if flags.insert(visited(v)) {
            for w in g.successors(v) {
                if flags.insert(seen(w)) {
                    buffer.push(w);
                }
            }
        } else {
            buffer.shift();
        }
    }

    ArrayNodeOrdering::new(buffer.into_boxed_slice())
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::cell::OnceCell;

    pub struct TestGraph {
        pub node_count: usize,
        pub edges: Vec<(usize, usize)>,
        entry: OnceCell<usize>,
        exit: OnceCell<usize>,
        postorder: OnceCell<ArrayNodeOrdering<usize>>,
    }

    impl TestGraph {
        pub fn new(edges: &[(usize, usize)]) -> Self {
            let node_count = edges.iter().flat_map(|&(v, w)| [v, w]).max().map_or(0, |c| c + 1);
            Self::with_nodes(node_count, edges)
        }

        pub fn with_nodes(node_count: usize, edges: &[(usize, usize)]) -> Self {
            let edges = edges.to_vec();
            Self { node_count, edges, entry: OnceCell::new(), exit: OnceCell::new(), postorder: OnceCell::new() }
        }

        pub fn postorder(&self) -> &ArrayNodeOrdering<usize> {
            self.postorder.get_or_init(|| postorder(self))
        }
    }

    impl Graph for TestGraph {
        type Node = usize;

        fn node_count(&self) -> usize {
            self.node_count
        }

        fn nodes(&self) -> impl Iterator<Item = Self::Node> {
            0..self.node_count
        }
    }

    impl Predecessors for TestGraph {
        fn predecessors(&self, node: usize) -> impl Iterator<Item = usize> {
            self.edges.iter().filter_map(move |&(u, v)| (v == node).then_some(u))
        }
    }

    impl EntryNode for TestGraph {
        fn entry(&self) -> usize {
            *self.entry.get_or_init(|| {
                let mut entries = (0..self.node_count).filter(|&n| self.predecessors(n).next().is_none());
                let entry = entries.next().expect("no entry node found");
                assert!(entries.next().is_none(), "multiple entry nodes found");
                entry
            })
        }
    }

    impl ExitNode for TestGraph {
        fn exit(&self) -> usize {
            *self.exit.get_or_init(|| {
                let mut exits = (0..self.node_count).filter(|&n| self.successors(n).next().is_none());
                let exit = exits.next().expect("no exit node found");
                assert!(exits.next().is_none(), "multiple exit nodes found");
                exit
            })
        }
    }

    impl Successors for TestGraph {
        fn successors(&self, node: usize) -> impl Iterator<Item = usize> {
            self.edges.iter().filter_map(move |&(u, v)| (u == node).then_some(v))
        }
    }

    #[test]
    fn test_cache_predecessors() {
        // 0 → 1 → 2
        //     ↓
        //     3
        let g = TestGraph::new(&[
            (0, 1),
            (1, 2),
            (1, 3),
        ]);
        let cached = cache_predecessors(g);

        let preds_0: Vec<_> = cached.predecessors(0).collect();
        let preds_1: Vec<_> = cached.predecessors(1).collect();
        let preds_2: Vec<_> = cached.predecessors(2).collect();
        let preds_3: Vec<_> = cached.predecessors(3).collect();

        assert!(preds_0.is_empty());
        assert_eq!(preds_1, vec![0]);
        assert_eq!(preds_2, vec![1]);
        assert_eq!(preds_3, vec![1]);
    }

    #[test]
    fn test_idom_single_node() {
        // 0
        let g = TestGraph::with_nodes(1, &[]);
        let result = idom(&g, g.postorder());
        assert_eq!(result[0], 0);
    }

    #[test]
    fn test_idom_linear() {
        // 0 → 1 → 2
        let g = TestGraph::new(&[
            (0, 1),
            (1, 2),
        ]);
        let result = idom(&g, g.postorder());
        assert_eq!(result[0], 0);
        assert_eq!(result[1], 0);
        assert_eq!(result[2], 1);
    }

    #[test]
    fn test_idom_diamond() {
        //   0
        //  ↙ ↘
        // 1   2
        //  ↘ ↙
        //   3
        let g = TestGraph::new(&[
            (0, 1),
            (0, 2),
            (1, 3),
            (2, 3),
        ]);
        let result = idom(&g, g.postorder());
        assert_eq!(result[0], 0);
        assert_eq!(result[1], 0);
        assert_eq!(result[2], 0);
        assert_eq!(result[3], 0);
    }

    #[test]
    fn test_idom_simple_loop() {
        // 0 → 1 → 2
        //     ↑   ↓
        //     └───┘
        let g = TestGraph::new(&[
            (0, 1),
            (1, 2),
            (2, 1),
        ]);
        let result = idom(&g, g.postorder());
        assert_eq!(result[0], 0);
        assert_eq!(result[1], 0);
        assert_eq!(result[2], 1);
    }

    #[test]
    fn test_idom_nested_loops() {
        // 0 → 1 → 2 → 3
        //     ↑   ↑   ↓
        //     │   └───┘
        //     └───────┘
        let g = TestGraph::new(&[
            (0, 1),
            (1, 2),
            (2, 3),
            (3, 2),
            (3, 1),
        ]);
        let result = idom(&g, g.postorder());
        assert_eq!(result[0], 0);
        assert_eq!(result[1], 0);
        assert_eq!(result[2], 1);
        assert_eq!(result[3], 2);
    }

    #[test]
    fn test_idom_irreducible() {
        //   0
        //  ↙ ↘
        // 1 ↔ 2
        let g = TestGraph::new(&[
            (0, 1),
            (0, 2),
            (1, 2),
            (2, 1),
        ]);
        let result = idom(&g, g.postorder());
        assert_eq!(result[0], 0);
        assert_eq!(result[1], 0);
        assert_eq!(result[2], 0);
    }
}
