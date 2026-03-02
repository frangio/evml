use std::{mem::replace, num::NonZero, ops::Range};
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

pub fn idom<G>(g: &G, postorder: &impl NodeOrdering<G::Node>) -> Box<[Option<G::Node>]>
where
    G: EntryNode + Predecessors,
{
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

    let mut idom = parents
        .into_iter()
        .map(|x| Some(dec(x)))
        .collect::<Box<[_]>>();
    idom[entry.index()] = None;
    idom
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DFSVisit<N> {
    pub node: N,
    pub exit: bool,
}

pub fn dfs<G: EntryNode + Successors>(g: &G) -> DFS<'_, G> {
    DFS::new(g)
}

pub struct DFS<'a, G: Graph + ?Sized> {
    graph: &'a G,
    flags: BitSet,
    buffer: Vec<G::Node>,
}

impl<'a, G: EntryNode + Successors> DFS<'a, G> {
    fn new(graph: &'a G) -> Self {
        let n = graph.node_count();
        let mut flags = BitSet::new(2 * n);
        let mut buffer = Vec::with_capacity(n);

        let entry = graph.entry();
        flags.insert(2 * entry.index() + 1);
        buffer.push(entry);

        Self { graph, flags, buffer }
    }
}

impl<G: EntryNode + Successors> Iterator for DFS<'_, G> {
    type Item = DFSVisit<G::Node>;

    fn next(&mut self) -> Option<Self::Item> {
        let &node = self.buffer.last()?;
        if self.flags.insert(2 * node.index()) {
            for succ in self.graph.successors(node) {
                if self.flags.insert(2 * succ.index() + 1) {
                    self.buffer.push(succ);
                }
            }
            Some(DFSVisit { node, exit: false })
        } else {
            self.buffer.pop();
            Some(DFSVisit { node, exit: true })
        }
    }
}

pub fn dfs_intervals<G: EntryNode + Successors>(g: &G) -> Box<[Range<usize>]> {
    let n = g.node_count();

    let mut ranges = vec![0..0; n].into_boxed_slice();
    let mut time = 0;

    for visit in dfs(g) {
        let node = visit.node;
        if !visit.exit {
            ranges[node.index()].start = time;
            time += 1;
        } else {
            ranges[node.index()].end = time;
        }
    }

    ranges
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

pub struct EdgeArray<N> {
    node_starts: Box<[usize]>,
    edge_targets: Box<[N]>,
}

impl<N> Default for EdgeArray<N> {
    fn default() -> Self {
        Self {
            node_starts: Box::new([]),
            edge_targets: Box::new([]),
        }
    }
}

impl<N: Idx> EdgeArray<N> {
    pub fn edges_from(&self, node: N) -> impl Iterator<Item = N> {
        let index = node.index();
        let start = self.node_starts[index];
        let end = self
            .node_starts
            .get(index + 1)
            .copied()
            .unwrap_or(self.edge_targets.len());
        self.edge_targets[start..end].iter().copied()
    }
}

pub struct Tree<N> {
    root: N,
    parents: Box<[Option<N>]>,
    children: EdgeArray<N>,
}

impl<N: Idx> Tree<N> {
    pub fn new(root: N, parents: Box<[Option<N>]>) -> Self {
        assert!(parents[root.index()].is_none());
        let mut tree = Self {
            root,
            parents,
            children: EdgeArray::default(),
        };
        tree.children = predecessor_edges(transpose(&tree));
        tree
    }

    pub fn parent(&self, node: N) -> Option<N> {
        self.parents[node.index()]
    }
}

impl<N: Idx> Graph for Tree<N> {
    type Node = N;

    fn node_count(&self) -> usize {
        self.parents.len()
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        (0..self.parents.len()).map(N::new)
    }
}

impl<N: Idx> EntryNode for Tree<N> {
    fn entry(&self) -> Self::Node {
        self.root
    }
}

impl<N: Idx> Successors for Tree<N> {
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.children.edges_from(node)
    }
}

impl<N: Idx> Predecessors for Tree<N> {
    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.parents[node.index()].into_iter()
    }
}

pub fn predecessor_edges<G: Successors>(g: G) -> EdgeArray<G::Node> {
    let mut node_starts = vec![0; g.node_count()].into_boxed_slice();

    for v in g.nodes() {
        for w in g.successors(v) {
            let wi = w.index();
            node_starts[wi] += 1;
        }
    }

    let mut total = 0;
    for count in node_starts.iter_mut() {
        total += *count;
        *count = total;
    }

    let mut edge_targets = Box::new_uninit_slice(total);

    for v in g.nodes() {
        for w in g.successors(v) {
            let wi = w.index();
            node_starts[wi] -= 1;
            edge_targets[node_starts[wi]].write(v);
        }
    }

    let edge_targets = unsafe { edge_targets.assume_init() };

    EdgeArray {
        node_starts,
        edge_targets,
    }
}

#[allow(unused)]
pub fn postorder<G: EntryNode + Successors>(g: G) -> Box<[G::Node]> {
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

    buffer.into_boxed_slice()
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::cell::OnceCell;

    pub struct TestGraph {
        pub node_count: usize,
        pub edges: Vec<(usize, usize)>,
        entry: OnceCell<usize>,
    }

    impl TestGraph {
        pub fn new(edges: &[(usize, usize)]) -> Self {
            let node_count = edges
                .iter()
                .flat_map(|&(v, w)| [v, w])
                .max()
                .map_or(0, |c| c + 1);
            Self::with_nodes(node_count, edges)
        }

        pub fn with_nodes(node_count: usize, edges: &[(usize, usize)]) -> Self {
            let edges = edges.to_vec();
            Self {
                node_count,
                edges,
                entry: OnceCell::new(),
            }
        }

        pub fn postorder(&self) -> impl NodeOrdering<usize> {
            struct Postorder<N> {
                nodes: Box<[N]>,
                positions: Box<[usize]>,
            }

            impl<N: Idx> NodeOrdering<N> for Postorder<N> {
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

            let nodes = postorder(self);

            let mut positions = vec![0; self.node_count()].into_boxed_slice();
            for (pos, &node) in nodes.iter().enumerate() {
                positions[node.index()] = pos;
            }

            Postorder { nodes, positions }
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
            self.edges
                .iter()
                .filter_map(move |&(u, v)| (v == node).then_some(u))
        }
    }

    impl EntryNode for TestGraph {
        fn entry(&self) -> usize {
            *self.entry.get_or_init(|| {
                let mut entries =
                    (0..self.node_count).filter(|&n| self.predecessors(n).next().is_none());
                let entry = entries.next().expect("no entry node found");
                assert!(entries.next().is_none(), "multiple entry nodes found");
                entry
            })
        }
    }

    impl Successors for TestGraph {
        fn successors(&self, node: usize) -> impl Iterator<Item = usize> {
            self.edges
                .iter()
                .filter_map(move |&(u, v)| (u == node).then_some(v))
        }
    }

    #[test]
    fn test_predecessor_edges() {
        // 0 → 1 → 2
        //     ↓
        //     3
        let g = TestGraph::new(&[
            (0, 1),
            (1, 2),
            (1, 3),
        ]);
        let preds = predecessor_edges(&g);

        let preds_0: Vec<_> = preds.edges_from(0).collect();
        let preds_1: Vec<_> = preds.edges_from(1).collect();
        let preds_2: Vec<_> = preds.edges_from(2).collect();
        let preds_3: Vec<_> = preds.edges_from(3).collect();

        assert!(preds_0.is_empty());
        assert_eq!(preds_1, vec![0]);
        assert_eq!(preds_2, vec![1]);
        assert_eq!(preds_3, vec![1]);
    }

    #[test]
    fn test_dfs() {
        // 0 → 1 → 2
        //   ↘ 3
        let g = TestGraph::new(&[
            (0, 1),
            (1, 2),
            (0, 3),
        ]);

        let visits: Vec<_> = dfs(&g).collect();

        assert_eq!(
            visits,
            vec![
                DFSVisit { node: 0, exit: false },
                DFSVisit { node: 3, exit: false },
                DFSVisit { node: 3, exit: true },
                DFSVisit { node: 1, exit: false },
                DFSVisit { node: 2, exit: false },
                DFSVisit { node: 2, exit: true },
                DFSVisit { node: 1, exit: true },
                DFSVisit { node: 0, exit: true },
            ]
        );
    }

    #[test]
    fn test_postorder_matches_dfs_exit_order() {
        // 0 → 1 → 2
        //   ↘ 3
        let g = TestGraph::new(&[
            (0, 1),
            (1, 2),
            (0, 3),
        ]);

        let expected: Vec<_> = dfs(&g)
            .filter_map(|visit| visit.exit.then_some(visit.node))
            .collect();

        assert_eq!(&*postorder(&g), expected.as_slice());
    }

    #[test]
    fn test_idom_single_node() {
        // 0
        let g = TestGraph::with_nodes(1, &[]);
        let result = idom(&g, &g.postorder());
        assert_eq!(result[0], None);
    }

    #[test]
    fn test_idom_linear() {
        // 0 → 1 → 2
        let g = TestGraph::new(&[
            (0, 1),
            (1, 2),
        ]);
        let result = idom(&g, &g.postorder());
        assert_eq!(result[0], None);
        assert_eq!(result[1], Some(0));
        assert_eq!(result[2], Some(1));
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
        let result = idom(&g, &g.postorder());
        assert_eq!(result[0], None);
        assert_eq!(result[1], Some(0));
        assert_eq!(result[2], Some(0));
        assert_eq!(result[3], Some(0));
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
        let result = idom(&g, &g.postorder());
        assert_eq!(result[0], None);
        assert_eq!(result[1], Some(0));
        assert_eq!(result[2], Some(1));
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
        let result = idom(&g, &g.postorder());
        assert_eq!(result[0], None);
        assert_eq!(result[1], Some(0));
        assert_eq!(result[2], Some(1));
        assert_eq!(result[3], Some(2));
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
        let result = idom(&g, &g.postorder());
        assert_eq!(result[0], None);
        assert_eq!(result[1], Some(0));
        assert_eq!(result[2], Some(0));
    }
}
