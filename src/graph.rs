use std::{iter, mem::replace, num::NonZero};
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
    fn predecessors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node>;
}

pub trait Successors: Graph {
    fn successors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node>;
}

pub trait Dfs: Graph {
    fn dfs(&self) -> impl Iterator<Item = NodeVisit<Self::Node>>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NodeVisit<N> {
    pub node: N,
    pub exit: bool,
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
    fn predecessors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        (*self).predecessors(node)
    }
}

impl<G: Successors + ?Sized> Successors for &G {
    fn successors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        (*self).successors(node)
    }
}

impl<'a, G: Dfs + ?Sized> Dfs for &'a G {
    fn dfs(&self) -> impl Iterator<Item = NodeVisit<Self::Node>> + use<'_, 'a, G> {
        (*self).dfs()
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
    fn predecessors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        self.inner.successors(node)
    }
}

impl<G: Predecessors> Successors for Transpose<G> {
    fn successors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
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
    pub fn edges_from(&self, node: N) -> &[N] {
        let index = node.index();
        let start = self.node_starts[index];
        let end = self
            .node_starts
            .get(index + 1)
            .copied()
            .unwrap_or(self.edge_targets.len());
        &self.edge_targets[start..end]
    }
}

pub struct Tree<N> {
    root: N,
    parents: Box<[Option<N>]>,
    children: EdgeArray<N>,
    intervals: Box<[(usize, usize)]>,
    height: usize,
}

impl<N: Idx> Tree<N> {
    pub fn new(root: N, parents: Box<[Option<N>]>) -> Self {
        assert!(parents[root.index()].is_none());
        let mut tree = Self {
            root,
            parents,
            children: EdgeArray::default(),
            intervals: Box::new([]),
            height: 0,
        };
        tree.children = predecessor_edges(transpose(&tree));
        (tree.intervals, tree.height) = dfs_intervals(&tree);
        tree
    }

    pub fn parent(&self, node: N) -> Option<N> {
        self.parents[node.index()]
    }

    pub fn height(&self) -> usize {
        self.height
    }

    pub fn is_ancestor(&self, a: N, b: N) -> bool {
        let (a_start, a_end) = self.intervals[a.index()];
        let (b_start, b_end) = self.intervals[b.index()];
        a_start <= b_start && b_end <= a_end
    }

    pub fn nca(&self, mut lhs: N, mut rhs: N) -> N {
        loop {
            if self.is_ancestor(lhs, rhs) {
                return lhs;
            }
            if self.is_ancestor(rhs, lhs) {
                return rhs;
            }
            lhs = self.parent(lhs).unwrap();
            rhs = self.parent(rhs).unwrap();
        }
    }
}

fn dfs_intervals<G: Dfs>(g: &G) -> (Box<[(usize, usize)]>, usize) {
    let n = g.node_count();

    let mut ranges = vec![(0, 0); n].into_boxed_slice();
    let mut time = 0;
    let mut depth = 0;
    let mut height = 0;

    for visit in g.dfs() {
        let node = visit.node;
        if !visit.exit {
            ranges[node.index()].0 = time;
            time += 1;
            depth += 1;
            height = height.max(depth);
        } else {
            ranges[node.index()].1 = time;
            depth -= 1;
        }
    }

    (ranges, height)
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
    fn successors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        self.children.edges_from(node).iter().copied()
    }
}

impl<N: Idx> Predecessors for Tree<N> {
    fn predecessors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        self.parents[node.index()].into_iter()
    }
}

impl<N: Idx> Dfs for Tree<N> {
    fn dfs(&self) -> impl Iterator<Item = NodeVisit<Self::Node>> {
        let mut stack = Vec::with_capacity(self.height);
        iter::successors(Some(NodeVisit { node: self.entry(), exit: false }), move |&visit| {
            let node = if visit.exit {
                stack.pop();
                self.parent(visit.node)?
            } else {
                stack.push(0);
                visit.node
            };
            let i = stack.last_mut().unwrap();
            if let Some(&succ) = self.children.edges_from(node).get(*i) {
                *i += 1;
                Some(NodeVisit { node: succ, exit: false })
            } else {
                Some(NodeVisit { node, exit: true })
            }
        })
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
    use std::{cell::OnceCell, collections::HashMap};

    pub struct TestGraph {
        pub node_count: usize,
        succs: HashMap<usize, Vec<usize>>,
        preds: HashMap<usize, Vec<usize>>,
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
            let mut succs = HashMap::<usize, Vec<usize>>::new();
            let mut preds = HashMap::<usize, Vec<usize>>::new();
            for &(u, v) in edges {
                succs.entry(u).or_default().push(v);
                preds.entry(v).or_default().push(u);
            }
            Self {
                node_count,
                succs,
                preds,
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
        fn predecessors(&self, node: usize) -> impl ExactSizeIterator<Item = usize> {
            self.preds.get(&node).map(Vec::as_slice).unwrap_or(&[]).iter().copied()
        }
    }

    impl EntryNode for TestGraph {
        fn entry(&self) -> usize {
            *self.entry.get_or_init(|| {
                let mut entries =
                    (0..self.node_count).filter(|&n| self.predecessors(n).len() == 0);
                let entry = entries.next().expect("no entry node found");
                assert!(entries.next().is_none(), "multiple entry nodes found");
                entry
            })
        }
    }

    impl Successors for TestGraph {
        fn successors(&self, node: usize) -> impl ExactSizeIterator<Item = usize> {
            self.succs.get(&node).map(Vec::as_slice).unwrap_or(&[]).iter().copied()
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

        let preds_0 = preds.edges_from(0);
        let preds_1 = preds.edges_from(1);
        let preds_2 = preds.edges_from(2);
        let preds_3 = preds.edges_from(3);

        assert!(preds_0.is_empty());
        assert_eq!(preds_1, &[0]);
        assert_eq!(preds_2, &[1]);
        assert_eq!(preds_3, &[1]);
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
