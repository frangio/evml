use std::{collections::{HashMap, HashSet}, hash::Hash, num::NonZero};

pub trait Graph {
    type Node: Copy + Eq + Hash;
    fn node_count(&self) -> usize;
}

pub trait StartNode: Graph {
    fn start(&self) -> Self::Node;
}

pub trait Predecessors: Graph {
    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node>;
}

pub trait Successors: Graph {
    fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node>;
}

pub trait DepthFirstPostorder: Graph + StartNode {
    fn node(&self, index: usize) -> Self::Node;
    fn predecessors_indices(&self, index: usize) -> impl Iterator<Item = usize>
    where Self: Predecessors;
    fn successors_indices(&self, index: usize) -> impl Iterator<Item = usize>
    where Self: Successors;
}

pub fn idom<G: DepthFirstPostorder + Predecessors>(g: &G) -> HashMap<G::Node, G::Node> {
    let enc = |v: usize| NonZero::new(v + 1);
    let dec = |x: Option<NonZero<usize>>| x.map_or(0, NonZero::get).wrapping_sub(1);

    let start_index = g.node_count() - 1;

    let mut parents = vec![None; g.node_count()];
    parents[start_index] = enc(start_index);

    let mut changed = true;
    while changed {
        changed = false;

        for v in (0..start_index).rev() {
            let mut x = None;

            for u in g.predecessors_indices(v) {
                if parents[u].is_some() {
                    let mut y = enc(u);
                    if x.is_none() {
                        x = y;
                    } else {
                        while x != y {
                            if x < y {
                                x = parents[dec(x)];
                            } else {
                                y = parents[dec(y)];
                            }
                        }
                    }
                }
            }

            if x != parents[v] {
                parents[v] = x;
                changed = true;
            }
        }
    }

    let mut idom = HashMap::with_capacity(g.node_count() - 1);
    idom.extend(
        (0..start_index).map(|i| {
            let v = g.node(i);
            let u = g.node(dec(parents[i]));
            (v, u)
        })
    );
    idom
}

#[derive(Clone, Copy)]
pub struct Instruction<'a, T> {
    pub defs: &'a [T],
    pub uses: &'a [T],
}

pub trait Procedure {
    type BlockId: Copy + Eq + Hash;
    type VarId: Copy + Eq + Hash;
    fn cfg(&self) -> impl DepthFirstPostorder<Node = Self::BlockId> + Successors;
    fn instructions(
        &self,
        b: Self::BlockId,
    ) -> impl DoubleEndedIterator<Item = Instruction<'_, Self::VarId>> + ExactSizeIterator;
}

/// Returns the last use instruction index for each live variable per block.
/// `None` means the variable is live-out.
pub fn liveness<P: Procedure>(proc: &P) -> HashMap<P::BlockId, HashMap<P::VarId, Option<usize>>> {
    let cfg = proc.cfg();
    let n = cfg.node_count();

    let mut result: HashMap<P::BlockId, HashMap<P::VarId, Option<usize>>> = HashMap::with_capacity(n);

    for i in 0..n {
        let block = cfg.node(i);
        let mut live = HashMap::new();

        for j in cfg.successors_indices(i) {
            if j < i {
                for &x in result[&cfg.node(j)].keys() {
                    live.insert(x, None);
                }
            } else {
                unimplemented!("cycles");
            }
        }

        for (i, instr) in proc.instructions(block).enumerate().rev() {
            for &x in instr.uses {
                live.insert(x, Some(i));
            }

            for &x in instr.defs {
                live.entry(x).or_insert(Some(i));
            }
        }

        result.insert(block, live);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestGraph<T> {
        edges: Vec<(T, T)>,
        postorder: Vec<T>,
    }

    impl<T: Copy + Eq + Hash> TestGraph<T> {
        fn new(start: T, edges: &[(T, T)]) -> Self {
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

        fn index(&self, node: T) -> usize {
            self.postorder.iter().position(|&n| n == node).unwrap()
        }
    }

    impl<T: Copy + Eq + Hash> Graph for TestGraph<T> {
        type Node = T;
        fn node_count(&self) -> usize {
            self.postorder.len()
        }
    }

    impl<T: Copy + Eq + Hash> Predecessors for TestGraph<T> {
        fn predecessors(&self, node: T) -> impl Iterator<Item = T> {
            self.edges.iter().filter_map(move |&(u, v)| (v == node).then_some(u))
        }
    }

    impl<T: Copy + Eq + Hash> StartNode for TestGraph<T> {
        fn start(&self) -> T {
            *self.postorder.last().unwrap()
        }
    }

    impl<T: Copy + Eq + Hash> Successors for TestGraph<T> {
        fn successors(&self, node: T) -> impl Iterator<Item = T> {
            self.edges.iter().filter_map(move |&(u, v)| (u == node).then_some(v))
        }
    }

    impl<T: Copy + Eq + Hash> DepthFirstPostorder for TestGraph<T> {
        fn node(&self, index: usize) -> T {
            self.postorder[index]
        }

        fn predecessors_indices(&self, index: usize) -> impl Iterator<Item = usize> {
            let node = self.node(index);
            self.predecessors(node).map(|u| self.index(u))
        }

        fn successors_indices(&self, index: usize) -> impl Iterator<Item = usize> {
            let node = self.node(index);
            self.successors(node).map(|u| self.index(u))
        }
    }

    #[test]
    fn test_idom_single_node() {
        // A
        let g = TestGraph::new("A", &[]);
        let result = idom(&g);
        assert!(result.is_empty());
    }

    #[test]
    fn test_idom_linear() {
        // A → B → C
        let g = TestGraph::new("A", &[
            ("A", "B"),
            ("B", "C"),
        ]);
        let result = idom(&g);
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
        assert_eq!(result["B"], "A");
        assert_eq!(result["C"], "A");
    }

    struct TestProcedure<B, V: 'static> {
        cfg: TestGraph<B>,
        instructions: HashMap<B, &'static [Instruction<'static, V>]>,
    }

    impl<B: Copy + Eq + Hash, V> TestProcedure<B, V> {
        fn new(
            start: B,
            edges: &[(B, B)],
            instructions: &[(B, &'static [Instruction<'static, V>])],
        ) -> Self {
            let cfg = TestGraph::new(start, edges);
            let instructions = instructions.iter().copied().collect();
            Self { cfg, instructions }
        }
    }

    impl<B: Copy + Eq + Hash, V: Copy + Eq + Hash> Procedure for TestProcedure<B, V> {
        type BlockId = B;
        type VarId = V;

        fn cfg(&self) -> impl DepthFirstPostorder<Node = Self::BlockId> + Successors {
            TestGraph::new(self.cfg.start(), &self.cfg.edges)
        }

        fn instructions(
            &self,
            b: Self::BlockId,
        ) -> impl DoubleEndedIterator<Item = Instruction<'_, Self::VarId>> + ExactSizeIterator {
            self.instructions.get(&b).copied().unwrap_or(&[]).iter().copied()
        }
    }

    macro_rules! instructions {
        ($($(def [$($d:literal),*])? $(use [$($u:literal),*])?);*) => {
            &[$(Instruction { defs: &[$($($d),*)?], uses: &[$($($u),*)?] }),*]
        };
    }

    #[test]
    fn test_live_in_single_block() {
        // A: use x
        let proc = TestProcedure::new("A", &[], &[
            ("A", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", Some(0))]));
    }

    #[test]
    fn test_live_in_linear() {
        // A: use x  →  B: use y
        let proc = TestProcedure::new("A", &[("A", "B")], &[
            ("A", instructions! { use ["x"] }),
            ("B", instructions! { use ["y"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", Some(0)), ("y", None)]));
        assert_eq!(result["B"], HashMap::from([("y", Some(0))]));
    }

    #[test]
    fn test_live_in_diamond() {
        //     A
        //    / \
        //   B   C
        //    \ /
        //     D: use x
        let proc = TestProcedure::new("A", &[
            ("A", "B"), ("A", "C"),
            ("B", "D"), ("C", "D"),
        ], &[
            ("D", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", None)]));
        assert_eq!(result["B"], HashMap::from([("x", None)]));
        assert_eq!(result["C"], HashMap::from([("x", None)]));
        assert_eq!(result["D"], HashMap::from([("x", Some(0))]));
    }

    #[test]
    fn test_live_in_def_kills() {
        // A: def x  →  B: use x
        let proc = TestProcedure::new("A", &[("A", "B")], &[
            ("A", instructions! { def ["x"] }),
            ("B", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", None)]));
        assert_eq!(result["B"], HashMap::from([("x", Some(0))]));
    }

    #[test]
    fn test_live_in_def_before_use() {
        // A: def x; use x
        let proc = TestProcedure::new("A", &[], &[
            ("A", instructions! { def ["x"] use []; use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", Some(1))]));
    }

    #[test]
    fn test_live_in_use_not_propagated_past_successor() {
        // A: def x  →  B: use x  →  C
        let proc = TestProcedure::new("A", &[("A", "B"), ("B", "C")], &[
            ("A", instructions! { def ["x"] }),
            ("B", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", None)]));
        assert_eq!(result["B"], HashMap::from([("x", Some(0))]));
        assert_eq!(result["C"], HashMap::from([]));
    }
}
