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

pub trait DepthFirstPostorder: Graph + StartNode {
    fn node(&self, index: usize) -> Self::Node;
    fn predecessors_indices(&self, number: usize) -> impl Iterator<Item = usize>
    where Self: Predecessors;
}

pub fn idom<G>(g: &G) -> HashMap<G::Node, G::Node>
where
    G: DepthFirstPostorder + Predecessors,
{
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

    impl<T: Copy + Eq + Hash> DepthFirstPostorder for TestGraph<T> {
        fn node(&self, index: usize) -> T {
            self.postorder[index]
        }

        fn predecessors_indices(&self, index: usize) -> impl Iterator<Item = usize> {
            let node = self.node(index);
            self.predecessors(node).map(|u| self.index(u))
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
}
