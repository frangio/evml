use std::{collections::HashMap, hash::Hash};

use crate::graph::{ArrayNodeOrdering, EntryNode, ExitNode, Graph, Idx, NodeOrdering, Predecessors, Successors, Transpose, cache_predecessors, idom, postorder, transpose};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefUse {
    Def,
    Use,
}

pub trait Procedure {
    type BlockId: Copy + Eq + Idx;
    type VarId: Copy + Eq + Hash;
    type InstrIdx: Copy;

    fn cfg(&self) -> impl Cfg<Node = Self::BlockId>;
    fn instructions(&self, b: Self::BlockId) -> impl DoubleEndedIterator<Item = (Self::InstrIdx, Self::VarId, DefUse)>;
}

pub trait Cfg: Graph + EntryNode + ExitNode + Successors {}
impl<T: Graph + EntryNode + ExitNode + Successors> Cfg for T {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct VarLiveness<Idx> {
    live_in: bool,
    last_use: Option<Idx>,
}

pub type Liveness<P> = Box<[BlockLiveness<P>]>;

pub struct BlockLiveness<P: Procedure> {
    map: HashMap<P::VarId, VarLiveness<P::InstrIdx>>,
    in_size: usize,
}

impl<P: Procedure> Clone for BlockLiveness<P> {
    fn clone(&self) -> Self {
        Self { map: self.map.clone(), in_size: self.in_size }
    }
}

impl<P: Procedure> BlockLiveness<P> {
    pub fn live_in(&self, var: P::VarId) -> bool {
        self.map.get(&var).is_some_and(|l| l.live_in)
    }

    pub fn live_out(&self, var: P::VarId) -> bool {
        self.map[&var].last_use.is_none()
    }

    pub fn last_use(&self, var: P::VarId) -> Option<P::InstrIdx> {
        self.map[&var].last_use
    }

    pub fn live_in_size(&self) -> usize {
        self.in_size
    }

}

/// Returns liveness info for each variable per block.
pub fn liveness<P: Procedure>(proc: &P, postorder: &impl NodeOrdering<P::BlockId>) -> Liveness<P> {
    let cfg = proc.cfg();
    let n = cfg.node_count();

    let mut liveness: Box<[BlockLiveness<P>]> = vec![BlockLiveness { map: HashMap::new(), in_size: 0 }; n].into_boxed_slice();

    for (bpo, block) in postorder.iter().enumerate() {
        let mut live: BlockLiveness<P> = BlockLiveness { map: HashMap::new(), in_size: 0 };

        for a in cfg.successors(block) {
            let apo = postorder.position(a);
            assert!(apo < bpo, "cycle detected");
            for (&x, info) in &liveness[a.index()].map {
                if info.live_in {
                    live.map.entry(x).or_insert_with(|| {
                        live.in_size += 1;
                        VarLiveness { live_in: true, last_use: None }
                    });
                }
            }
        }

        for (i, x, def_use) in proc.instructions(block).rev() {
            match def_use {
                DefUse::Use => {
                    live.map.entry(x).or_insert_with(|| {
                        live.in_size += 1;
                        VarLiveness { live_in: true, last_use: Some(i) }
                    });
                }

                DefUse::Def => {
                    live.map.entry(x)
                        .and_modify(|info| {
                            if info.live_in {
                                live.in_size -= 1;
                            }
                            info.live_in = false;
                        })
                        .or_insert(VarLiveness { live_in: false, last_use: None });
                }
            }
        }
        liveness[block.index()] = live;
    }

    liveness
}

struct ReverseCfg<G: Graph> {
    inner: Transpose<G>,
    postorder: ArrayNodeOrdering<G::Node>,
}

impl<G: Graph> Graph for ReverseCfg<G> {
    type Node = G::Node;

    fn node_count(&self) -> usize {
        self.inner.node_count()
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        self.inner.nodes()
    }
}

impl<G: ExitNode> EntryNode for ReverseCfg<G> {
    fn entry(&self) -> Self::Node {
        self.inner.entry()
    }
}

impl<G: Successors> Predecessors for ReverseCfg<G> {
    fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.inner.predecessors(node)
    }
}

pub fn ipdom<G: ExitNode + Successors>(cfg: &G) -> Box<[G::Node]> {
    let rev_cfg = transpose(cache_predecessors(cfg));
    let rev_postorder = postorder(&rev_cfg);
    idom(&transpose(cfg), &rev_postorder)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::graph::tests::TestGraph;

    struct TestProcedure<V: 'static> {
        cfg: TestGraph,
        instructions: HashMap<usize, &'static [&'static [(DefUse, V)]]>,
    }

    impl<V> TestProcedure<V> {
        fn new(
            start: usize,
            edges: &[(usize, usize)],
            instructions: &[(usize, &'static [&'static [(DefUse, V)]])],
        ) -> Self {
            let cfg = TestGraph::new(start, edges);
            let instructions = instructions.iter().copied().collect();
            Self { cfg, instructions }
        }
    }

    impl<V: Copy + Eq + Hash> Procedure for TestProcedure<V> {
        type BlockId = usize;
        type VarId = V;
        type InstrIdx = usize;

        fn cfg(&self) -> impl Cfg<Node = Self::BlockId> {
            &self.cfg
        }

        fn instructions(&self, b: Self::BlockId) -> impl DoubleEndedIterator<Item = (Self::InstrIdx, Self::VarId, DefUse)> {
            self.instructions.get(&b).copied().unwrap_or(&[]).iter().enumerate()
                .flat_map(|(i, instr)| instr.iter().map(move |&(du, v)| (i, v, du)))
        }
    }

    macro_rules! instructions {
        ($($(def [$($d:literal),*])? $(use [$($u:literal),*])?);*) => {{
            &[$(&[$($((DefUse::Def, $d)),*)? $($((DefUse::Use, $u)),*)?]),*]
        }};
    }

    #[test]
    fn test_liveness_single_block() {
        // 0: def x; use x
        let proc = TestProcedure::new(0, &[], &[
            (0, instructions! { def ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc, &proc.cfg.postorder);
        let a = &result[0];
        assert!(!a.live_in("x"));
        assert_eq!(a.last_use("x"), Some(1));
    }

    #[test]
    fn test_liveness_linear() {
        // 0: def x; def y; use x  →  1: use y
        let proc = TestProcedure::new(0, &[(0, 1)], &[
            (0, instructions! { def ["x"]; def ["y"]; use ["x"] }),
            (1, instructions! { use ["y"] }),
        ]);
        let result = liveness(&proc, &proc.cfg.postorder);
        let a = &result[0];
        assert!(!a.live_in("x"));
        assert_eq!(a.last_use("x"), Some(2));
        assert!(!a.live_in("y"));
        assert!(a.live_out("y"));
        let b = &result[1];
        assert!(b.live_in("y"));
        assert_eq!(b.last_use("y"), Some(0));
    }

    #[test]
    fn test_liveness_diamond() {
        //     0: def x
        //    / \
        //   1   2
        //    \ /
        //     3: use x
        let proc = TestProcedure::new(0, &[
            (0, 1), (0, 2),
            (1, 3), (2, 3),
        ], &[
            (0, instructions! { def ["x"] }),
            (3, instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc, &proc.cfg.postorder);
        assert!(!result[0].live_in("x"));
        assert!(result[0].live_out("x"));
        assert!(result[1].live_in("x"));
        assert!(result[1].live_out("x"));
        assert!(result[2].live_in("x"));
        assert!(result[2].live_out("x"));
        assert!(result[3].live_in("x"));
        assert_eq!(result[3].last_use("x"), Some(0));
    }

    #[test]
    fn test_liveness_def_kills() {
        // 0  →  1: def x  →  2: use x
        let proc = TestProcedure::new(0, &[(0, 1), (1, 2)], &[
            (1, instructions! { def ["x"] }),
            (2, instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc, &proc.cfg.postorder);
        assert_eq!(result[0].live_in_size(), 0);
        assert!(!result[1].live_in("x"));
        assert!(result[1].live_out("x"));
        assert!(result[2].live_in("x"));
        assert_eq!(result[2].last_use("x"), Some(0));
    }

    #[test]
    fn test_liveness_local() {
        // 0: def x; use x
        let proc = TestProcedure::new(0, &[], &[
            (0, instructions! { def ["x"] ; use ["x"] }),
        ]);
        let result = liveness(&proc, &proc.cfg.postorder);
        assert!(!result[0].live_in("x"));
        assert_eq!(result[0].last_use("x"), Some(1));
    }

    #[test]
    fn test_liveness_last_use() {
        // 0: def x  →  1: use x  →  2
        let proc = TestProcedure::new(0, &[(0, 1), (1, 2)], &[
            (0, instructions! { def ["x"] }),
            (1, instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc, &proc.cfg.postorder);
        assert!(!result[0].live_in("x"));
        assert!(result[0].live_out("x"));
        assert!(result[1].live_in("x"));
        assert_eq!(result[1].last_use("x"), Some(0));
        assert_eq!(result[2].live_in_size(), 0);
    }

    #[test]
    fn test_liveness_multiple_uses() {
        // 0: def x; use x; use x
        let proc = TestProcedure::new(0, &[], &[
            (0, instructions! { def ["x"]; use ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc, &proc.cfg.postorder);
        assert!(!result[0].live_in("x"));
        assert_eq!(result[0].last_use("x"), Some(2));
    }
}
