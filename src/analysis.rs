use std::{cmp::Ordering, collections::HashMap, hash::Hash};
use crate::graph::{EntryNode, ExitNode, Graph, Idx, NodeOrdering, Successors, cache_predecessors, idom, postorder, transpose};

pub trait Procedure {
    type BlockId: Copy + Eq + Idx;
    type VarId: Copy + Eq + Hash;
    type InstrIdx: Copy + Eq;

    fn cfg(&self) -> impl Cfg<Node = Self::BlockId>;
    fn instructions(&self, b: Self::BlockId) -> impl DoubleEndedIterator<Item = (Self::InstrIdx, Self::VarId, DefUse)>;
}

pub trait Cfg: Graph + EntryNode + ExitNode + Successors {}
impl<T: Graph + EntryNode + ExitNode + Successors> Cfg for T {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefUse {
    Def,
    Use,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct VarLiveness<Idx> {
    live_in: bool,
    last_use: VarUse<Idx>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VarUse<Idx> {
    Unused,
    Instr(Idx),
    LiveOut,
}

impl<Idx: PartialEq> PartialEq<Idx> for VarUse<Idx> {
    fn eq(&self, other: &Idx) -> bool {
        match self {
            VarUse::Unused => false,
            VarUse::Instr(a) => a == other,
            VarUse::LiveOut => false,
        }
    }
}

impl<Idx: PartialOrd> PartialOrd<Idx> for VarUse<Idx> {
    fn partial_cmp(&self, other: &Idx) -> Option<Ordering> {
        match self {
            VarUse::Unused => Some(Ordering::Less),
            VarUse::Instr(a) => a.partial_cmp(other),
            VarUse::LiveOut => Some(Ordering::Greater),
        }
    }
}

pub struct BlockLiveness<P: Procedure> {
    map: HashMap<P::VarId, VarLiveness<P::InstrIdx>>,
}

impl<P: Procedure> Clone for BlockLiveness<P> {
    fn clone(&self) -> Self {
        Self { map: self.map.clone() }
    }
}

impl<P: Procedure> BlockLiveness<P> {
    pub fn live_in(&self, var: P::VarId) -> bool {
        self.map.get(&var).is_some_and(|l| l.live_in)
    }

    pub fn live_out(&self, var: P::VarId) -> bool {
        self.last_use(var) == VarUse::LiveOut
    }

    pub fn live_in_vars(&self) -> impl Iterator<Item = P::VarId> + '_ {
        self.map.iter().filter_map(|(&var, info)| info.live_in.then_some(var))
    }

    pub fn last_use(&self, var: P::VarId) -> VarUse<P::InstrIdx> {
        self.map.get(&var).map_or(VarUse::Unused, |l| l.last_use)
    }
}

/// Returns liveness info for each variable per block.
pub fn liveness<P: Procedure>(proc: &P, postorder: &impl NodeOrdering<P::BlockId>) -> Box<[BlockLiveness<P>]> {
    let cfg = proc.cfg();
    let n = cfg.node_count();

    let mut liveness: Box<[BlockLiveness<P>]> = vec![BlockLiveness { map: HashMap::new() }; n].into_boxed_slice();

    for (bpo, block) in postorder.iter().enumerate() {
        let mut live: BlockLiveness<P> = BlockLiveness { map: HashMap::new() };

        for a in cfg.successors(block) {
            let apo = postorder.position(a);
            assert!(apo < bpo, "cycle detected");
            for (&x, info) in &liveness[a.index()].map {
                if info.live_in {
                    live.map.entry(x).or_insert(VarLiveness { live_in: true, last_use: VarUse::LiveOut });
                }
            }
        }

        for (i, x, def_use) in proc.instructions(block).rev() {
            match def_use {
                DefUse::Use => {
                    live.map.entry(x).or_insert(VarLiveness { live_in: true, last_use: VarUse::Instr(i) });
                }

                DefUse::Def => {
                    live.map.entry(x)
                        .and_modify(|info| info.live_in = false)
                        .or_insert(VarLiveness { live_in: false, last_use: VarUse::Instr(i) });
                }
            }
        }
        liveness[block.index()] = live;
    }

    liveness
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
            edges: &[(usize, usize)],
            instructions: &[(usize, &'static [&'static [(DefUse, V)]])],
        ) -> Self {
            let node_count = edges.iter().flat_map(|&(v, w)| [v, w]).max().map_or(0, |c| c + 1);
            Self::with_nodes(node_count, edges, instructions)
        }

        fn with_nodes(
            node_count: usize,
            edges: &[(usize, usize)],
            instructions: &[(usize, &'static [&'static [(DefUse, V)]])],
        ) -> Self {
            let cfg = TestGraph::with_nodes(node_count, edges);
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
        let proc = TestProcedure::with_nodes(1, &[], &[
            (0, instructions! { def ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        let a = &result[0];
        assert!(!a.live_in("x"));
        assert_eq!(a.last_use("x"), VarUse::Instr(1));
    }

    #[test]
    fn test_liveness_linear() {
        // 0: def x; def y; use x  →  1: use y
        let proc = TestProcedure::new(&[(0, 1)], &[
            (0, instructions! { def ["x"]; def ["y"]; use ["x"] }),
            (1, instructions! { use ["y"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        let a = &result[0];
        assert!(!a.live_in("x"));
        assert_eq!(a.last_use("x"), VarUse::Instr(2));
        assert!(!a.live_in("y"));
        assert_eq!(a.last_use("y"), VarUse::LiveOut);
        let b = &result[1];
        assert!(b.live_in("y"));
        assert_eq!(b.last_use("y"), VarUse::Instr(0));
    }

    #[test]
    fn test_liveness_diamond() {
        //     0: def x
        //    / \
        //   1   2
        //    \ /
        //     3: use x
        let proc = TestProcedure::new(&[
            (0, 1), (0, 2),
            (1, 3), (2, 3),
        ], &[
            (0, instructions! { def ["x"] }),
            (3, instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert_eq!(result[0].last_use("x"), VarUse::LiveOut);
        assert!(result[1].live_in("x"));
        assert_eq!(result[1].last_use("x"), VarUse::LiveOut);
        assert!(result[2].live_in("x"));
        assert_eq!(result[2].last_use("x"), VarUse::LiveOut);
        assert!(result[3].live_in("x"));
        assert_eq!(result[3].last_use("x"), VarUse::Instr(0));
    }

    #[test]
    fn test_liveness_def_kills() {
        // 0  →  1: def x  →  2: use x
        let proc = TestProcedure::new(&[(0, 1), (1, 2)], &[
            (1, instructions! { def ["x"] }),
            (2, instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[1].live_in("x"));
        assert_eq!(result[1].last_use("x"), VarUse::LiveOut);
        assert!(result[2].live_in("x"));
        assert_eq!(result[2].last_use("x"), VarUse::Instr(0));
    }

    #[test]
    fn test_liveness_local() {
        // 0: def x; use x
        let proc = TestProcedure::with_nodes(1, &[], &[
            (0, instructions! { def ["x"] ; use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert_eq!(result[0].last_use("x"), VarUse::Instr(1));
    }

    #[test]
    fn test_liveness_last_use() {
        // 0: def x  →  1: use x  →  2
        let proc = TestProcedure::new(&[(0, 1), (1, 2)], &[
            (0, instructions! { def ["x"] }),
            (1, instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert_eq!(result[0].last_use("x"), VarUse::LiveOut);
        assert!(result[1].live_in("x"));
        assert_eq!(result[1].last_use("x"), VarUse::Instr(0));
    }

    #[test]
    fn test_liveness_multiple_uses() {
        // 0: def x; use x; use x
        let proc = TestProcedure::with_nodes(1, &[], &[
            (0, instructions! { def ["x"]; use ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert_eq!(result[0].last_use("x"), VarUse::Instr(2));
    }
}
