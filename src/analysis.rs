use std::{collections::{HashMap, hash_map::Entry}, hash::Hash};
use crate::graph::{EntryNode, ExitNode, Graph, Idx, NodeOrdering, Successors};

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
struct VarLiveness {
    live_in: bool,
    live_out: bool,
    used: bool,
}

#[derive(Clone)]
pub struct BlockLiveness<V> {
    vars: HashMap<V, VarLiveness>,
    used_count: usize,
}

impl<V: Copy + Eq + Hash> BlockLiveness<V> {
    pub fn live_in(&self, var: V) -> bool {
        self.vars.get(&var).is_some_and(|l| l.live_in)
    }

    pub fn live_out(&self, var: V) -> bool {
        self.vars.get(&var).is_some_and(|l| l.live_out)
    }

    pub fn live_in_vars(&self) -> impl Iterator<Item = V> + '_ {
        self.vars.iter().filter_map(|(&var, info)| info.live_in.then_some(var))
    }

    pub fn used_count(&self) -> usize {
        self.used_count
    }
}

/// Returns liveness info for each variable per block.
pub fn liveness<P: Procedure>(proc: &P, postorder: &impl NodeOrdering<P::BlockId>) -> Box<[BlockLiveness<P::VarId>]> {
    let cfg = proc.cfg();
    let n = cfg.node_count();

    let mut liveness: Box<[BlockLiveness<P::VarId>]> = vec![BlockLiveness { vars: HashMap::new(), used_count: 0 }; n].into_boxed_slice();

    for (bpo, block) in postorder.iter().enumerate() {
        let mut live: BlockLiveness<P::VarId> = BlockLiveness { vars: HashMap::new(), used_count: 0 };

        for a in cfg.successors(block) {
            let apo = postorder.position(a);
            assert!(apo < bpo, "cycle detected");
            for (&x, info) in &liveness[a.index()].vars {
                if info.live_in {
                    live.vars.entry(x).or_insert(VarLiveness {
                        live_in: true,
                        live_out: true,
                        used: false,
                    });
                }
            }
        }

        for (_, x, def_use) in proc.instructions(block).rev() {
            match live.vars.entry(x) {
                Entry::Occupied(mut entry) => {
                    let info = entry.get_mut();
                    if !info.used {
                        info.used = true;
                        live.used_count += 1;
                    }
                    if def_use == DefUse::Def {
                        info.live_in = false;
                    }
                }

                Entry::Vacant(entry) => {
                    live.used_count += 1;
                    entry.insert(VarLiveness {
                        live_in: def_use == DefUse::Use,
                        live_out: false,
                        used: true,
                    });
                }
            }
        }

        liveness[block.index()] = live;
    }

    liveness
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
        assert!(!a.live_out("x"));
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
        assert!(!a.live_out("x"));
        assert!(!a.live_in("y"));
        assert!(a.live_out("y"));
        let b = &result[1];
        assert!(b.live_in("y"));
        assert!(!b.live_out("y"));
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
        assert!(result[0].live_out("x"));
        assert!(result[1].live_in("x"));
        assert!(result[1].live_out("x"));
        assert!(result[2].live_in("x"));
        assert!(result[2].live_out("x"));
        assert!(result[3].live_in("x"));
        assert!(!result[3].live_out("x"));
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
        assert!(result[1].live_out("x"));
        assert!(result[2].live_in("x"));
        assert!(!result[2].live_out("x"));
    }

    #[test]
    fn test_liveness_local() {
        // 0: def x; use x
        let proc = TestProcedure::with_nodes(1, &[], &[
            (0, instructions! { def ["x"] ; use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert!(!result[0].live_out("x"));
    }

    #[test]
    fn test_liveness_live_out() {
        // 0: def x  →  1: use x  →  2
        let proc = TestProcedure::new(&[(0, 1), (1, 2)], &[
            (0, instructions! { def ["x"] }),
            (1, instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert!(result[0].live_out("x"));
        assert!(result[1].live_in("x"));
        assert!(!result[1].live_out("x"));
    }

    #[test]
    fn test_liveness_multiple_uses() {
        // 0: def x; use x; use x
        let proc = TestProcedure::with_nodes(1, &[], &[
            (0, instructions! { def ["x"]; use ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert!(!result[0].live_out("x"));
    }
}
