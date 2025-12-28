use std::{collections::HashMap, hash::Hash};

use crate::{graph::{EntryNode, ExitNode, Graph, Numbered, Postorder, Predecessors, Successors, Transpose, idom, postorder, transpose, cache_predecessors}};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefUse {
    Def,
    Use,
}

pub trait Procedure {
    type BlockId: Copy + Eq;
    type VarId: Copy + Eq + Hash;
    type InstrIdx: Copy;

    fn cfg(&self) -> impl Cfg<Node = Self::BlockId>;
    fn instructions(&self, b: Self::BlockId) -> impl DoubleEndedIterator<Item = (Self::InstrIdx, Self::VarId, DefUse)>;
}

pub trait Cfg: Graph + EntryNode + ExitNode + Successors + Postorder + Numbered {}
impl<T: Graph + EntryNode + ExitNode + Successors + Postorder + Numbered> Cfg for T {}

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
pub fn liveness<P: Procedure>(proc: &P) -> Liveness<P> {
    let cfg = proc.cfg();
    let n = cfg.node_count();

    let mut liveness: Box<[BlockLiveness<P>]> = vec![BlockLiveness { map: HashMap::new(), in_size: 0 }; n].into_boxed_slice();

    for (bpo, block) in cfg.postorder_iter().enumerate() {
        let mut live: BlockLiveness<P> = BlockLiveness { map: HashMap::new(), in_size: 0 };

        for a in cfg.successors(block) {
            let apo = cfg.postorder(a);
            assert!(apo < bpo, "cycle detected");
            for (&x, info) in &liveness[cfg.number(a)].map {
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
        liveness[cfg.number(block)] = live;
    }

    liveness
}

struct ReverseCfg<G: Graph> {
    inner: Transpose<G>,
    postorder: Box<[G::Node]>,
    postorder_index: Box<[usize]>,
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

impl<G: Numbered> Postorder for ReverseCfg<G> {
    fn postorder(&self, node: Self::Node) -> usize {
        self.postorder_index[self.number(node)]
    }

    fn at_postorder(&self, index: usize) -> Self::Node {
        self.postorder[index]
    }
}

impl<G: Numbered> Numbered for ReverseCfg<G> {
    fn number(&self, node: Self::Node) -> usize {
        self.inner.number(node)
    }

    fn numbered(&self, number: usize) -> Self::Node {
        self.inner.numbered(number)
    }
}

pub fn ipdom<G: ExitNode + Successors + Numbered>(cfg: G) -> Box<[G::Node]> {
    let rev_postorder = postorder(&transpose(cache_predecessors(&cfg)));

    let mut rev_postorder_index = vec![0; cfg.node_count()].into_boxed_slice();
    for (i, &v) in rev_postorder.iter().enumerate() {
        rev_postorder_index[cfg.number(v)] = i;
    }

    let rev_cfg = ReverseCfg {
        inner: transpose(cfg),
        postorder: rev_postorder,
        postorder_index: rev_postorder_index,
    };

    idom(&rev_cfg)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::graph::{Numbered, tests::TestGraph};

    struct TestProcedure<B, V: 'static> {
        cfg: TestGraph<B>,
        instructions: HashMap<B, &'static [&'static [(DefUse, V)]]>,
    }

    impl<B: Copy + Eq + Hash, V> TestProcedure<B, V> {
        fn new(
            start: B,
            edges: &[(B, B)],
            instructions: &[(B, &'static [&'static [(DefUse, V)]])],
        ) -> Self {
            let cfg = TestGraph::new(start, edges);
            let instructions = instructions.iter().copied().collect();
            Self { cfg, instructions }
        }
    }

    impl<B: Copy + Eq + Hash, V: Copy + Eq + Hash> Procedure for TestProcedure<B, V> {
        type BlockId = B;
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
        // A: def x; use x
        let proc = TestProcedure::new("A", &[], &[
            ("A", instructions! { def ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc);
        let a = &result[proc.cfg.number("A")];
        assert!(!a.live_in("x"));
        assert_eq!(a.last_use("x"), Some(1));
    }

    #[test]
    fn test_liveness_linear() {
        // A: def x; def y; use x  →  B: use y
        let proc = TestProcedure::new("A", &[("A", "B")], &[
            ("A", instructions! { def ["x"]; def ["y"]; use ["x"] }),
            ("B", instructions! { use ["y"] }),
        ]);
        let result = liveness(&proc);
        let a = &result[proc.cfg.number("A")];
        assert!(!a.live_in("x"));
        assert_eq!(a.last_use("x"), Some(2));
        assert!(!a.live_in("y"));
        assert!(a.live_out("y"));
        let b = &result[proc.cfg.number("B")];
        assert!(b.live_in("y"));
        assert_eq!(b.last_use("y"), Some(0));
    }

    #[test]
    fn test_liveness_diamond() {
        //     A: def x
        //    / \
        //   B   C
        //    \ /
        //     D: use x
        let proc = TestProcedure::new("A", &[
            ("A", "B"), ("A", "C"),
            ("B", "D"), ("C", "D"),
        ], &[
            ("A", instructions! { def ["x"] }),
            ("D", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert!(!result[proc.cfg.number("A")].live_in("x"));
        assert!(result[proc.cfg.number("A")].live_out("x"));
        assert!(result[proc.cfg.number("B")].live_in("x"));
        assert!(result[proc.cfg.number("B")].live_out("x"));
        assert!(result[proc.cfg.number("C")].live_in("x"));
        assert!(result[proc.cfg.number("C")].live_out("x"));
        assert!(result[proc.cfg.number("D")].live_in("x"));
        assert_eq!(result[proc.cfg.number("D")].last_use("x"), Some(0));
    }

    #[test]
    fn test_liveness_def_kills() {
        // A  →  B: def x  →  C: use x
        let proc = TestProcedure::new("A", &[("A", "B"), ("B", "C")], &[
            ("B", instructions! { def ["x"] }),
            ("C", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result[proc.cfg.number("A")].live_in_size(), 0);
        assert!(!result[proc.cfg.number("B")].live_in("x"));
        assert!(result[proc.cfg.number("B")].live_out("x"));
        assert!(result[proc.cfg.number("C")].live_in("x"));
        assert_eq!(result[proc.cfg.number("C")].last_use("x"), Some(0));
    }

    #[test]
    fn test_liveness_local() {
        // A: def x; use x
        let proc = TestProcedure::new("A", &[], &[
            ("A", instructions! { def ["x"] ; use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert!(!result[proc.cfg.number("A")].live_in("x"));
        assert_eq!(result[proc.cfg.number("A")].last_use("x"), Some(1));
    }

    #[test]
    fn test_liveness_last_use() {
        // A: def x  →  B: use x  →  C
        let proc = TestProcedure::new("A", &[("A", "B"), ("B", "C")], &[
            ("A", instructions! { def ["x"] }),
            ("B", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert!(!result[proc.cfg.number("A")].live_in("x"));
        assert!(result[proc.cfg.number("A")].live_out("x"));
        assert!(result[proc.cfg.number("B")].live_in("x"));
        assert_eq!(result[proc.cfg.number("B")].last_use("x"), Some(0));
        assert_eq!(result[proc.cfg.number("C")].live_in_size(), 0);
    }

    #[test]
    fn test_liveness_multiple_uses() {
        // A: def x; use x; use x
        let proc = TestProcedure::new("A", &[], &[
            ("A", instructions! { def ["x"]; use ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert!(!result[proc.cfg.number("A")].live_in("x"));
        assert_eq!(result[proc.cfg.number("A")].last_use("x"), Some(2));
    }
}
