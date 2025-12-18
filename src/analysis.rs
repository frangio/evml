use std::{collections::HashMap, hash::Hash};
use crate::graph::{Graph, DepthFirstPostorder, Successors};

pub trait Instruction {
    type VarId: Copy + Eq + Hash;
    fn index(&self) -> usize;
    fn defs(&self) -> impl Iterator<Item = Self::VarId>;
    fn uses(&self) -> impl Iterator<Item = Self::VarId>;
}

pub trait Procedure {
    type BlockId: Copy + Eq + Hash;
    type VarId: Copy + Eq + Hash;
    fn cfg(&self) -> impl DepthFirstPostorder<Node = Self::BlockId> + Successors;
    fn instructions(
        &self,
        b: Self::BlockId,
    ) -> impl DoubleEndedIterator<Item: Instruction<VarId = Self::VarId>>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VarLiveness {
    pub live_in: bool,
    pub last_use: Option<usize>,
}

pub type BlockLiveness<P> = HashMap<<P as Procedure>::VarId, VarLiveness>;
pub type Liveness<P> = HashMap<<P as Procedure>::BlockId, BlockLiveness<P>>;

/// Returns liveness info for each variable per block.
pub fn liveness<P: Procedure>(proc: &P) -> Liveness<P> {
    let cfg = proc.cfg();
    let n = cfg.node_count();

    let mut result: Liveness<P> = HashMap::with_capacity(n);

    for v in 0..n {
        let block = cfg.node(v);
        let mut live: BlockLiveness<P> = HashMap::new();

        for u in cfg.successors_indices(v) {
            if u < v {
                for (&x, info) in &result[&cfg.node(u)] {
                    if info.live_in {
                        live.insert(x, VarLiveness { live_in: true, last_use: None });
                    }
                }
            } else {
                unimplemented!("cycles");
            }
        }

        for instr in proc.instructions(block).rev() {
            let i = instr.index();
            for x in instr.uses() {
                live.entry(x).or_insert(VarLiveness { live_in: true, last_use: Some(i) });
            }
            for x in instr.defs() {
                live.entry(x)
                    .and_modify(|info| info.live_in = false)
                    .or_insert(VarLiveness { live_in: false, last_use: None });
            }
        }

        result.insert(block, live);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::graph::{StartNode, tests::TestGraph};

    struct TestInstruction<V: 'static> {
        defs: &'static [V],
        uses: &'static [V],
    }

    impl<V: Copy + Eq + Hash> Instruction for (usize, &TestInstruction<V>) {
        type VarId = V;
        fn index(&self) -> usize {
            self.0
        }
        fn defs(&self) -> impl Iterator<Item = Self::VarId> {
            self.1.defs.iter().copied()
        }
        fn uses(&self) -> impl Iterator<Item = Self::VarId> {
            self.1.uses.iter().copied()
        }
    }

    struct TestProcedure<B, V: 'static> {
        cfg: TestGraph<B>,
        instructions: HashMap<B, &'static [TestInstruction<V>]>,
    }

    impl<B: Copy + Eq + Hash, V> TestProcedure<B, V> {
        fn new(
            start: B,
            edges: &[(B, B)],
            instructions: &[(B, &'static [TestInstruction<V>])],
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
            &self.cfg
        }

        fn instructions(
            &self,
            b: Self::BlockId,
        ) -> impl DoubleEndedIterator<Item: Instruction<VarId = Self::VarId>> {
            self.instructions.get(&b).copied().unwrap_or(&[]).iter().enumerate()
        }
    }

    macro_rules! instructions {
        ($($(def [$($d:literal),*])? $(use [$($u:literal),*])?);*) => {
            &[$(TestInstruction { defs: &[$($($d),*)?], uses: &[$($($u),*)?] }),*]
        };
    }

    const fn live_in(last_use: Option<usize>) -> VarLiveness {
        VarLiveness { live_in: true, last_use }
    }

    const fn local(last_use: Option<usize>) -> VarLiveness {
        VarLiveness { live_in: false, last_use }
    }

    #[test]
    fn test_liveness_single_block() {
        // A: def x; use x
        let proc = TestProcedure::new("A", &[], &[
            ("A", instructions! { def ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", local(Some(1)))]));
    }

    #[test]
    fn test_liveness_linear() {
        // A: def x; def y; use x  →  B: use y
        let proc = TestProcedure::new("A", &[("A", "B")], &[
            ("A", instructions! { def ["x"]; def ["y"]; use ["x"] }),
            ("B", instructions! { use ["y"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", local(Some(2))), ("y", local(None))]));
        assert_eq!(result["B"], HashMap::from([("y", live_in(Some(0)))]));
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
        assert_eq!(result["A"], HashMap::from([("x", local(None))]));
        assert_eq!(result["B"], HashMap::from([("x", live_in(None))]));
        assert_eq!(result["C"], HashMap::from([("x", live_in(None))]));
        assert_eq!(result["D"], HashMap::from([("x", live_in(Some(0)))]));
    }

    #[test]
    fn test_liveness_def_kills() {
        // A  →  B: def x  →  C: use x
        let proc = TestProcedure::new("A", &[("A", "B"), ("B", "C")], &[
            ("B", instructions! { def ["x"] }),
            ("C", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([]));
        assert_eq!(result["B"], HashMap::from([("x", local(None))]));
        assert_eq!(result["C"], HashMap::from([("x", live_in(Some(0)))]));
    }

    #[test]
    fn test_liveness_local() {
        // A: def x; use x
        let proc = TestProcedure::new("A", &[], &[
            ("A", instructions! { def ["x"] ; use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", local(Some(1)))]));
    }

    #[test]
    fn test_liveness_last_use() {
        // A: def x  →  B: use x  →  C
        let proc = TestProcedure::new("A", &[("A", "B"), ("B", "C")], &[
            ("A", instructions! { def ["x"] }),
            ("B", instructions! { use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", local(None))]));
        assert_eq!(result["B"], HashMap::from([("x", live_in(Some(0)))]));
        assert_eq!(result["C"], HashMap::from([]));
    }

    #[test]
    fn test_liveness_multiple_uses() {
        // A: def x; use x; use x
        let proc = TestProcedure::new("A", &[], &[
            ("A", instructions! { def ["x"]; use ["x"]; use ["x"] }),
        ]);
        let result = liveness(&proc);
        assert_eq!(result["A"], HashMap::from([("x", local(Some(2)))]));
    }
}
