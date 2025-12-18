use std::{collections::HashMap, hash::Hash};
use crate::graph::{Graph, DepthFirstPostorder, Successors};

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

    use crate::graph::{StartNode, tests::TestGraph};

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
            &self.cfg
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

