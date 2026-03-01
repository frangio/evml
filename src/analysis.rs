use std::{collections::{HashMap, HashSet, hash_map::Entry}, hash::Hash};
use crate::graph::{EntryNode, Graph, Idx, NodeOrdering, Predecessors, Successors, Tree, dfs_intervals};
use crate::utils::BitSet;

pub trait Procedure {
    type BlockId: Copy + Eq + Idx;
    type VarId: Copy + Eq + Hash;
    type InstrIdx: Copy + Eq;

    fn cfg(&self) -> impl Cfg<Node = Self::BlockId>;
    fn instructions(&self, b: Self::BlockId) -> impl DoubleEndedIterator<Item = (Self::InstrIdx, Self::VarId, DefUse)>;
}

pub trait Cfg: Graph + EntryNode + Successors + Predecessors {}
impl<T: Graph + EntryNode + Successors + Predecessors> Cfg for T {}

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

    pub fn live_out_vars(&self) -> impl Iterator<Item = V> + '_ {
        self.vars.iter().filter_map(|(&var, info)| info.live_out.then_some(var))
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
            if apo >= bpo { todo!("liveness in cyclic cfg") }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PinState {
    PinOut,
    PinThrough,
}

#[derive(Clone, Debug, Default)]
pub struct Pinning<V> {
    pinned: HashMap<V, PinState>,
}

impl<V: Copy + Eq + Hash> Pinning<V> {
    pub fn is_pinned_out(&self, var: V) -> bool {
        self.pinned.contains_key(&var)
    }

    pub fn is_pinned(&self, var: V) -> bool {
        self.pinned.get(&var) == Some(&PinState::PinThrough)
    }
}

/// Returns, for each block, pinned live-out variables.
///
/// - key presence means pinned at block exit
/// - `PinState::PinOut` means not pinned at block entry
/// - `PinState::PinThrough` means pinned at block entry and exit
pub fn pinning<P: Procedure>(
    proc: &P,
    postorder: &impl NodeOrdering<P::BlockId>,
    dom_tree: &Tree<P::BlockId>,
    liveness: &[BlockLiveness<P::VarId>],
) -> Box<[Pinning<P::VarId>]>
where
    P::BlockId: Hash,
{
    let cfg = proc.cfg();
    let n = cfg.node_count();

    let dom_intervals = dfs_intervals(dom_tree);
    let dominates = |a: P::BlockId, b: P::BlockId| {
        let ra = &dom_intervals[a.index()];
        let rb = &dom_intervals[b.index()];
        ra.start <= rb.start && rb.end <= ra.end
    };

    let mut pins: Box<[HashSet<P::BlockId>]> = vec![HashSet::new(); n].into_boxed_slice();

    for b in postorder.iter() {
        for t in cfg.successors(b) {
            if b == t || !dominates(b, t) {
                pins[b.index()].insert(t);
            }
        }
    }

    let mut worklist: Vec<P::BlockId> = postorder.iter().collect();
    let mut not_queued = BitSet::new(n);

    while let Some(b) = worklist.pop() {
        not_queued.insert(b.index());
        let mut changed = false;

        for s in cfg.successors(b) {
            if s == b {
                continue;
            }
            let [pins_s, pins_b] = pins.get_disjoint_mut([s.index(), b.index()]).unwrap();
            for &t in pins_s.iter() {
                if dom_tree.parent(t) != Some(s) {
                    changed |= pins_b.insert(t);
                }
            }
        }

        if changed {
            for p in cfg.predecessors(b) {
                if not_queued.remove(p.index()) {
                    worklist.push(p);
                }
            }
        }
    }

    let mut pinned: Box<[Pinning<P::VarId>]> = vec![Pinning { pinned: HashMap::new() }; n].into_boxed_slice();

    for b in cfg.nodes() {
        for t in pins[b.index()].iter().copied() {
            let pin_state = if dom_tree.parent(t) == Some(b) {
                PinState::PinOut
            } else {
                PinState::PinThrough
            };

            for x in liveness[t.index()].live_in_vars() {
                pinned[b.index()].pinned
                    .entry(x)
                    .and_modify(|state| {
                        if pin_state == PinState::PinThrough {
                            *state = PinState::PinThrough;
                        }
                    })
                    .or_insert(pin_state);
            }
        }
    }

    pinned
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::graph::{Tree, idom, tests::TestGraph};

    struct TestProcedure<V: 'static> {
        cfg: TestGraph,
        instructions: HashMap<usize, &'static [&'static [(DefUse, V)]]>,
    }

    impl<V> TestProcedure<V> {
        fn new(
            edges: &[(usize, usize)],
            instructions: &[(usize, &'static [&'static [(DefUse, V)]])],
        ) -> Self {
            let node_count = edges
                .iter()
                .flat_map(|&(v, w)| [v, w])
                .max()
                .map_or(0, |c| c + 1);
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

        fn instructions(
            &self,
            b: Self::BlockId,
        ) -> impl DoubleEndedIterator<Item = (Self::InstrIdx, Self::VarId, DefUse)> {
            self.instructions
                .get(&b)
                .copied()
                .unwrap_or(&[])
                .iter()
                .enumerate()
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
        let proc =
            TestProcedure::with_nodes(1, &[], &[(0, instructions! { def ["x"]; use ["x"] })]);
        let result = liveness(&proc, proc.cfg.postorder());
        let a = &result[0];
        assert!(!a.live_in("x"));
        assert!(!a.live_out("x"));
    }

    #[test]
    fn test_liveness_linear() {
        // 0: def x; def y; use x  →  1: use y
        let proc = TestProcedure::new(
            &[(0, 1)],
            &[
                (0, instructions! { def ["x"]; def ["y"]; use ["x"] }),
                (1, instructions! { use ["y"] }),
            ],
        );
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
        let proc = TestProcedure::new(
            &[(0, 1), (0, 2), (1, 3), (2, 3)],
            &[
                (0, instructions! { def ["x"] }),
                (3, instructions! { use ["x"] }),
            ],
        );
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
        let proc = TestProcedure::new(
            &[(0, 1), (1, 2)],
            &[
                (1, instructions! { def ["x"] }),
                (2, instructions! { use ["x"] }),
            ],
        );
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[1].live_in("x"));
        assert!(result[1].live_out("x"));
        assert!(result[2].live_in("x"));
        assert!(!result[2].live_out("x"));
    }

    #[test]
    fn test_liveness_local() {
        // 0: def x; use x
        let proc =
            TestProcedure::with_nodes(1, &[], &[(0, instructions! { def ["x"] ; use ["x"] })]);
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert!(!result[0].live_out("x"));
    }

    #[test]
    fn test_liveness_live_out() {
        // 0: def x  →  1: use x  →  2
        let proc = TestProcedure::new(
            &[(0, 1), (1, 2)],
            &[
                (0, instructions! { def ["x"] }),
                (1, instructions! { use ["x"] }),
            ],
        );
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert!(result[0].live_out("x"));
        assert!(result[1].live_in("x"));
        assert!(!result[1].live_out("x"));
    }

    #[test]
    fn test_liveness_multiple_uses() {
        // 0: def x; use x; use x
        let proc = TestProcedure::with_nodes(
            1,
            &[],
            &[(0, instructions! { def ["x"]; use ["x"]; use ["x"] })],
        );
        let result = liveness(&proc, proc.cfg.postorder());
        assert!(!result[0].live_in("x"));
        assert!(!result[0].live_out("x"));
    }

    #[test]
    fn test_pinning_linear() {
        // 0: def x  →  1  →  2: use x
        let proc = TestProcedure::new(
            &[(0, 1), (1, 2)],
            &[
                (0, instructions! { def ["x"] }),
                (2, instructions! { use ["x"] }),
            ],
        );
        let postorder = proc.cfg.postorder();
        let live = liveness(&proc, postorder);
        let dom_tree = Tree::new(proc.cfg.entry(), idom(&proc.cfg, postorder));
        let result = pinning(&proc, postorder, &dom_tree, &live);

        assert!(!result[0].is_pinned_out("x"));
        assert!(!result[0].is_pinned("x"));
        assert!(!result[1].is_pinned_out("x"));
        assert!(!result[1].is_pinned("x"));
        assert!(!result[2].is_pinned_out("x"));
        assert!(!result[2].is_pinned("x"));
    }

    #[test]
    fn test_pinning_barrier() {
        // 4: def x -> 0 -> 1 -> 3: use x
        //               \-> 2 -/
        let proc = TestProcedure::with_nodes(
            5,
            &[(4, 0), (0, 1), (0, 2), (1, 3), (2, 3)],
            &[
                (4, instructions! { def ["x"] }),
                (3, instructions! { use ["x"] }),
            ],
        );
        let postorder = proc.cfg.postorder();
        let live = liveness(&proc, postorder);
        let dom_tree = Tree::new(proc.cfg.entry(), idom(&proc.cfg, postorder));
        let result = pinning(&proc, postorder, &dom_tree, &live);

        assert!(!result[4].is_pinned_out("x"));
        assert!(!result[4].is_pinned("x"));
        assert!(result[0].is_pinned_out("x"));
        assert!(!result[0].is_pinned("x"));
        assert!(result[1].is_pinned_out("x"));
        assert!(result[1].is_pinned("x"));
        assert!(result[2].is_pinned_out("x"));
        assert!(result[2].is_pinned("x"));
        assert!(!result[3].is_pinned_out("x"));
        assert!(!result[3].is_pinned("x"));
    }
}
