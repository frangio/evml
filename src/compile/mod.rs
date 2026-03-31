use std::collections::{HashMap, VecDeque};
use std::iter::{chain, zip};
use std::mem::{replace, take};
use std::num::NonZero;
use std::slice;

use crate::utils::exact_size_chain;
use crate::{asm, core};
use crate::id::{Id, IdGen};
use crate::analysis::{self, Cfg, DefUse, Procedure, liveness};
use crate::graph::{EdgeArray, EntryNode, Graph, Idx, NodeOrdering, Predecessors, Successors, Tree, idom, predecessor_edges};

mod plan;

pub fn compile(program: core::Program, ids: &mut IdGen) -> Vec<asm::Instr> {
    let mut code = vec![];

    compile_proc(
        core::Proc {
            args: Box::new([]),
            rets: program.rets,
            body: program.main,
        },
        true,
        ids,
        &mut code,
    );

    for (label, proc) in program.procs {
        code.push(asm::Instr::JumpDest(label));
        compile_proc(proc, false, ids, &mut code);
    }

    code
}

fn compile_proc(
    proc: core::Proc,
    stop: bool,
    ids: &mut IdGen,
    code: &mut Vec<asm::Instr>,
) {
    let proc = build_cfg(proc, stop, ids);
    let block_plans = plan::plan_proc(&proc);

    for block_id in proc.blocks_rpo() {
        emit_block(
            proc.block(block_id),
            &block_plans[block_id.index()],
            proc.fallthrough(block_id).and_then(|i| proc.label(i)),
            ids,
            code,
        );
    }
}

fn emit_block(
    block: BasicBlockRef,
    block_plan: &plan::BlockPlan,
    fallthrough_label: Option<Id>,
    ids: &mut IdGen,
    code: &mut Vec<asm::Instr>,
) {
    if let Some(label) = block.data().label {
        code.push(asm::Instr::JumpDest(label));
    }

    let mut block_actions = block_plan.actions();

    for ((_, expr), actions) in zip(block.priors(), &mut block_actions) {
        let ret = emit_actions(actions, ids, code);
        emit_expr(expr, code);
        if let Some(ret) = ret {
            code.push(asm::Instr::JumpDest(ret));
        }
    }

    let cont_actions = block_actions.next().unwrap();
    assert!(block_actions.next().is_none());

    emit_actions(cont_actions, ids, code);
    emit_cont(&block.data().cont, fallthrough_label, code);
}

fn emit_actions(actions: &[plan::Action], ids: &mut IdGen, code: &mut Vec<asm::Instr>) -> Option<Id> {
    use asm::Instr;
    use plan::Action;
    let mut ret = None;
    for &action in actions {
        match action {
            Action::Pop => {
                code.push(Instr::Pop);
            }
            Action::PushLabel => {
                let ret = *ret.get_or_insert_with(|| ids.generate());
                code.push(Instr::PushLabel(ret));
            }
            Action::Swap(depth) => {
                code.push(Instr::Swap(depth));
            }
            Action::Dup(depth) => {
                code.push(Instr::Dup(depth));
            }
        }
    }
    ret
}

fn emit_expr(expr: &core::Expr, code: &mut Vec<asm::Instr>) {
    use core::*;
    use asm::*;
    match *expr {
        Expr::Var(_) => {}

        Expr::Const(c) => {
            code.push(Instr::Push(c));
        }

        Expr::Op(op, _) => {
            code.push(Instr::Op(op));
        }

        Expr::Apply(target, _) => {
            code.push(Instr::PushLabel(target));
            code.push(Instr::Jump);
        }

        Expr::Unit | Expr::IfThenElse(..) => panic!(),
    }
}

fn emit_cont(
    cont: &Cont,
    fallthrough_label: Option<Id>,
    code: &mut Vec<asm::Instr>,
) {
    use asm::*;
    match *cont {
        Cont::Ret { target_var, .. } => {
            if target_var.is_some() {
                code.push(Instr::Jump);
            } else {
                code.push(Instr::Stop);
            }
        }

        Cont::Jump(target, _) => {
            if Some(target) != fallthrough_label {
                code.push(Instr::PushLabel(target));
                code.push(Instr::Jump);
            }
        }

        Cont::JumpIf { then, .. } => {
            code.push(Instr::PushLabel(then));
            code.push(Instr::JumpIf);
        }
    }
}

type BlockLiveness = analysis::BlockLiveness<Id>;
type BlockPinning = analysis::Pinning<Id>;

pub fn analyze(proc: &ProcCfg) -> ProcAnalysis {
    let postorder = proc.postorder();
    let liveness = liveness(proc, &postorder);
    let dom_tree = Tree::new(proc.entry(), idom(proc, &postorder));
    let pinning = analysis::pinning(proc, &postorder, &dom_tree, &liveness);
    ProcAnalysis { liveness, pinning, dom_tree }
}

pub struct ProcAnalysis {
    liveness: Box<[BlockLiveness]>,
    pinning: Box<[BlockPinning]>,
    dom_tree: Tree<CfgId>,
}

impl ProcAnalysis {
    fn liveness(&self, block_id: CfgId) -> &BlockLiveness {
        &self.liveness[block_id.index()]
    }

    fn pinning(&self, block_id: CfgId) -> &BlockPinning {
        &self.pinning[block_id.index()]
    }

    fn dom_tree(&self) -> &Tree<CfgId> {
        &self.dom_tree
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CfgId(NonZero<usize>);

impl Idx for CfgId {
    fn new(index: usize) -> Self {
        CfgId(NonZero::new(index + 1).unwrap())
    }

    fn index(self) -> usize {
        self.0.get() - 1
    }
}

pub struct ProcCfg {
    args: Box<[Id]>,
    ret_target_var: Option<Id>,
    blocks: Box<[BasicBlock]>,
    segments: Box<[Box<[(Option<Id>, core::Expr)]>]>,
    labeled_blocks: HashMap<Id, usize>,
    preds: EdgeArray<CfgId>,
}

#[derive(PartialEq, Eq, Debug)]
struct BasicBlock {
    label: Option<Id>,
    input: Option<Id>,
    segment: usize,
    start: usize,
    end: usize,
    cont: Cont,
}

#[derive(PartialEq, Eq, Debug)]
enum Cont {
    Ret { target_var: Option<Id>, value: Option<Id> },
    Jump(Id, Box<[Id]>),
    JumpIf { cond: Id, then: Id },
}

impl ProcCfg {
    fn ret_target_var(&self) -> Option<Id> {
        self.ret_target_var
    }

    pub fn block(&self, block_id: CfgId) -> BasicBlockRef<'_> {
        BasicBlockRef {
            id: block_id,
            proc: self,
        }
    }

    fn label(&self, block_id: CfgId) -> Option<Id> {
        self.blocks[block_id.index()].label
    }

    fn fallthrough(&self, block_id: CfgId) -> Option<CfgId> {
        block_id.index().checked_sub(1).map(CfgId::new)
    }

    fn successor_blocks(&self, block_id: CfgId) -> impl ExactSizeIterator<Item = CfgId> {
        let (target, fallthrough) = match &self.block(block_id).data().cont {
            Cont::Ret { .. } => (None, None),
            Cont::Jump(target, _) => (
                // Target may be another procedure if this is a tail call
                self.labeled_blocks.get(target).map(|&i| CfgId::new(i)),
                None,
            ),
            Cont::JumpIf { then, .. } => (
                Some(CfgId::new(self.labeled_blocks[then])),
                Some(self.fallthrough(block_id).unwrap()),
            ),
        };
        exact_size_chain(target, fallthrough)
    }

    fn postorder(&self) -> IndexedProcPostorder {
        IndexedProcPostorder {
            block_count: self.blocks.len(),
        }
    }

    fn blocks_rpo(&self) -> impl Iterator<Item = CfgId> {
        self.postorder().iter().rev()
    }
}

pub struct BasicBlockRef<'a> {
    id: CfgId,
    proc: &'a ProcCfg,
}

impl<'a> BasicBlockRef<'a> {
    fn data(&self) -> &'a BasicBlock {
        &self.proc.blocks[self.id.index()]
    }

    pub fn inputs(&self) -> &'a [Id] {
        if self.id == self.proc.entry() {
            self.proc.args.as_ref()
        } else {
            self.data().input.as_slice()
        }
    }

    fn priors(&self) -> &'a [(Option<Id>, core::Expr)] {
        let data = self.data();
        &self.proc.segments[data.segment][data.start..data.end]
    }
}

pub struct IndexedProcPostorder {
    block_count: usize,
}

impl NodeOrdering<CfgId> for IndexedProcPostorder {
    fn position(&self, node: CfgId) -> usize {
        let index = node.index();
        assert!(index < self.block_count);
        index
    }

    fn node_at(&self, position: usize) -> CfgId {
        assert!(position < self.block_count);
        CfgId::new(position)
    }

    #[allow(refining_impl_trait)]
    fn iter(&self) -> impl DoubleEndedIterator<Item = CfgId> + ExactSizeIterator + use<> {
        (0..self.block_count).map(CfgId::new)
    }
}

fn normalize_tail(
    block: core::Block,
    stop: Option<usize>,
    ids: &mut IdGen,
) -> (Vec<(Option<Id>, core::Expr)>, core::TailExpr) {
    use core::{Block, Expr, TailExpr};

    let Block {
        mut priors,
        mut tail,
    } = block;
    if let Some(rets) = stop && let TailExpr::Apply(target, args) = tail {
        assert!(rets <= 1);
        if rets == 0 {
            priors.push((None, Expr::Apply(target, args)));
            tail = TailExpr::Unit;
        } else {
            let res = ids.generate();
            priors.push((Some(res), Expr::Apply(target, args)));
            tail = TailExpr::Var(res);
        }
    }
    (priors, tail)
}

struct BasicBlockCandidate {
    label: Option<Id>,
    input: Option<Id>,
    segment: usize,
    start: usize,
    tail: core::TailExpr,
    cont_label: Option<Id>,
}

impl BasicBlockCandidate {
    fn split_at_control(
        &mut self,
        segments: &mut [Box<[(Option<Id>, core::Expr)]>],
        ids: &mut IdGen,
    ) -> Option<(usize, BasicBlockCandidate)> {
        use core::{Expr, TailExpr};

        let split = segments[self.segment]
            .iter_mut()
            .enumerate()
            .skip(self.start)
            .find_map(|(i, (_, e))| matches!(e, Expr::IfThenElse(..)).then_some(i))?;

        let (split_output, Expr::IfThenElse(cond, then_else)) =
            take(&mut segments[self.segment][split])
        else {
            unreachable!()
        };

        let cont_label = self.cont_label;

        let join_label = Some(ids.generate());
        self.cont_label = join_label;

        let tail = replace(&mut self.tail, TailExpr::IfThenElse(cond, then_else));

        Some((
            split,
            BasicBlockCandidate {
                label: join_label,
                input: split_output,
                segment: self.segment,
                start: split + 1,
                tail,
                cont_label,
            },
        ))
    }
}

fn build_cfg(proc: core::Proc, stop: bool, ids: &mut IdGen) -> ProcCfg {
    use core::*;

    let Proc { args, body, rets } = proc;
    let ret_target_var = (!stop).then(|| ids.generate());

    enum QueueItem {
        Finished(BasicBlock),
        Discovered(BasicBlock),
        Unvisited(BasicBlockCandidate),
    }

    let mut label_count = 0;

    macro_rules! generate_label {
        () => {{
            label_count += 1;
            ids.generate()
        }};
    }

    let mut segments = vec![];
    let mut queue = VecDeque::new();

    macro_rules! build_candidate {
        ($block:expr) => {{
            let (priors, tail) = normalize_tail($block, stop.then_some(rets), ids);
            let segment = segments.len();
            segments.push(priors.into_boxed_slice());
            BasicBlockCandidate {
                segment,
                tail,
                start: 0,
                label: None,
                input: None,
                cont_label: None,
            }
        }};
    }

    queue.push_front(QueueItem::Unvisited(build_candidate!(body)));

    while queue
        .front()
        .is_some_and(|item| !matches!(item, QueueItem::Finished(_)))
    {
        match queue.pop_front().unwrap() {
            QueueItem::Finished(_) => unreachable!(),

            QueueItem::Discovered(basic_block) => {
                queue.push_back(QueueItem::Finished(basic_block));
            }

            QueueItem::Unvisited(mut candidate) => {
                let (end, join) = candidate.split_at_control(&mut segments, ids).unzip();

                let end = end.unwrap_or_else(|| segments[candidate.segment].len());

                if let Some(join) = &join
                    && join.label.is_some()
                {
                    label_count += 1;
                }

                let BasicBlockCandidate {
                    label,
                    input,
                    segment,
                    start,
                    tail,
                    cont_label,
                } = candidate;

                match tail {
                    TailExpr::Unit | TailExpr::Var(_) | TailExpr::Apply(_, _) => {
                        let cont = match tail {
                            TailExpr::Unit | TailExpr::Var(_) => {
                                let res = if let TailExpr::Var(x) = tail {
                                    Some(x)
                                } else {
                                    None
                                };
                                cont_label.map_or(
                                    if stop {
                                        Cont::Ret { target_var: None, value: res }
                                    } else {
                                        Cont::Ret { target_var: ret_target_var, value: res }
                                    },
                                    |cont| Cont::Jump(cont, res.into_iter().collect()),
                                )
                            }

                            TailExpr::Apply(target, args) => {
                                assert!(cont_label.is_none());
                                Cont::Jump(target, args)
                            }

                            TailExpr::IfThenElse(..) => unreachable!(),
                        };
                        queue.push_back(QueueItem::Finished(BasicBlock {
                            label,
                            input,
                            segment,
                            start,
                            end,
                            cont,
                        }))
                    }

                    TailExpr::IfThenElse(cond, then_else) => {
                        let [then_block, else_block] = *then_else;
                        let then_label = generate_label!();

                        queue.push_front(QueueItem::Discovered(BasicBlock {
                            label,
                            input,
                            segment,
                            start,
                            end,
                            cont: Cont::JumpIf {
                                cond,
                                then: then_label,
                            },
                        }));

                        queue.push_front(QueueItem::Unvisited(BasicBlockCandidate {
                            cont_label,
                            ..build_candidate!(else_block)
                        }));

                        queue.push_front(QueueItem::Unvisited(BasicBlockCandidate {
                            label: Some(then_label),
                            cont_label,
                            ..build_candidate!(then_block)
                        }));
                    }
                }

                if let Some(join) = join {
                    queue.push_front(QueueItem::Unvisited(join));
                }
            }
        }
    }

    let mut labeled_blocks = HashMap::with_capacity(label_count);

    // Blocks are now in postorder
    let blocks: Vec<_> = Vec::from(queue)
        .into_iter()
        .enumerate()
        .map(|(i, item)| {
            let QueueItem::Finished(b) = item else {
                unreachable!()
            };
            if let Some(label) = b.label {
                labeled_blocks.insert(label, i);
            }
            b
        })
        .collect();

    let mut cfg = ProcCfg {
        args,
        ret_target_var,
        segments: segments.into_boxed_slice(),
        preds: EdgeArray::default(),
        blocks: blocks.into_boxed_slice(),
        labeled_blocks,
    };
    cfg.preds = predecessor_edges(&cfg);
    cfg
}

impl Graph for ProcCfg {
    type Node = CfgId;

    fn node_count(&self) -> usize {
        self.blocks.len()
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        let postorder = self.postorder();
        postorder.iter()
    }
}

impl EntryNode for ProcCfg {
    fn entry(&self) -> CfgId {
        CfgId::new(self.blocks.len() - 1)
    }
}

impl Successors for ProcCfg {
    fn successors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        self.successor_blocks(node)
    }
}

impl Predecessors for ProcCfg {
    fn predecessors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        self.preds.edges_from(node).iter().copied()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum InstrIdx {
    Input,
    Prior(usize),
    Cont,
}

impl Procedure for ProcCfg {
    type BlockId = CfgId;
    type VarId = Id;
    type InstrIdx = InstrIdx;

    fn cfg(&self) -> impl Cfg<Node = Self::BlockId> {
        self
    }

    fn instructions(
        &self,
        b: Self::BlockId,
    ) -> impl DoubleEndedIterator<Item = (InstrIdx, Id, DefUse)> {
        use core::*;

        let block = self.block(b);
        let input_defs = block
            .inputs()
            .iter()
            .map(|&id| (InstrIdx::Input, id, DefUse::Def));

        let priors = block.priors();

        let prior_def_uses = priors.iter().enumerate().flat_map(|(i, (def, expr))| {
            let def_iter = def.map(|id| (InstrIdx::Prior(i), id, DefUse::Def));
            let ids: &[Id] = match expr {
                Expr::Unit | Expr::Const(_) => &[],
                Expr::Var(id) => slice::from_ref(id),
                Expr::Op(_, args) => args,
                Expr::Apply(_, args) => args,
                Expr::IfThenElse(id, _) => slice::from_ref(id),
            };
            let uses_iter = ids.iter().map(move |&id| (InstrIdx::Prior(i), id, DefUse::Use));
            chain(def_iter, uses_iter)
        });

        let (cont_args, cont_target_var) = match &block.data().cont {
            Cont::Ret { target_var, value } => (value.as_slice(), *target_var),
            Cont::Jump(target, args) => {
                let tail_call = !self.labeled_blocks.contains_key(target);
                (args.as_ref(), tail_call.then_some(self.ret_target_var).flatten())
            }
            Cont::JumpIf { cond, .. } => (slice::from_ref(cond), None),
        };
        let cont_uses = exact_size_chain(
            cont_args.iter().copied(),
            cont_target_var,
        ).map(|id| (InstrIdx::Cont, id, DefUse::Use));

        chain(input_defs, prior_def_uses).chain(cont_uses)
    }
}

#[cfg(test)]
mod tests {
    use revm::primitives::U256;

    use super::*;
    use crate::id::{IdGen, generate_ids};
    use crate::{
        asm::Instr::*,
        core::{self, Block, Expr::*, TailExpr},
        graph::Successors,
    };

    fn program(main: Block, rets: usize) -> core::Program {
        core::Program {
            main,
            rets,
            procs: vec![],
        }
    }

    #[test]
    fn test_index_trivial() {
        let mut ids = IdGen::new();
        generate_ids! { x in ids };
        let block = Block {
            priors: vec![],
            tail: TailExpr::Var(x),
        };
        let indexed = build_cfg(core::Proc { args: Box::new([]), rets: 1, body: block }, true, &mut ids);
        assert_eq!(indexed.blocks.len(), 1);

        let entry_successors: Vec<_> = indexed.successors(indexed.entry()).collect();
        assert!(entry_successors.is_empty());
    }

    #[test]
    fn test_index_if_then_else_tail() {
        let mut ids = IdGen::new();
        generate_ids! { x, y, z in ids };
        let block = Block {
            priors: vec![],
            tail: TailExpr::IfThenElse(
                x,
                Box::new([
                    Block {
                        priors: vec![],
                        tail: TailExpr::Var(y),
                    },
                    Block {
                        priors: vec![],
                        tail: TailExpr::Var(z),
                    },
                ]),
            ),
        };
        let indexed = build_cfg(core::Proc { args: Box::new([]), rets: 1, body: block }, true, &mut ids);
        assert_eq!(indexed.blocks.len(), 3);

        let entry = indexed.entry();
        let entry_successors: Vec<_> = indexed.successors(entry).collect();
        assert_eq!(entry_successors.len(), 2);
        let [branch0, branch1] = entry_successors[..] else {
            panic!()
        };

        let branch0_successors: Vec<_> = indexed.successors(branch0).collect();
        let branch1_successors: Vec<_> = indexed.successors(branch1).collect();

        assert_eq!(branch0_successors, branch1_successors);
        assert!(branch0_successors.is_empty());
    }

    #[test]
    fn test_index_if_then_else_prior() {
        let mut ids = IdGen::new();
        generate_ids! { x, y in ids };
        generate_ids! { t, f in ids };
        let block = Block {
            priors: vec![
                (Some(x), Const(U256::from(1))),
                (
                    Some(y),
                    IfThenElse(
                        x,
                        Box::new([
                            Block {
                                priors: vec![(Some(t), Const(U256::from(1)))],
                                tail: TailExpr::Var(t),
                            },
                            Block {
                                priors: vec![(Some(f), Const(U256::from(0)))],
                                tail: TailExpr::Var(f),
                            },
                        ]),
                    ),
                ),
            ],
            tail: TailExpr::Var(y),
        };

        let indexed = build_cfg(core::Proc { args: Box::new([]), rets: 1, body: block }, true, &mut ids);
        assert_eq!(indexed.blocks.len(), 4);

        let entry = indexed.entry();

        let entry_successors: Vec<_> = indexed.successors(entry).collect();
        assert_eq!(entry_successors.len(), 2);
        let [branch0, branch1] = entry_successors[..] else {
            panic!()
        };

        let branch0_successors: Vec<_> = indexed.successors(branch0).collect();
        let branch1_successors: Vec<_> = indexed.successors(branch1).collect();
        assert_eq!(branch0_successors, branch1_successors);
        assert_eq!(branch0_successors.len(), 1);
        let [tail] = branch0_successors[..] else {
            panic!()
        };

        let tail_successors: Vec<_> = indexed.successors(tail).collect();
        assert!(tail_successors.is_empty());
    }

    #[test]
    fn test_compile_if_then_else_tail() {
        let mut ids = IdGen::new();
        generate_ids! { x, t, f in ids };
        let block = Block {
            priors: vec![(Some(x), Const(U256::from(2)))],
            tail: TailExpr::IfThenElse(
                x,
                Box::new([
                    Block {
                        priors: vec![(Some(t), Const(U256::from(1)))],
                        tail: TailExpr::Var(t),
                    },
                    Block {
                        priors: vec![(Some(f), Const(U256::from(0)))],
                        tail: TailExpr::Var(f),
                    },
                ]),
            ),
        };
        let code = compile(program(block, 1), &mut ids.clone());
        generate_ids! { label in ids };
        assert_eq!(
            code,
            vec![
                Push(U256::from(2)),
                PushLabel(label),
                JumpIf,
                Push(U256::from(0)),
                Stop,
                JumpDest(label),
                Push(U256::from(1)),
                Stop,
            ]
        );
    }

    #[test]
    fn test_compile_if_then_else_prior() {
        let mut ids = IdGen::new();
        generate_ids! { x, y, t, f in ids };
        let block = Block {
            priors: vec![
                (Some(x), Const(U256::from(2))),
                (
                    Some(y),
                    IfThenElse(
                        x,
                        Box::new([
                            Block {
                                priors: vec![(Some(t), Const(U256::from(1)))],
                                tail: TailExpr::Var(t),
                            },
                            Block {
                                priors: vec![(Some(f), Const(U256::from(0)))],
                                tail: TailExpr::Var(f),
                            },
                        ]),
                    ),
                ),
            ],
            tail: TailExpr::Var(y),
        };
        let code = compile(program(block, 1), &mut ids.clone());
        generate_ids! { label1, label2 in ids };
        assert_eq!(
            code,
            vec![
                Push(U256::from(2)),
                PushLabel(label2),
                JumpIf,
                Push(U256::from(0)),
                PushLabel(label1),
                Jump,
                JumpDest(label2),
                Push(U256::from(1)),
                JumpDest(label1),
                Stop,
            ]
        );
    }

    #[test]
    fn test_compile_if_nested() {
        let mut ids = IdGen::new();
        generate_ids! { x, y, a, b, c in ids };
        let block = Block {
            priors: vec![
                (Some(x), Const(U256::from(1))),
                (Some(y), Const(U256::from(0))),
            ],
            tail: TailExpr::IfThenElse(
                x,
                Box::new([
                    Block {
                        priors: vec![],
                        tail: TailExpr::IfThenElse(
                            y,
                            Box::new([
                                Block {
                                    priors: vec![(Some(a), Const(U256::from(1)))],
                                    tail: TailExpr::Var(a),
                                },
                                Block {
                                    priors: vec![(Some(b), Const(U256::from(2)))],
                                    tail: TailExpr::Var(b),
                                },
                            ]),
                        ),
                    },
                    Block {
                        priors: vec![(Some(c), Const(U256::from(3)))],
                        tail: TailExpr::Var(c),
                    },
                ]),
            ),
        };
        let code = compile(program(block, 1), &mut ids.clone());
        generate_ids! { label1, label2 in ids };
        assert_eq!(
            code,
            vec![
                Push(U256::from(1)),
                Push(U256::from(0)),
                Swap(1),
                PushLabel(label1),
                JumpIf,
                Push(U256::from(3)),
                Swap(1),
                Pop,
                Stop,
                JumpDest(label1),
                PushLabel(label2),
                JumpIf,
                Push(U256::from(2)),
                Stop,
                JumpDest(label2),
                Push(U256::from(1)),
                Stop,
            ]
        );
    }

}
