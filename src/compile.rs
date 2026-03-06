use std::collections::{HashMap, VecDeque};
use std::iter::{chain, zip};
use std::mem::{replace, take};
use std::num::NonZero;
use std::ops::Range;
use std::slice;

use smallvec::SmallVec;

use crate::utils::exact_size_chain;
use crate::{asm, core};
use crate::id::{Id, IdGen};
use crate::analysis::{self, Cfg, DefUse, Procedure, liveness};
use crate::graph::{dfs, EdgeArray, EntryNode, Graph, Idx, NodeOrdering, Predecessors, Successors, Tree, idom, predecessor_edges};
use crate::stack::Stack;

pub fn compile(program: core::Program, ids: &mut IdGen) -> Vec<asm::Instr> {
    let mut code = vec![];

    compile_proc(program.main, &[], Some(program.rets), ids, &mut code);

    for (label, proc) in program.procs {
        code.push(asm::Instr::JumpDest(label));
        compile_proc(proc.body, &proc.args, None, ids, &mut code);
    }

    code
}

fn compile_proc(
    proc_body: core::Block,
    args: &[Id],
    stop: Option<usize>,
    ids: &mut IdGen,
    code: &mut Vec<asm::Instr>,
) {
    let proc = build_cfg(proc_body, stop, ids);
    let analysis = analyze(&proc);
    let mut block_code: Box<[Vec<asm::Instr>]> = vec![vec![]; proc.blocks.len()].into_boxed_slice();

    let mut stack = Stack::new();
    stack.extend(args.iter().copied().rev());

    let dom_tree = analysis.dom_tree();
    for visit in dfs(dom_tree) {
        if visit.exit {
            stack.pop_checkpoint();
            continue;
        }
        stack.push_checkpoint();

        let block_id = visit.node;
        let block = proc.block(block_id);
        let liveness = analysis.liveness(block_id);
        let pinning = analysis.pinning(block_id);
        let last_use = collect_last_use(&proc, block_id, liveness.used_count());

        if proc.predecessors(block_id).len() > 1 {
            let dead_count = stack
                .contents()
                .iter()
                .rposition(|&x| x.is_some_and(|x| liveness.live_in(x)))
                .map_or(stack.len(), |i| stack.len() - 1 - i);
            stack.popn(dead_count);
        }

        compile_block(
            block,
            proc.fallthrough(block_id).and_then(|i| proc.label(i)),
            liveness,
            pinning,
            &last_use,
            ids,
            &mut stack,
            &mut block_code[block_id.index()],
        );
    }

    code.reserve(block_code.iter().map(Vec::len).sum());
    for block_id in proc.blocks_rpo() {
        code.extend(take(&mut block_code[block_id.index()]));
    }
}

fn collect_last_use(proc: &ProcCfg, block_id: CfgId, capacity: usize) -> HashMap<Id, InstrIdx> {
    let mut last_use = HashMap::with_capacity(capacity);
    for (i, x, _) in proc.instructions(block_id).rev() {
        last_use.entry(x).or_insert(i);
    }
    last_use
}

fn compile_block(
    block: BasicBlockRef,
    fallthrough_label: Option<Id>,
    liveness: &BlockLiveness,
    pinning: &BlockPinning,
    last_use: &HashMap<Id, InstrIdx>,
    ids: &mut IdGen,
    stack: &mut Stack<Id>,
    code: &mut Vec<asm::Instr>,
) {
    stack.extend(block.data.input);

    if let Some(label) = block.data.label {
        code.push(asm::Instr::JumpDest(label));
    }

    for (i, (x, expr)) in block.priors().iter().enumerate() {
        let is_last_use = |y| !liveness.live_out(y) && last_use[&y] == InstrIdx::Prior(i);
        compile_expr(expr, *x, is_last_use, pinning, ids, stack, code);
    }

    compile_cont(
        &block.data.cont,
        fallthrough_label,
        liveness,
        pinning,
        last_use,
        stack,
        code,
    );
}

fn compile_cont(
    cont: &Cont,
    fallthrough_label: Option<Id>,
    liveness: &BlockLiveness,
    pinning: &BlockPinning,
    last_use: &HashMap<Id, InstrIdx>,
    stack: &mut Stack<Id>,
    code: &mut Vec<asm::Instr>,
) {
    use asm::*;

    let mut move_candidates = collect_cont_move_candidates(stack, liveness, pinning, last_use);

    while let Some((from_kind, from_index)) = move_candidates.next() {
        if from_kind == ContMoveKind::Dead {
            let top_index = stack.len() - 1;
            if from_index < top_index {
                let from_depth = top_index - from_index;
                code.push(Instr::Swap(from_depth));
                stack.swap(from_depth);
            }
            code.push(Instr::Pop);
            stack.popn(1);
        } else if from_kind == ContMoveKind::PinOut
            && let Some((to_kind, to_index)) =
                move_candidates.rfind(|&(k, _)| k != ContMoveKind::PinOut)
        {
            debug_assert!(to_index < from_index);
            let top_index = stack.len() - 1;
            if from_index < top_index {
                let from_depth = top_index - from_index;
                code.push(Instr::Swap(from_depth));
                stack.swap(from_depth);
            }
            let to_depth = top_index - to_index;
            code.push(Instr::Swap(to_depth));
            stack.swap(to_depth);
            if to_kind == ContMoveKind::Dead {
                code.push(Instr::Pop);
                stack.popn(1);
            }
        }
    }

    let should_move = |x: Id| !liveness.live_out(x) && last_use[&x] == InstrIdx::Cont;

    match *cont {
        Cont::Stop(_) => {
            code.push(Instr::Stop);
        }

        Cont::Ret(x) => {
            let offset = x.is_some() as usize;
            if offset > 0 {
                code.push(Instr::Swap(offset));
            }
            code.push(Instr::Jump);
        }

        Cont::Jump(target, ref args) => {
            compile_args(args, None, should_move, pinning, stack, code);
            stack.popn(args.len());

            if Some(target) != fallthrough_label {
                code.push(Instr::PushLabel(target));
                code.push(Instr::Jump);
            }
        }

        Cont::JumpIf { cond, then } => {
            let should_move = should_move(cond) && !is_stack_top_pinned(stack, pinning);
            compile_var(cond, None, 0, should_move, stack, code);
            code.push(Instr::PushLabel(then));
            code.push(Instr::JumpIf);
            stack.popn(1);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ContMoveKind {
    PinOut,
    Unpinned,
    Dead,
}

fn collect_cont_move_candidates(
    stack: &Stack<Id>,
    liveness: &BlockLiveness,
    pinning: &BlockPinning,
    last_use: &HashMap<Id, InstrIdx>,
) -> impl DoubleEndedIterator<Item = (ContMoveKind, usize)> + use<> {
    struct Segment {
        kind: ContMoveKind,
        range: Range<usize>,
    }

    let mut segments: Vec<Segment> = vec![];
    let mut unmatched_pinouts = 0usize;
    let mut below_pinned_through = false;

    for (index, &slot) in stack.contents().iter().enumerate().rev() {
        if below_pinned_through && unmatched_pinouts == 0 {
            break;
        }

        let kind = match slot {
            Some(x) if pinning.is_pinned_through(x) => {
                below_pinned_through = true;
                continue;
            }
            Some(x) if pinning.is_pinned_out(x) => {
                if below_pinned_through {
                    continue;
                }
                unmatched_pinouts += 1;
                ContMoveKind::PinOut
            }
            _ => {
                if below_pinned_through {
                    unmatched_pinouts -= 1;
                }
                if let Some(x) = slot && (liveness.live_out(x) || last_use.get(&x) == Some(&InstrIdx::Cont)) {
                    ContMoveKind::Unpinned
                } else {
                    ContMoveKind::Dead
                }
            }
        };

        if let Some(segment) = segments.last_mut()
            && segment.kind == kind
            && segment.range.start == index + 1
        {
            segment.range.start = index;
        } else {
            segments.push(Segment {
                kind,
                range: index..index + 1,
            });
        }
    }

    segments
        .into_iter()
        .flat_map(|segment| segment.range.rev().map(move |i| (segment.kind, i)))
}

fn compile_expr(
    expr: &core::Expr,
    output: Option<Id>,
    is_last_use: impl Fn(Id) -> bool,
    pinning: &BlockPinning,
    ids: &mut IdGen,
    stack: &mut Stack<Id>,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;
    match expr {
        Expr::Const(c) => {
            code.push(Instr::Push(*c));
            stack.push(output);
        }

        Expr::Var(x) => {
            let should_move = is_last_use(*x) && !is_stack_top_pinned(stack, pinning);
            compile_var(*x, output, 0, should_move, stack, code);
        }

        Expr::Op(op, args) => {
            compile_args(args, None, is_last_use, pinning, stack, code);
            code.push(Instr::Op(*op));
            stack.popn(args.len());
            stack.extend(output);
        }

        Expr::Apply(target, args) => {
            let ret = ids.generate();
            compile_args(args, Some(ret), is_last_use, pinning, stack, code);
            code.push(Instr::PushLabel(*target));
            code.push(Instr::Jump);
            code.push(Instr::JumpDest(ret));
            stack.popn(args.len() + 1);
            stack.extend(output);
        }

        Expr::Unit | Expr::IfThenElse(..) => panic!(),
    }
}

fn compile_args(
    args: &[Id],
    ret_label: Option<Id>,
    is_last_use: impl Fn(Id) -> bool,
    pinning: &BlockPinning,
    stack: &mut Stack<Id>,
    code: &mut Vec<asm::Instr>,
) {
    use asm::*;

    struct ArgPlan {
        should_move: bool,
        target_depth: usize,
    }

    let mut plan: SmallVec<[ArgPlan; 8]> = SmallVec::with_capacity(args.len());
    let mut move_count = 0usize;
    let mut allow_moves = true;

    for (i, &arg) in args.iter().enumerate() {
        let target_depth = move_count;

        let can_move = allow_moves && is_last_use(arg) && !args[..i].contains(&arg);
        let should_move = can_move
            && stack.read(move_count).is_none_or(|x| !pinning.is_pinned_through(x));
        if can_move && !should_move {
            allow_moves = false;
        }

        plan.push(ArgPlan { should_move, target_depth });
        move_count += should_move as usize;
    }

    if let Some(ret_label) = ret_label {
        code.push(Instr::PushLabel(ret_label));
        stack.push(None);
        let offset = move_count;
        if offset > 0 {
            code.push(Instr::Swap(offset));
            stack.swap(offset);
        }
    }

    for (&arg, plan) in zip(args, plan).rev() {
        compile_var(arg, None, plan.target_depth, plan.should_move, stack, code);
    }
}

fn compile_var(
    x: Id,
    name: Option<Id>,
    target_depth: usize,
    should_move: bool,
    stack: &mut Stack<Id>,
    code: &mut Vec<asm::Instr>,
) {
    use asm::*;
    let depth = stack.depth(x);
    if should_move {
        if depth > 0 {
            code.push(Instr::Swap(depth));
            stack.swap(depth);
        }
        stack.popn(1);
    } else {
        code.push(Instr::Dup(depth));
    }
    stack.push(name);

    if target_depth > 0 {
        code.push(Instr::Swap(target_depth));
        stack.swap(target_depth);
    }
}

type BlockLiveness = analysis::BlockLiveness<Id>;
type BlockPinning = analysis::Pinning<Id>;

fn is_stack_top_pinned(stack: &Stack<Id>, pinning: &BlockPinning) -> bool {
    stack.read(0).is_some_and(|y| pinning.is_pinned_through(y))
}

fn analyze(proc: &ProcCfg) -> ProcAnalysis {
    let postorder = proc.postorder();
    let liveness = liveness(proc, &postorder);
    let dom_tree = Tree::new(proc.entry(), idom(proc, &postorder));
    let pinning = analysis::pinning(proc, &postorder, &dom_tree, &liveness);
    ProcAnalysis { liveness, pinning, dom_tree }
}

struct ProcAnalysis {
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
struct CfgId(NonZero<usize>);

impl Idx for CfgId {
    fn new(index: usize) -> Self {
        CfgId(NonZero::new(index + 1).unwrap())
    }

    fn index(self) -> usize {
        self.0.get() - 1
    }
}

struct ProcCfg {
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
    Ret(Option<Id>),
    Stop(Option<Id>),
    Jump(Id, Box<[Id]>),
    JumpIf { cond: Id, then: Id },
}

impl ProcCfg {
    fn block(&self, block_id: CfgId) -> BasicBlockRef<'_> {
        BasicBlockRef {
            proc: self,
            data: &self.blocks[block_id.index()],
        }
    }

    fn label(&self, block_id: CfgId) -> Option<Id> {
        self.blocks[block_id.index()].label
    }

    fn fallthrough(&self, block_id: CfgId) -> Option<CfgId> {
        block_id.index().checked_sub(1).map(CfgId::new)
    }

    fn successor_blocks(&self, block_id: CfgId) -> impl ExactSizeIterator<Item = CfgId> {
        let (target, fallthrough) = match &self.block(block_id).data.cont {
            Cont::Stop(_) | Cont::Ret(_) => (None, None),
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

struct BasicBlockRef<'a> {
    proc: &'a ProcCfg,
    data: &'a BasicBlock,
}

impl<'a> BasicBlockRef<'a> {
    fn priors(&self) -> &'a [(Option<Id>, core::Expr)] {
        &self.proc.segments[self.data.segment][self.data.start..self.data.end]
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
    if let Some(rets) = stop
        && let TailExpr::Apply(target, args) = tail
    {
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

fn build_cfg(proc_body: core::Block, stop: Option<usize>, ids: &mut IdGen) -> ProcCfg {
    use core::*;

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
        ($block:ident) => {{
            let (priors, tail) = normalize_tail($block, stop, ids);
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

    queue.push_front(QueueItem::Unvisited(build_candidate!(proc_body)));

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
                                    if stop.is_some() {
                                        Cont::Stop(res)
                                    } else {
                                        Cont::Ret(res)
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
    #[allow(refining_impl_trait)]
    fn successors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        self.successor_blocks(node)
    }
}

impl Predecessors for ProcCfg {
    #[allow(refining_impl_trait)]
    fn predecessors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        self.preds.edges_from(node)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum InstrIdx {
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

        fn instrs<'a>(
            idx: InstrIdx,
            def_use: DefUse,
            ids: &'a [Id],
        ) -> impl DoubleEndedIterator<Item = (InstrIdx, Id, DefUse)> + use<'a> {
            ids.iter().map(move |&id| (idx, id, def_use))
        }

        let block = self.block(b);
        let input_defs = block
            .data
            .input
            .map(|id| (InstrIdx::Input, id, DefUse::Def));
        let cont_ids: &[Id] = match &block.data.cont {
            Cont::Stop(x) | Cont::Ret(x) => x.as_slice(),
            Cont::Jump(_, args) => args,
            Cont::JumpIf { cond, .. } => slice::from_ref(cond),
        };
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
            let uses_iter = instrs(InstrIdx::Prior(i), DefUse::Use, ids);
            chain(def_iter, uses_iter)
        });

        let cont_uses = instrs(InstrIdx::Cont, DefUse::Use, cont_ids);

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
        let indexed = build_cfg(block, Some(1), &mut ids);
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
        let indexed = build_cfg(block, Some(1), &mut ids);
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

        let indexed = build_cfg(block, Some(1), &mut ids);
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
