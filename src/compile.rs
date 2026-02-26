use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::{chain, repeat_n, zip};
use std::mem::{replace, take};
use std::num::NonZero;
use std::slice;

use crate::utils::exact_size_chain;
use crate::utils::exact_size_iter::iter_some;
use crate::{asm, core};
use crate::id::{Id, IdGen};
use crate::analysis::{self, Cfg, DefUse, Procedure, liveness};
use crate::graph::{EntryNode, ExitNode, Graph, Idx, NodeOrdering, Successors, ipdom};
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

fn compile_proc(proc_body: core::Block, args: &[Id], stop: Option<usize>, ids: &mut IdGen, code: &mut Vec<asm::Instr>) {
    let proc = build_cfg(proc_body, stop, ids);
    let analysis = analyze(&proc);

    let mut stack = Stack::new();
    stack.extend(args.iter().copied());

    let mut scratch: Box<[Option<Box<[Id]>>]> = vec![None; proc.blocks.len()].into_boxed_slice();
    scratch[proc.entry().index()] = Some(Box::new([]));

    for block_id in proc.blocks_rpo() {
        let frame = analysis.frame(block_id);
        let liveness = analysis.liveness(block_id);
        let last_use = build_last_use(&proc, block_id, liveness.used_count());

        let popped = stack.len_framed().strict_sub(frame.frame_size);
        stack.pop_from_frame(popped);

        stack.extend(scratch[block_id.index()].take().unwrap());

        compile_block(
            proc.block(block_id),
            &mut stack,
            frame,
            liveness,
            &last_use,
            proc.fallthrough(block_id).and_then(|i| proc.label(i)),
            ids,
            code,
        );

        if !frame.push.is_empty() {
            stack.push_to_frame(frame.push.len());
            debug_assert!(frame.push.iter().all(|&id|
                stack.depth(id).strict_sub(stack.len_scratch()) < frame.push.len()
            ));
        }

        let succ_scratch = stack.drain_scratch().collect();
        let succs = proc.successor_blocks(block_id);
        let succs_scratch = repeat_n(succ_scratch, succs.len());
        for (succ, succ_scratch) in zip(succs, succs_scratch) {
            scratch[succ.index()] = Some(succ_scratch);
        }
    }

    assert!(stack.len() == stack.len_scratch());
    debug_assert!(scratch.iter().all(Option::is_none));
}

fn build_last_use(proc: &ProcCfg, block_id: CfgId, capacity: usize) -> HashMap<Id, InstrIdx> {
    let mut last_use = HashMap::with_capacity(capacity);
    for (i, x, _) in proc.instructions(block_id).rev() {
        last_use.entry(x).or_insert(i);
    }
    last_use
}

fn compile_block(
    block: BasicBlockRef,
    stack: &mut Stack<Id>,
    frame: &BlockFrame,
    liveness: &BlockLiveness,
    last_use: &HashMap<Id, InstrIdx>,
    fallthrough_label: Option<Id>,
    ids: &mut IdGen,
    code: &mut Vec<asm::Instr>,
) {
    stack.extend(block.data.input);

    if let Some(label) = block.data.label {
        code.push(asm::Instr::JumpDest(label));
    }

    for (i, (x, expr)) in block.priors().iter().enumerate() {
        let is_last_use = |y| {
            !liveness.live_out(y) && last_use[&y] == InstrIdx::Prior(i)
        };
        compile_expr_onto(expr, stack, is_last_use, ids, code);
        if x.is_some() {
            stack.push(*x);
        }
    }

    compile_cont(
        &block.data.cont,
        stack,
        frame,
        liveness,
        last_use,
        fallthrough_label,
        code,
    );
}

fn compile_cont(
    cont: &Cont,
    stack: &mut Stack<Id>,
    frame: &BlockFrame,
    liveness: &BlockLiveness,
    last_use: &HashMap<Id, InstrIdx>,
    fallthrough_label: Option<Id>,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;

    let scratch_end = stack.len_scratch() - frame.push.len();
    let mut next_non_scratch = scratch_end;
    let mut popped = 0;

    for d in 0..scratch_end {
        let d = d - popped;
        let x = stack.read(d);
        let is_cont_last_use = last_use.get(&x) == Some(&InstrIdx::Cont);
        if !liveness.live_out(x) && !is_cont_last_use {
            if d > 0 {
                code.push(Instr::Swap(d));
                stack.swap(d);
            }
            code.push(Instr::Pop);
            stack.popn(1);
            popped += 1;
            next_non_scratch -= 1;
        } else if frame.push.contains(&x) {
            let e = (next_non_scratch..stack.len()).find(|&e| {
                let y = stack.read(e);
                !frame.push.contains(&y)
            }).unwrap();
            next_non_scratch = e + 1;
            if d > 0 {
                code.push(Instr::Swap(d));
                stack.swap(d);
            }
            code.push(Instr::Swap(e));
            stack.swap(e);
        }
    }

    let should_swap = |x: Id| !liveness.live_out(x) && last_use[&x] == InstrIdx::Cont;

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
            compile_args_onto(args, None, stack, should_swap, code);
            stack.popn(args.len());

            if Some(target) != fallthrough_label {
                code.push(Instr::PushLabel(target));
                code.push(Instr::Jump);
            }
        }

        Cont::JumpIf { cond, then } => {
            compile_val_onto(&Val::Var(cond), stack, should_swap, code);
            code.push(Instr::PushLabel(then));
            code.push(Instr::JumpIf);
        }
    }
}

fn compile_expr_onto(
    expr: &core::Expr,
    stack: &mut Stack<Id>,
    is_last_use: impl Fn(Id) -> bool,
    ids: &mut IdGen,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;
    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, stack, is_last_use, code);
        }

        Expr::Op(op, args) => {
            compile_args_onto(args, None, stack, is_last_use, code);
            code.push(Instr::Op(*op));
            stack.popn(args.len());
        }

        Expr::Apply(target, args) => {
            let ret = ids.generate();
            compile_args_onto(args, Some(ret), stack, is_last_use, code);
            code.push(Instr::PushLabel(*target));
            code.push(Instr::Jump);
            code.push(Instr::JumpDest(ret));
            stack.popn(args.len() + 1);
        }

        Expr::Unit | Expr::IfThenElse(..) => panic!(),
    }
}

fn compile_args_onto(
    args: &[core::Val],
    ret_label: Option<Id>,
    stack: &mut Stack<Id>,
    is_last_use: impl Fn(Id) -> bool,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;

    let should_swap = |x, i| {
        is_last_use(x) && !args[..i].contains(&Val::Var(x))
    };

    let stack_delta = args.iter().enumerate().filter(|&(i, v)| {
        match v {
            Val::Const(_) => true,
            Val::Var(x) => !should_swap(*x, i),
        }
    }).count();

    if let Some(ret_label) = ret_label {
        code.push(Instr::PushLabel(ret_label));
        stack.push(None);
        let offset = args.len() - stack_delta;
        if offset > 0 {
            code.push(Instr::Swap(offset));
            stack.swap(offset);
        }
    }

    let target_stack_len = stack.len() + stack_delta;

    for (i, v) in args.iter().enumerate().rev() {
        let should_swap = |x: Id| should_swap(x, i);
        compile_val_onto(v, stack, should_swap, code);
        stack.push(None);
        let rem_delta = target_stack_len - stack.len();
        let offset = i - rem_delta;
        if offset > 0 {
            code.push(Instr::Swap(offset));
            stack.swap(offset);
        }
    }
}

fn compile_val_onto(
    val: &core::Val,
    stack: &mut Stack<Id>,
    should_swap: impl Fn(Id) -> bool,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;
    match *val {
        Val::Const(c) => {
            code.push(Instr::Push(c));
        }

        Val::Var(x) => {
            let depth = stack.depth(x);
            if should_swap(x) {
                if depth > 0 {
                    code.push(Instr::Swap(depth));
                    stack.swap(depth);
                }
                stack.popn(1);
            } else {
                code.push(Instr::Dup(depth));
            }
        }
    }
}

type BlockLiveness = analysis::BlockLiveness<Id>;

fn analyze(proc: &ProcCfg) -> ProcAnalysis {
    let liveness = liveness(proc, &proc.postorder());
    let ipdoms = ipdom(proc);
    let frames = build_frames(proc, &liveness, &ipdoms);
    ProcAnalysis { liveness, frames }
}

struct ProcAnalysis {
    liveness: Box<[BlockLiveness]>,
    frames: Box<[BlockFrame]>,
}

impl ProcAnalysis {
    fn liveness(&self, block_id: CfgId) -> &BlockLiveness {
        &self.liveness[block_id.index()]
    }

    fn frame(&self, block_id: CfgId) -> &BlockFrame {
        &self.frames[block_id.index()]
    }
}

#[derive(Clone, Debug, Default)]
struct BlockFrame {
    frame_size: usize,
    push: HashSet<Id>,
}

// This current scheme only works for simple structured acyclic control flow.
fn build_frames(
    proc: &ProcCfg,
    liveness: &[BlockLiveness],
    ipdoms: &[CfgId],
) -> Box<[BlockFrame]> {
    let mut frames = vec![BlockFrame::default(); proc.blocks.len()];
    let mut parents: Vec<Option<CfgId>> = vec![None; proc.node_count()];
    parents[proc.entry().index()] = Some(proc.exit());
    parents[proc.exit().index()] = Some(proc.exit());

    for block_id in proc.blocks_rpo() {
        let block_idx = block_id.index();
        let block_liveness = &liveness[block_idx];
        let ipdom = ipdoms[block_idx];
        let ipdom_liveness = &liveness[ipdom.index()];
        let parent = parents[block_idx].unwrap();
        let parent_ipdom = ipdoms[parent.index()];
        let parent_ipdom_liveness = &liveness[parent_ipdom.index()];

        let frame = &mut frames[block_idx];
        frame.push = ipdom_liveness.live_in_vars()
            .filter(|&x| block_liveness.live_out(x))
            .filter(|&x| !parent_ipdom_liveness.live_in(x))
            .collect();

        let (succ_parent, succ_frame_size) = if frame.push.is_empty() {
            (parent, frame.frame_size)
        } else {
            (block_id, frame.frame_size + frame.push.len())
        };

        if parents[ipdom.index()].is_none() {
            parents[ipdom.index()] = Some(parent);
            frames[ipdom.index()].frame_size = frame.frame_size;
        }

        for succ in proc.successor_blocks(block_id) {
            if parents[succ.index()].is_none() {
                parents[succ.index()] = Some(succ_parent);
                frames[succ.index()].frame_size = succ_frame_size;
            }
        }
    }

    frames.into_boxed_slice()
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
    Jump(Id, Box<[core::Val]>),
    JumpIf { cond: Id, then: Id },
}

impl ProcCfg {
    fn block(&self, block_id: CfgId) -> BasicBlockRef<'_> {
        BasicBlockRef { proc: self, data: &self.blocks[block_id.index()] }
    }

    fn label(&self, block_id: CfgId) -> Option<Id> {
        self.blocks[block_id.index()].label
    }

    fn fallthrough(&self, block_id: CfgId) -> Option<CfgId> {
        assert!(block_id != self.exit());
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

    fn is_exit_block(&self, block_id: CfgId) -> bool {
        if block_id == self.exit() {
            return false;
        }
        match self.block(block_id).data.cont {
            Cont::Stop(_) | Cont::Ret(_) => true,
            Cont::Jump(target, _) => !self.labeled_blocks.contains_key(&target),
            Cont::JumpIf { .. } => false,
        }
    }

    fn postorder(&self) -> IndexedProcPostorder {
        IndexedProcPostorder { block_count: self.blocks.len() }
    }

    fn blocks_rpo(&self) -> impl Iterator<Item = CfgId> {
        self.postorder().iter().skip(1).rev()
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
        assert!(index <= self.block_count);
        if index == self.block_count {
            0
        } else {
            index + 1
        }
    }

    fn node_at(&self, position: usize) -> CfgId {
        assert!(position <= self.block_count);
        if position == 0 {
            CfgId::new(self.block_count)
        } else {
            CfgId::new(position - 1)
        }
    }

    #[allow(refining_impl_trait)]
    fn iter(&self) -> impl DoubleEndedIterator<Item = CfgId> + ExactSizeIterator + use<> {
        exact_size_chain(
            [CfgId::new(self.block_count)],
            (0..self.block_count).map(CfgId::new),
        )
    }
}

fn normalize_tail(block: core::Block, stop: Option<usize>, ids: &mut IdGen) -> (Vec<(Option<Id>, core::Expr)>, core::TailExpr) {
    use core::{Block, Expr, TailExpr};

    let Block { mut priors, mut tail } = block;
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
        else { unreachable!() };

        let cont_label = self.cont_label;

        let join_label = Some(ids.generate());
        self.cont_label = join_label;

        let tail = replace(&mut self.tail, TailExpr::IfThenElse(cond, then_else));

        Some((split, BasicBlockCandidate {
            label: join_label,
            input: split_output,
            segment: self.segment,
            start: split + 1,
            tail,
            cont_label,
        }))
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
        }}
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
        }}
    }

    queue.push_front(QueueItem::Unvisited(build_candidate!(proc_body)));

    while queue.front().is_some_and(|item| !matches!(item, QueueItem::Finished(_))) {
        match queue.pop_front().unwrap() {
            QueueItem::Finished(_) => unreachable!(),

            QueueItem::Discovered(basic_block) => {
                queue.push_back(QueueItem::Finished(basic_block));
            }

            QueueItem::Unvisited(mut candidate) => {
                let (end, join) = candidate.split_at_control(&mut segments, ids).unzip();

                let end = end.unwrap_or_else(|| segments[candidate.segment].len());

                if let Some(join) = &join && join.label.is_some() {
                    label_count += 1;
                }

                let BasicBlockCandidate { label, input, segment, start, tail, cont_label } = candidate;

                match tail {
                    TailExpr::Unit | TailExpr::Var(_) | TailExpr::Apply(_, _) => {
                        let cont = match tail {
                            TailExpr::Unit | TailExpr::Var(_) => {
                                let res = if let TailExpr::Var(x) = tail { Some(x) } else { None };
                                cont_label.map_or(
                                    if stop.is_some() {
                                        Cont::Stop(res)
                                    } else {
                                        Cont::Ret(res)
                                    },
                                    |cont| Cont::Jump(cont, res.into_iter().map(Val::Var).collect()),
                                )
                            }

                            TailExpr::Apply(target, args) => {
                                assert!(cont_label.is_none());
                                Cont::Jump(target, args)
                            }

                            TailExpr::IfThenElse(..) => unreachable!(),
                        };
                        queue.push_back(QueueItem::Finished(BasicBlock { label, input, segment, start, end, cont }))
                    }

                    TailExpr::IfThenElse(cond, then_else) => {
                        let [then_block, else_block] = *then_else;
                        let then_label = generate_label!();

                        queue.push_front(QueueItem::Discovered(BasicBlock {
                            label, input, segment, start, end,
                            cont: Cont::JumpIf { cond, then: then_label },
                        }));

                        queue.push_front(QueueItem::Unvisited(BasicBlockCandidate {
                            cont_label,
                            .. build_candidate!(else_block)
                        }));

                        queue.push_front(QueueItem::Unvisited(BasicBlockCandidate {
                            label: Some(then_label),
                            cont_label,
                            .. build_candidate!(then_block)
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
    let blocks: Vec<_> = Vec::from(queue).into_iter().enumerate().map(|(i, item)| {
        let QueueItem::Finished(b) = item else { unreachable!() };
        if let Some(label) = b.label {
            labeled_blocks.insert(label, i);
        }
        b
    }).collect();

    ProcCfg {
        segments: segments.into_boxed_slice(),
        blocks: blocks.into_boxed_slice(),
        labeled_blocks,
    }
}

impl Graph for ProcCfg {
    type Node = CfgId;

    fn node_count(&self) -> usize {
        self.blocks.len() + 1
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

impl ExitNode for ProcCfg {
    fn exit(&self) -> CfgId {
        CfgId::new(self.blocks.len())
    }
}

impl Successors for ProcCfg {
    #[allow(refining_impl_trait)]
    fn successors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        exact_size_chain(
            iter_some((node != self.exit()).then(|| self.successor_blocks(node))),
            self.is_exit_block(node).then_some(self.exit()),
        )
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

    fn instructions(&self, b: Self::BlockId) -> impl DoubleEndedIterator<Item = (InstrIdx, Id, DefUse)> {
        use core::*;

        fn instrs<'a>(idx: InstrIdx, def_use: DefUse, vals: &'a [Val], ids: &'a [Id])
            -> impl DoubleEndedIterator<Item = (InstrIdx, Id, DefUse)> + use<'a>
        { 
            chain(
                vals.iter().filter_map(|val| match val {
                    Val::Var(id) => Some(id),
                    Val::Const(_) => None,
                }),
                ids,
            ).map(move |&id| (idx, id, def_use))
        }

        let (priors, input_defs, cont_vals, cont_ids): (&[_], _, &[Val], &[Id]) = if b == self.exit() {
            (&[], None, &[], &[])
        } else {
            let block = self.block(b);
            let input_defs = block.data.input.map(|id| (InstrIdx::Input, id, DefUse::Def));
            let (cont_vals, cont_ids): (&[Val], &[Id]) = match &block.data.cont {
                Cont::Stop(x) | Cont::Ret(x) => (&[], x.as_slice()),
                Cont::Jump(_, args) => (args, &[]),
                Cont::JumpIf { cond, .. } => (&[], slice::from_ref(cond)),
            };
            (block.priors(), input_defs, cont_vals, cont_ids)
        };

        let prior_def_uses = priors.iter().enumerate().flat_map(|(i, (def, expr))| {
            let def_iter = def.map(|id| (InstrIdx::Prior(i), id, DefUse::Def));
            let (vals, ids): (&[Val], &[Id]) = match expr {
                Expr::Unit => (&[], &[]),
                Expr::Val(val) => (slice::from_ref(val), &[]),
                Expr::Op(_, args) => (args, &[]),
                Expr::Apply(_, args) => (args, &[]),
                Expr::IfThenElse(id, _) => (&[], slice::from_ref(id)),
            };
            let uses_iter = instrs(InstrIdx::Prior(i), DefUse::Use, vals, ids);
            chain(def_iter, uses_iter)
        });

        let cont_uses = instrs(InstrIdx::Cont, DefUse::Use, cont_vals, cont_ids);

        chain(input_defs, prior_def_uses).chain(cont_uses)
    }
}

#[cfg(test)]
mod tests {
    use revm::primitives::U256;

    use super::*;
    use crate::id::{IdGen, generate_ids};
    use crate::{asm::Instr::*, core::{self, Block, Expr::*, TailExpr, Val::*}, graph::Successors};

    fn program(main: Block, rets: usize) -> core::Program {
        core::Program { main, rets, procs: vec![] }
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
        assert_eq!(entry_successors.len(), 1);
        let [exit] = entry_successors[..] else { panic!() };
        assert_eq!(exit, indexed.exit());
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
        let [branch0, branch1] = entry_successors[..] else { panic!() };

        let branch0_successors: Vec<_> = indexed.successors(branch0).collect();
        let branch1_successors: Vec<_> = indexed.successors(branch1).collect();

        assert_eq!(branch0_successors, branch1_successors);
        assert_eq!(branch0_successors.len(), 1);
        let [exit] = branch0_successors[..] else { panic!() };

        assert_eq!(exit, indexed.exit());
    }

    #[test]
    fn test_index_if_then_else_prior() {
        let mut ids = IdGen::new();
        generate_ids! { x, y in ids };
        generate_ids! { t, f in ids };
        let block = Block {
            priors: vec![
                (Some(x), Val(Const(U256::from(1)))),
                (Some(y), IfThenElse(
                    x,
                    Box::new([
                        Block { priors: vec![(Some(t), Val(Const(U256::from(1))))], tail: TailExpr::Var(t) },
                        Block { priors: vec![(Some(f), Val(Const(U256::from(0))))], tail: TailExpr::Var(f) },
                    ]),
                )),
            ],
            tail: TailExpr::Var(y),
        };

        let indexed = build_cfg(block, Some(1), &mut ids);
        assert_eq!(indexed.blocks.len(), 4);

        let entry = indexed.entry();

        let entry_successors: Vec<_> = indexed.successors(entry).collect();
        assert_eq!(entry_successors.len(), 2);
        let [branch0, branch1] = entry_successors[..] else { panic!() };

        let branch0_successors: Vec<_> = indexed.successors(branch0).collect();
        let branch1_successors: Vec<_> = indexed.successors(branch1).collect();
        assert_eq!(branch0_successors, branch1_successors);
        assert_eq!(branch0_successors.len(), 1);
        let [tail] = branch0_successors[..] else { panic!() };

        let tail_successors: Vec<_> = indexed.successors(tail).collect();
        assert_eq!(tail_successors.len(), 1);
        let [exit] = tail_successors[..] else { panic!() };

        assert_eq!(exit, indexed.exit());
    }

    #[test]
    fn test_compile_if_then_else_tail() {
        let mut ids = IdGen::new();
        generate_ids! { x, t, f in ids };
        let block = Block {
            priors: vec![
                (Some(x), Val(Const(U256::from(2)))),
            ],
            tail: TailExpr::IfThenElse(
                x,
                Box::new([
                    Block { priors: vec![(Some(t), Val(Const(U256::from(1))))], tail: TailExpr::Var(t) },
                    Block { priors: vec![(Some(f), Val(Const(U256::from(0))))], tail: TailExpr::Var(f) },
                ]),
            ),
        };
        let code = compile(program(block, 1), &mut ids.clone());
        generate_ids! { label in ids };
        assert_eq!(code, vec![
            Push(U256::from(2)),
            PushLabel(label),
            JumpIf,
            Push(U256::from(0)),
            Stop,
            JumpDest(label),
            Push(U256::from(1)),
            Stop,
        ]);
    }

    #[test]
    fn test_compile_if_then_else_prior() {
        let mut ids = IdGen::new();
        generate_ids! { x, y, t, f in ids };
        let block = Block {
            priors: vec![
                (Some(x), Val(Const(U256::from(2)))),
                (Some(y), IfThenElse(
                    x,
                    Box::new([
                        Block { priors: vec![(Some(t), Val(Const(U256::from(1))))], tail: TailExpr::Var(t) },
                        Block { priors: vec![(Some(f), Val(Const(U256::from(0))))], tail: TailExpr::Var(f) },
                    ]),
                )),
            ],
            tail: TailExpr::Var(y),
        };
        let code = compile(program(block, 1), &mut ids.clone());
        generate_ids! { label1, label2 in ids };
        assert_eq!(code, vec![
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
        ]);
    }

    #[test]
    fn test_compile_if_nested() {
        let mut ids = IdGen::new();
        generate_ids! { x, y, a, b, c in ids };
        let block = Block {
            priors: vec![
                (Some(x), Val(Const(U256::from(1)))),
                (Some(y), Val(Const(U256::from(0)))),
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
                                    priors: vec![(Some(a), Val(Const(U256::from(1))))],
                                    tail: TailExpr::Var(a),
                                },
                                Block {
                                    priors: vec![(Some(b), Val(Const(U256::from(2))))],
                                    tail: TailExpr::Var(b),
                                },
                            ]),
                        ),
                    },
                    Block {
                        priors: vec![(Some(c), Val(Const(U256::from(3))))],
                        tail: TailExpr::Var(c),
                    },
                ]),
            ),
        };
        let code = compile(program(block, 1), &mut ids.clone());
        generate_ids! { label1, label2 in ids };
        assert_eq!(code, vec![
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
        ]);
    }
}
