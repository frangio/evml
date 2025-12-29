use std::collections::{HashMap, VecDeque, hash_map};
use std::iter::{chain, repeat_n, zip};
use std::mem::{take};
use std::num::NonZero;
use std::ops::Range;
use std::slice;

use crate::utils::exact_size_chain;
use crate::{Id, IdGen, asm, core, opcodes};
use crate::analysis::{self, Cfg, DefUse, Procedure, ipdom, liveness};
use crate::graph::{EntryNode, ExitNode, Graph, Idx, IdxNodeOrdering, NodeOrdering, Successors};

fn size_of(expr: &core::Expr) -> usize {
    use core::*;
    match expr {
        Expr::Val(_) => 1,
        Expr::Op(op, _) => opcodes::info(*op).unwrap().outputs,
        Expr::IfThenElse(_, then_else) => size_of(&then_else[0].tail),
    }
}

#[derive(Clone)]
struct Stack(Vec<Option<Id>>);
struct StackEntry<'a> {
    stack: &'a mut Stack,
    index: usize,
}

impl Stack {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn popn(&mut self, count: usize) {
        self.0.truncate(self.0.len() - count);
    }

    fn push(&mut self, x: Option<Id>) {
        self.0.push(x);
    }

    fn swap(&mut self, depth: usize) {
        let top = self.0.len() - 1;
        let index = top - depth;
        self.0.swap(index, top);
    }

    fn read(&self, depth: usize) -> Id {
        let top = self.0.len() - 1;
        let index = top - depth;
        self.0[index].unwrap()
    }

    fn entry(&mut self, x: Id) -> StackEntry<'_> {
        let index = self.0.iter()
            .rposition(|y| y.as_ref().is_some_and(|&y| y == x))
            .expect("unknown variable");
        StackEntry { stack: self, index }
    }

    fn find_depth(&self, depths: Range<usize>, pred: impl Fn(Option<Id>) -> bool) -> Option<usize> {
        let top = self.0.len() - 1;
        let [start_index, end_index] = [depths.end, depths.start].map(|d| top - d);
        self.0[start_index..end_index].iter()
            .copied()
            .rposition(pred)
            .map(|i| top - (start_index + i))
    }
}

impl StackEntry<'_> {
    fn var(&self) -> Id {
        self.stack.0[self.index].expect("stack item is temporary")
    }

    fn depth(&self) -> usize {
        self.stack.0.len() - 1 - self.index
    }

    fn swap(&mut self) {
        let top = self.stack.0.len() - 1;
        self.stack.0.swap(self.index, top);
    }
}

pub fn compile(block: core::Block, ids: &mut IdGen) -> Vec<asm::Instr> {
    let proc = index(block, ids);
    let analysis = analyze(&proc);

    let mut stacks = HashMap::new();
    stacks.insert(proc.entry(), Stack::new());

    let mut code = vec![];

    for block_id in proc.postorder().iter().skip(1).rev() {
        let block = proc.block(block_id);
        if let Some(label) = block.data.label {
            code.push(asm::Instr::JumpDest(label));
        }
        let hash_map::Entry::Occupied(mut stack_entry) = stacks.entry(block_id) else { panic!() };
        let stack = stack_entry.get_mut();
        let liveness = &analysis.liveness[block_id.index()];
        for (i, prior) in block.priors().iter().enumerate() {
            let is_last_use = |x| liveness.last_use(x) == Some(InstrIdx::Prior(i));
            compile_prior(prior, stack, is_last_use, &mut code);
        }

        let ipdom = proc.ipdom[block_id.index()];
        let ipdom_liveness = &analysis.liveness[ipdom.index()];

        let live_out = |x| liveness.last_use(x).is_none_or(|i| i == InstrIdx::Cont);

        compile_cont(block.data.cont, stack, live_out, ipdom_liveness, &mut code);

        let (_, stack) = stack_entry.remove_entry();
        let succs = proc.successors(block_id);
        let stack = repeat_n(stack, succs.len());
        for (succ, stack) in zip(succs, stack) {
            let prev_stack = stacks.insert(succ, stack);
            assert!(prev_stack.is_none());
        }
    }

    code
}

fn compile_prior(
    prior: &core::BlockPrior,
    stack: &mut Stack,
    is_last_use: impl Fn(Id) -> bool,
    code: &mut Vec<asm::Instr>,
) {
    let core::BlockPrior::Let(x, e) = prior;
    compile_expr_onto(e, stack, is_last_use, code);
    if let &Some(x) = x {
        stack.push(Some(x));
    }
}

fn compile_cont(
    cont: Cont,
    stack: &mut Stack,
    live_out: impl Fn(Id) -> bool,
    ipdom_liveness: &BlockLiveness,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;

    let stash_start = stack.len() - 1 - ipdom_liveness.live_in_size();
    let mut next_avail = stash_start;
    let mut popped = 0;

    for d in 0..stash_start {
        let d = d - popped;
        let x = stack.read(d);
        if !live_out(x) {
            if d > 0 {
                code.push(Instr::Swap(d));
                stack.swap(d);
            }
            code.push(Instr::Pop);
            stack.popn(1);
            popped += 1;
            next_avail -= 1;
        } else if ipdom_liveness.live_in(x) {
            let e = (next_avail..stack.len()).find(|&e| {
                let y = stack.read(e);
                !ipdom_liveness.live_in(y)
            }).unwrap();
            next_avail = e + 1;
            if d > 0 {
                code.push(Instr::Swap(d));
                stack.swap(d);
            }
            code.push(Instr::Swap(e));
            stack.swap(e);
        }
    }

    if let Cont::Stop(res) | Cont::Jump(_, res) = cont {
        assert!(res.is_none() || Some(&res) == stack.0.last());
        let res_size = res.map_or(0, |_| 1);
        let stack_size = stack.len();
        if stack_size > res_size {
            let excess = stack_size - res_size;
            code.extend(repeat_n([Instr::Swap(excess), Instr::Pop], res_size).flatten());
            if excess > res_size {
                code.extend(repeat_n(Instr::Pop, excess - res_size));
            }
        }
    }

    match cont {
        Cont::Stop(_) => {
            code.push(Instr::Stop);
        }

        Cont::Jump(target, _) => {
            code.push(Instr::PushLabel(target));
            code.push(Instr::Jump);
        }

        Cont::JumpIf { cond, then } => {
            compile_val_onto(&Val::Var(cond), stack, |e| !live_out(e.var()), code);
            code.push(Instr::PushLabel(then));
            code.push(Instr::JumpIf);
        }
    }
}

fn compile_expr_onto(
    expr: &core::Expr,
    stack: &mut Stack,
    is_last_use: impl Fn(Id) -> bool,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;
    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, stack, |e| is_last_use(e.var()), code);
        }

        Expr::Op(op, args) => {
            let should_swap  = |x, i| {
                is_last_use(x) && !args[..i].contains(&Val::Var(x))
            };

            let stack_delta = args.iter().enumerate().filter(|&(i, v)| {
                match v {
                    Val::Const(_) => true,
                    Val::Var(x) => !should_swap(*x, i),
                }
            }).count();

            let target_stack_len = stack.len() + stack_delta;

            for (i, v) in args.iter().enumerate().rev() {
                let should_swap = |e: &StackEntry| should_swap(e.var(), i);
                compile_val_onto(v, stack, should_swap, code);
                stack.push(None);
                let rem_delta = target_stack_len - stack.len();
                let offset = i - rem_delta;
                if offset > 0 {
                    code.push(Instr::Swap(offset));
                    stack.swap(offset);
                }
            }

            code.push(Instr::Op(*op));
            stack.popn(args.len());
        }

        Expr::IfThenElse(..) => panic!(),
    }
}

fn compile_val_onto(
    val: &core::Val,
    stack: &mut Stack,
    should_swap: impl Fn(&StackEntry) -> bool,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;
    match val {
        Val::Const(c) => {
            code.push(Instr::Push(*c));
        }

        Val::Var(x) => {
            let mut entry = stack.entry(*x);
            let depth = entry.depth();
            if should_swap(&entry) {
                if depth > 0 {
                    code.push(Instr::Swap(depth));
                    entry.swap();
                }
                stack.popn(1);
            } else {
                code.push(Instr::Dup(depth));
            }
        }
    }
}

type Liveness = analysis::Liveness<IndexedProc>;
type BlockLiveness = analysis::BlockLiveness<IndexedProc>;

struct Analysis {
    liveness: Liveness,
}

fn analyze(proc: &IndexedProc) -> Analysis {
    let liveness = liveness(proc, &proc.postorder());
    Analysis { liveness }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct BlockId(NonZero<usize>);

impl Idx for BlockId {
    fn new(index: usize) -> Self {
        BlockId(NonZero::new(index + 1).unwrap())
    }

    fn index(self) -> usize {
        self.0.get() - 1
    }
}

struct IndexedProc {
    blocks: Box<[IndexedBlock]>,
    segments: Box<[Box<[core::BlockPrior]>]>,
    labels: HashMap<Id, BlockId>,
    ipdom: Box<[BlockId]>,
}

#[derive(PartialEq, Eq, Debug)]
struct IndexedBlock {
    label: Option<Id>,
    input: Option<Id>,
    segment: usize,
    start: usize,
    end: usize,
    cont: Cont,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Cont {
    Stop(Option<Id>),
    Jump(Id, Option<Id>),
    JumpIf { cond: Id, then: Id },
}

struct IndexedBlockRef<'a> {
    proc: &'a IndexedProc,
    data: &'a IndexedBlock,
}

impl IndexedProc {
    fn block(&self, block_id: BlockId) -> IndexedBlockRef<'_> {
        IndexedBlockRef { proc: self, data: &self.blocks[block_id.0.get() - 2] }
    }

    fn fallthrough(&self, block_id: BlockId) -> BlockId {
        let po = self.postorder();
        po.node_at(po.position(block_id) - 1)
    }

    fn postorder(&self) -> IdxNodeOrdering<BlockId> {
        IdxNodeOrdering::new(self.blocks.len() + 1)
    }
}

impl<'a> IndexedBlockRef<'a> {
    fn priors(&self) -> &'a [core::BlockPrior] {
        &self.proc.segments[self.data.segment][self.data.start..self.data.end]
    }
}

enum TailExpr {
    Return(Option<Id>),
    IfThenElse(Id, Box<[core::Block; 2]>),
}

fn normalize_tail(block: core::Block, ids: &mut IdGen) -> (Vec<core::BlockPrior>, TailExpr) {
    use core::*;
    let Block { mut priors, tail } = block;
    let tail = match tail {
        Expr::Val(Val::Var(x)) => {
            TailExpr::Return(Some(x))
        }

        expr @ Expr::Op(..) if size_of(&expr) == 0 => {
            priors.push(BlockPrior::Let(None, expr));
            TailExpr::Return(None)
        }

        expr @ (Expr::Op(..) | Expr::Val(_)) => {
            let x = ids.generate();
            priors.push(BlockPrior::Let(Some(x), expr));
            TailExpr::Return(Some(x))
        }

        Expr::IfThenElse(cond, then_else) => {
            let Val::Var(cond) = cond else { todo!() };
            TailExpr::IfThenElse(cond, then_else)
        }
    };
    (priors, tail)
}

fn index(block: core::Block, ids: &mut IdGen) -> IndexedProc {
    use core::*;

    enum QueueItem {
        Finished(IndexedBlock),
        Discovered(IndexedBlock),
        Unvisited(UnvisitedBlock),
    }

    struct UnvisitedBlock {
        label: Option<Id>,
        input: Option<Id>,
        segment: usize,
        start: usize,
        tail: TailExpr,
        cont_label: Option<Id>,
    }

    let mut labeled_blocks = 0;

    macro_rules! generate_label {
        () => {{
            labeled_blocks += 1;
            ids.generate()
        }}
    }

    let mut segments = vec![];
    let mut queue = VecDeque::new();

    macro_rules! unvisited_block {
        ($block:expr) => {{
            let (priors, tail) = normalize_tail($block, ids);
            let segment = segments.len();
            segments.push(priors.into_boxed_slice());
            UnvisitedBlock {
                segment,
                tail,
                start: 0,
                label: None,
                input: None,
                cont_label: None,
            }
        }}
    }

    queue.push_front(QueueItem::Unvisited(unvisited_block!(block)));

    while queue.front().is_some_and(|item| !matches!(item, QueueItem::Finished(_))) {
        match queue.pop_front().unwrap() {
            QueueItem::Finished(_) => unreachable!(),

            QueueItem::Discovered(indexed_block) => {
                queue.push_back(QueueItem::Finished(indexed_block));
            }

            QueueItem::Unvisited(unvisited_block) => {
                let UnvisitedBlock { label, input, segment, start, tail, cont_label } = unvisited_block;

                let split = segments[segment].iter_mut().enumerate().skip(start).find_map(|(i, p)| {
                    matches!(p, BlockPrior::Let(_, Expr::IfThenElse(..))).then_some(i)
                });

                let (tail, cont_label, join) = match split {
                    None => (tail, cont_label, None),
                    Some(split) => {
                        let BlockPrior::Let(res, Expr::IfThenElse(cond, then_else)) =
                            take(&mut segments[segment][split])
                        else { unreachable!() };

                        let Val::Var(cond) = cond else { todo!() };

                        let join = UnvisitedBlock {
                            label: Some(generate_label!()),
                            input: res,
                            segment,
                            start: split + 1,
                            tail,
                            cont_label,
                        };

                        (TailExpr::IfThenElse(cond, then_else), join.label, Some(join))
                    }
                };

                match tail {
                    TailExpr::Return(res) => {
                        queue.push_back(QueueItem::Finished(IndexedBlock {
                            label,
                            input,
                            segment,
                            start,
                            end: segments[segment].len(),
                            cont: cont_label.map_or(Cont::Stop(res), |cont| Cont::Jump(cont, res)),
                        }))
                    }

                    TailExpr::IfThenElse(cond, then_else) => {
                        let [then_block, else_block] = *then_else;
                        let then_label = generate_label!();

                        queue.push_front(QueueItem::Discovered(IndexedBlock {
                            label,
                            input,
                            segment,
                            start,
                            end: split.unwrap_or(segments[segment].len()),
                            cont: Cont::JumpIf { cond, then: then_label },
                        }));

                        queue.push_front(QueueItem::Unvisited(UnvisitedBlock {
                            cont_label,
                            .. unvisited_block!(else_block)
                        }));

                        queue.push_front(QueueItem::Unvisited(UnvisitedBlock {
                            label: Some(then_label),
                            cont_label,
                            .. unvisited_block!(then_block)
                        }));
                    }
                }

                if let Some(join) = join {
                    queue.push_front(QueueItem::Unvisited(join));
                }
            }
        }
    }

    let mut labels = HashMap::<Id, BlockId>::with_capacity(labeled_blocks);

    // Blocks are now in postorder
    let blocks: Vec<_> = Vec::from(queue).into_iter().enumerate().map(|(i, item)| {
        let QueueItem::Finished(b) = item else { unreachable!() };
        if let Some(label) = b.label {
            labels.insert(label, BlockId(NonZero::new(i + 2).unwrap()));
        }
        b
    }).collect();

    let mut proc = IndexedProc {
        segments: segments.into_boxed_slice(),
        blocks: blocks.into_boxed_slice(),
        labels,
        ipdom: Box::default(),
    };

    proc.ipdom = ipdom(&proc);
    proc
}

impl Graph for IndexedProc {
    type Node = BlockId;

    fn node_count(&self) -> usize {
        self.blocks.len() + 1
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        self.postorder().iter()
    }
}

impl EntryNode for IndexedProc {
    fn entry(&self) -> BlockId {
        BlockId(NonZero::new(self.blocks.len() + 1).unwrap())
    }
}

impl ExitNode for IndexedProc {
    fn exit(&self) -> BlockId {
        BlockId(NonZero::new(1).unwrap())
    }
}

impl Successors for IndexedProc {
    #[allow(refining_impl_trait)]
    fn successors(&self, node: Self::Node) -> impl ExactSizeIterator<Item = Self::Node> {
        let (target, fallthrough) = if node == self.exit() {
            (None, None)
        } else {
            match &self.block(node).data.cont {
                Cont::Stop(_) => (Some(self.exit()), None),
                Cont::Jump(target, _) => (Some(self.labels[target]), None),
                Cont::JumpIf { then, .. } => (Some(self.labels[then]), Some(self.fallthrough(node))),
            }
        };
        exact_size_chain(target, fallthrough)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InstrIdx {
    Input,
    Prior(usize),
    Cont,
}

impl Procedure for IndexedProc {
    type BlockId = BlockId;
    type VarId = Id;
    type InstrIdx = InstrIdx;

    fn cfg(&self) -> impl Cfg<Node = Self::BlockId> {
        self
    }

    fn instructions(&self, b: Self::BlockId) -> impl DoubleEndedIterator<Item = (Self::InstrIdx, Self::VarId, DefUse)> {
        use core::*;

        let (priors, input_def, cont_use) = if b == self.exit() {
            ([].as_slice(), None, None)
        } else {
            let block = self.block(b);
            let priors = block.priors();
            let input_def = block.data.input.map(|id| (InstrIdx::Input, id, DefUse::Def));
            let cont_use = match &block.data.cont {
                Cont::Stop(x) | Cont::Jump(_, x) => *x,
                Cont::JumpIf { cond, .. } => Some(*cond),
            }.map(|id| (InstrIdx::Cont, id, DefUse::Use));
            (priors, input_def, cont_use)
        };

        let prior_def_uses = priors.iter().enumerate().flat_map(|(i, prior)| {
            let BlockPrior::Let(def, expr) = prior;
            let vals: &[Val] = match expr {
                Expr::Val(val) => slice::from_ref(val),
                Expr::Op(_, args) => args,
                Expr::IfThenElse(val, _) => slice::from_ref(val),
            };
            let def_iter = def.map(|id| (InstrIdx::Prior(i), id, DefUse::Def));
            let uses_iter = vals.iter().filter_map(move |val| match val {
                Val::Var(id) => Some((InstrIdx::Prior(i), *id, DefUse::Use)),
                Val::Const(_) => None,
            });
            chain(def_iter, uses_iter)
        });

        chain(input_def, prior_def_uses).chain(cont_use)
    }
}

#[cfg(test)]
mod tests {
    use revm::primitives::U256;

    use super::*;
    use crate::{IdGen, generate_ids, asm::Instr::*, core::{Block, BlockPrior::*, Expr::*, Val::*}, graph::Successors};

    #[test]
    fn test_index_trivial() {
        let mut ids = IdGen::new();
        generate_ids!(ids => x);
        let block = Block {
            priors: vec![],
            tail: Val(Var(x)),
        };
        let indexed = index(block, &mut ids);
        assert_eq!(indexed.blocks.len(), 1);

        let entry_successors: Vec<_> = indexed.successors(indexed.entry()).collect();
        assert_eq!(entry_successors.len(), 1);
        let [exit] = entry_successors[..] else { panic!() };
        assert_eq!(exit, indexed.exit());
    }

    #[test]
    fn test_index_if_then_else_tail() {
        let mut ids = IdGen::new();
        generate_ids!(ids => x, y, z);
        let block = Block {
            priors: vec![],
            tail: IfThenElse(
                Var(x),
                Box::new([
                    Block {
                        priors: vec![],
                        tail: Val(Var(y)),
                    },
                    Block {
                        priors: vec![],
                        tail: Val(Var(z)),
                    },
                ]),
            ),
        };
        let indexed = index(block, &mut ids);
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
        generate_ids!(ids => x, y);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(1)))),
                Let(Some(y), IfThenElse(
                    Var(x),
                    Box::new([
                        Block { priors: vec![], tail: Val(Const(U256::from(1))) },
                        Block { priors: vec![], tail: Val(Const(U256::from(0))) },
                    ]),
                )),
            ],
            tail: Val(Var(y)),
        };

        let indexed = index(block, &mut ids);
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
    #[ignore]
    fn test_compile_if_then_else_tail() {
        let mut ids = IdGen::new();
        generate_ids!(ids => x);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(2)))),
            ],
            tail: IfThenElse(
                Var(x),
                Box::new([
                    Block { priors: vec![], tail: Val(Const(U256::from(1))) },
                    Block { priors: vec![], tail: Val(Const(U256::from(0))) },
                ]),
            ),
        };
        let code = compile(block, &mut ids);
        generate_ids!(ids => label);
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
    #[ignore]
    fn test_compile_if_then_else_prior() {
        let mut ids = IdGen::new();
        generate_ids!(ids => x, y);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(1)))),
                Let(Some(y), IfThenElse(
                    Var(x),
                    Box::new([
                        Block { priors: vec![], tail: Val(Const(U256::from(1))) },
                        Block { priors: vec![], tail: Val(Const(U256::from(0))) },
                    ]),
                )),
            ],
            tail: Val(Var(y)),
        };
        let code = compile(block, &mut ids);
        generate_ids!(ids => label1, label2);
        assert_eq!(code, vec![
            Push(U256::from(1)),
            PushLabel(label1),
            Swap(1),
            JumpIf,
            Push(U256::from(0)),
            PushLabel(label2),
            Jump,
            JumpDest(label1),
            Push(U256::from(1)),
            JumpDest(label2),
            Stop,
        ]);
    }
}
