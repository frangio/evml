use std::collections::{HashMap, VecDeque, hash_map};
use std::iter::{chain, repeat_n, zip};
use std::mem::{take};
use std::num::NonZero;
use std::slice;
use crate::utils::exact_size_chain;
use crate::utils::exact_size_iter::iter_some;
use crate::{asm, core};
use crate::id::{Id, IdGen};
use crate::analysis::{self, Cfg, DefUse, Procedure, ipdom, liveness};
use crate::graph::{EntryNode, ExitNode, Graph, Idx, NodeOrdering, Successors};

#[derive(Debug, Clone, PartialEq, Eq)]
struct Stack(Vec<Option<Id>>);
struct StackEntry<'a> {
    stack: &'a mut Stack,
    index: usize,
}

impl Stack {
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
}

impl Default for Stack {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl FromIterator<Id> for Stack {
    fn from_iter<T: IntoIterator<Item = Id>>(iter: T) -> Self {
        Stack(iter.into_iter().map(Some).collect())
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

pub fn compile(program: core::Program, ids: &mut IdGen) -> Vec<asm::Instr> {
    let mut code = vec![];

    compile_proc(program.main, &[], Some(program.rets), ids, &mut code);

    for (label, proc) in program.procs {
        code.push(asm::Instr::JumpDest(label));
        compile_proc(proc.body, &proc.args, None, ids, &mut code);
    }

    code
}

fn compile_proc(body: core::Block, args: &[Id], stop: Option<usize>, ids: &mut IdGen, code: &mut Vec<asm::Instr>) {
    let proc = index(body, stop, ids);
    let analysis = analyze(&proc);

    let mut stacks = HashMap::<_, Stack>::new();
    stacks.insert(proc.entry(), args.iter().copied().collect());

    for block_id in proc.postorder().iter().skip(1).rev() {
        let block = proc.block(block_id);
        if let Some(label) = block.data.label {
            code.push(asm::Instr::JumpDest(label));
        }
        let hash_map::Entry::Occupied(mut stack_entry) = stacks.entry(block_id) else { panic!() };
        let stack = stack_entry.get_mut();
        if let Some(input) = block.data.input {
            stack.push(Some(input));
        }
        let liveness = &analysis.liveness[block_id.index()];
        for (i, prior) in block.priors().iter().enumerate() {
            let is_last_use = |x| liveness.last_use(x) == InstrIdx::Prior(i);
            compile_prior(prior, stack, is_last_use, ids, code);
        }

        let ipdom = proc.ipdom[block_id.index()];
        let ipdom_liveness = &analysis.liveness[ipdom.index()];

        compile_cont(
            &block.data.cont,
            stack,
            liveness,
            ipdom_liveness,
            proc.fallthrough(block_id).and_then(|i| proc.blocks[i.index()].label),
            code,
        );

        let (_, stack) = stack_entry.remove_entry();
        let succs = proc.successor_blocks(block_id);
        let stack = repeat_n(stack, succs.len());
        for (succ, stack) in zip(succs, stack) {
            let prev_stack = stacks.insert(succ, stack);
            if let Some(prev_stack) = prev_stack {
                debug_assert_eq!(prev_stack, stacks[&succ]);
            }
        }
    }
}

fn compile_prior(
    prior: &core::BlockPrior,
    stack: &mut Stack,
    is_last_use: impl Fn(Id) -> bool,
    ids: &mut IdGen,
    code: &mut Vec<asm::Instr>,
) {
    let core::BlockPrior::Let(x, e) = prior;
    compile_expr_onto(e, stack, is_last_use, ids, code);
    if let &Some(x) = x {
        stack.push(Some(x));
    }
}

fn compile_cont(
    cont: &Cont,
    stack: &mut Stack,
    liveness: &BlockLiveness,
    ipdom_liveness: &BlockLiveness,
    fallthrough_target: Option<Id>,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;

    let stash_start = stack.len() - ipdom_liveness.live_in_size();
    let mut next_avail = stash_start;
    let mut popped = 0;

    for d in 0..stash_start {
        let d = d - popped;
        let x = stack.read(d);
        if liveness.last_use(x) < InstrIdx::Cont {
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

    let should_swap = |x: Id| liveness.last_use(x) == InstrIdx::Cont;

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

            if Some(target) != fallthrough_target {
                code.push(Instr::PushLabel(target));
                code.push(Instr::Jump);
            }
        }

        Cont::JumpIf { cond, then } => {
            compile_val_onto(&Val::Var(cond), stack, |e: &StackEntry| should_swap(e.var()), code);
            code.push(Instr::PushLabel(then));
            code.push(Instr::JumpIf);
        }
    }
}

fn compile_expr_onto(
    expr: &core::Expr,
    stack: &mut Stack,
    is_last_use: impl Fn(Id) -> bool,
    ids: &mut IdGen,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;
    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, stack, |e| is_last_use(e.var()), code);
        }

        Expr::Op(op, args) => {
            compile_args_onto(args, None, stack, &is_last_use, code);
            code.push(Instr::Op(*op));
            stack.popn(args.len());
        }

        Expr::Apply(target, args) => {
            let ret = ids.generate();
            compile_args_onto(args, Some(ret), stack, &is_last_use, code);
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
    stack: &mut Stack,
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

type BlockLiveness = analysis::BlockLiveness<IndexedProc>;

struct Analysis {
    liveness: Box<[BlockLiveness]>,
}

fn analyze(proc: &IndexedProc) -> Analysis {
    let liveness = liveness(proc, &proc.postorder());
    Analysis { liveness }
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

struct IndexedProc {
    blocks: Box<[IndexedBlock]>,
    segments: Box<[Box<[core::BlockPrior]>]>,
    labeled_blocks: HashMap<Id, usize>,
    ipdom: Box<[CfgId]>,
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

#[derive(PartialEq, Eq, Debug)]
enum Cont {
    Ret(Option<Id>),
    Stop(Option<Id>),
    Jump(Id, Vec<core::Val>),
    JumpIf { cond: Id, then: Id },
}

impl IndexedProc {
    fn block(&self, block_id: CfgId) -> IndexedBlockRef<'_> {
        IndexedBlockRef { proc: self, data: &self.blocks[block_id.index()] }
    }

    fn fallthrough(&self, block_id: CfgId) -> Option<CfgId> {
        assert!(block_id != self.exit());
        block_id.index().checked_sub(1).map(CfgId::new)
    }

    fn successor_blocks(&self, block_id: CfgId) -> impl ExactSizeIterator<Item = CfgId> {
        let (target, fallthrough) = match &self.block(block_id).data.cont {
            Cont::Stop(_) | Cont::Ret(_) => (None, None),
            Cont::Jump(target, _) => (self.labeled_blocks.get(target).map(|&i| CfgId::new(i)), None),
            Cont::JumpIf { then, .. } => (Some(CfgId::new(self.labeled_blocks[then])), Some(self.fallthrough(block_id).unwrap())),
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
}

struct IndexedBlockRef<'a> {
    proc: &'a IndexedProc,
    data: &'a IndexedBlock,
}

impl<'a> IndexedBlockRef<'a> {
    fn priors(&self) -> &'a [core::BlockPrior] {
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

fn index(block: core::Block, stop: Option<usize>, ids: &mut IdGen) -> IndexedProc {
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

    let mut label_count = 0;

    macro_rules! generate_label {
        () => {{
            label_count += 1;
            ids.generate()
        }}
    }

    let mut segments = vec![];
    let mut queue = VecDeque::new();

    macro_rules! unvisited_block {
        ($block:expr) => {{
            let Block { mut priors, mut tail } = $block;
            if let Some(rets) = stop && let TailExpr::Apply(target, args) = tail {
                assert!(rets <= 1);
                if rets == 0 {
                    priors.push(BlockPrior::Let(None, Expr::Apply(target, args)));
                    tail = TailExpr::Unit;
                } else {
                    let res = ids.generate();
                    priors.push(BlockPrior::Let(Some(res), Expr::Apply(target, args)));
                    tail = TailExpr::Var(res);
                }
            }
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
                        queue.push_back(QueueItem::Finished(IndexedBlock {
                            label,
                            input,
                            segment,
                            start,
                            end: segments[segment].len(),
                            cont,
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

    let mut labeled_blocks = HashMap::with_capacity(label_count);

    // Blocks are now in postorder
    let blocks: Vec<_> = Vec::from(queue).into_iter().enumerate().map(|(i, item)| {
        let QueueItem::Finished(b) = item else { unreachable!() };
        if let Some(label) = b.label {
            labeled_blocks.insert(label, i);
        }
        b
    }).collect();

    let mut proc = IndexedProc {
        segments: segments.into_boxed_slice(),
        blocks: blocks.into_boxed_slice(),
        labeled_blocks,
        ipdom: Box::default(),
    };

    proc.ipdom = ipdom(&proc);
    proc
}

impl Graph for IndexedProc {
    type Node = CfgId;

    fn node_count(&self) -> usize {
        self.blocks.len() + 1
    }

    fn nodes(&self) -> impl Iterator<Item = Self::Node> {
        let postorder = self.postorder();
        postorder.iter()
    }
}

impl EntryNode for IndexedProc {
    fn entry(&self) -> CfgId {
        CfgId::new(self.blocks.len() - 1)
    }
}

impl ExitNode for IndexedProc {
    fn exit(&self) -> CfgId {
        CfgId::new(self.blocks.len())
    }
}

impl Successors for IndexedProc {
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

impl Procedure for IndexedProc {
    type BlockId = CfgId;
    type VarId = Id;
    type InstrIdx = InstrIdx;

    fn cfg(&self) -> impl Cfg<Node = Self::BlockId> {
        self
    }

    fn instructions(&self, b: Self::BlockId) -> impl DoubleEndedIterator<Item = (Self::InstrIdx, Self::VarId, DefUse)> {
        use core::*;

        let (priors, input_def, cont_vals, cont_ids): (&[_], _, &[Val], &[Id]) = if b == self.exit() {
            (&[], None, &[], &[])
        } else {
            let block = self.block(b);
            let priors = block.priors();
            let input_def = block.data.input.map(|id| (InstrIdx::Input, id, DefUse::Def));
            let (cont_vals, cont_ids): (&[Val], &[Id]) = match &block.data.cont {
                Cont::Stop(x) | Cont::Ret(x) => (&[], x.as_slice()),
                Cont::Jump(_, args) => (args.as_slice(), &[]),
                Cont::JumpIf { cond, .. } => (&[], slice::from_ref(cond)),
            };
            (priors, input_def, cont_vals, cont_ids)
        };

        let prior_def_uses = priors.iter().enumerate().flat_map(|(i, prior)| {
            let BlockPrior::Let(def, expr) = prior;
            let (vals, ids): (&[Val], &[Id]) = match expr {
                Expr::Unit => (&[], &[]),
                Expr::Val(val) => (slice::from_ref(val), &[]),
                Expr::Op(_, args) => (args.as_slice(), &[]),
                Expr::Apply(_, args) => (args.as_slice(), &[]),
                Expr::IfThenElse(id, _) => (&[], slice::from_ref(id)),
            };
            let def_iter = def.map(|id| (InstrIdx::Prior(i), id, DefUse::Def));
            let uses_iter_vals = vals.iter().filter_map(move |val| match val {
                Val::Var(id) => Some((InstrIdx::Prior(i), *id, DefUse::Use)),
                Val::Const(_) => None,
            });
            let uses_iter_ids = ids.iter().map(move |&id| (InstrIdx::Prior(i), id, DefUse::Use));
            chain(def_iter, uses_iter_vals).chain(uses_iter_ids)
        });

        let cont_uses_vals = cont_vals.iter().filter_map(|v| match v {
            Val::Var(id) => Some((InstrIdx::Cont, *id, DefUse::Use)),
            Val::Const(_) => None,
        });
        let cont_uses_ids = cont_ids.iter().map(|&id| (InstrIdx::Cont, id, DefUse::Use));

        chain(input_def, prior_def_uses).chain(cont_uses_vals).chain(cont_uses_ids)
    }
}

#[cfg(test)]
mod tests {
    use revm::primitives::U256;

    use super::*;
    use crate::id::{IdGen, generate_ids};
    use crate::{asm::Instr::*, core::{self, Block, BlockPrior::*, Expr::*, TailExpr, Val::*}, graph::Successors};

    fn program(main: Block, rets: usize) -> core::Program {
        core::Program { main, rets, procs: vec![] }
    }

    #[test]
    fn test_index_trivial() {
        let mut ids = IdGen::new();
        generate_ids!(ids => x);
        let block = Block {
            priors: vec![],
            tail: TailExpr::Var(x),
        };
        let indexed = index(block, Some(1), &mut ids);
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
        let indexed = index(block, Some(1), &mut ids);
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
        generate_ids!(ids => t, f);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(1)))),
                Let(Some(y), IfThenElse(
                    x,
                    Box::new([
                        Block { priors: vec![Let(Some(t), Val(Const(U256::from(1))))], tail: TailExpr::Var(t) },
                        Block { priors: vec![Let(Some(f), Val(Const(U256::from(0))))], tail: TailExpr::Var(f) },
                    ]),
                )),
            ],
            tail: TailExpr::Var(y),
        };

        let indexed = index(block, Some(1), &mut ids);
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
        generate_ids!(ids => x, t, f);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(2)))),
            ],
            tail: TailExpr::IfThenElse(
                x,
                Box::new([
                    Block { priors: vec![Let(Some(t), Val(Const(U256::from(1))))], tail: TailExpr::Var(t) },
                    Block { priors: vec![Let(Some(f), Val(Const(U256::from(0))))], tail: TailExpr::Var(f) },
                ]),
            ),
        };
        let code = compile(program(block, 1), &mut ids.clone());
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
    fn test_compile_if_then_else_prior() {
        let mut ids = IdGen::new();
        generate_ids!(ids => x, y, t, f);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(2)))),
                Let(Some(y), IfThenElse(
                    x,
                    Box::new([
                        Block { priors: vec![Let(Some(t), Val(Const(U256::from(1))))], tail: TailExpr::Var(t) },
                        Block { priors: vec![Let(Some(f), Val(Const(U256::from(0))))], tail: TailExpr::Var(f) },
                    ]),
                )),
            ],
            tail: TailExpr::Var(y),
        };
        let code = compile(program(block, 1), &mut ids.clone());
        generate_ids!(ids => label1, label2);
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
}
