use std::cmp::max;
use std::collections::HashMap;
use std::iter::{repeat_n, zip};

use smallvec::SmallVec;

use crate::core;
use crate::compile::{
    BasicBlockRef, BlockLiveness, BlockPinning, CfgId, Cont, InstrIdx, ProcCfg, analyze,
};
use crate::id::Id;
use crate::analysis::Procedure;
use crate::graph::{Dfs, Idx, Predecessors, Successors};
use crate::stack::Stack;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Action {
    Pop,
    PushLabel,
    Swap(usize),
    Dup(usize),
}

#[derive(Clone, Default)]
pub struct BlockPlan {
    pub stack_log: Vec<(Id, Option<Id>)>,
    pub stack: Stack<Option<Id>>,
    actions: Vec<Action>,
    prior_action_offsets: Box<[usize]>,
    pub dead_count: usize,
}

impl BlockPlan {
    pub fn actions(&self) -> impl Iterator<Item = &[Action]> {
        (0..=self.prior_action_offsets.len()).map(|i| {
            let start = i.checked_sub(1)
                .and_then(|j| self.prior_action_offsets.get(j))
                .copied()
                .unwrap_or(0);
            let end = self.prior_action_offsets.get(i).copied().unwrap_or(self.actions.len());
            &self.actions[start..end]
        })
    }
}

pub fn plan_proc(proc: &ProcCfg) -> Box<[BlockPlan]> {
    let analysis = analyze(proc);
    let mut block_contexts: Box<[BlockPlan]> = vec![BlockPlan::default(); proc.blocks.len()].into_boxed_slice();

    let dom_tree = analysis.dom_tree();

    for visit in dom_tree.dfs() {
        if visit.exit {
            continue;
        }

        let block_id = visit.node;
        let block = proc.block(block_id);
        let liveness = analysis.liveness(block_id);
        let pinning = analysis.pinning(block_id);
        let last_use = collect_last_use(proc, block_id, liveness.used_count());
        let bp = &mut block_contexts[block_id.index()];

        if proc.predecessors(block_id).len() > 1 {
            bp.dead_count = bp
                .stack
                .contents()
                .iter()
                .rposition(|&x| x.is_some_and(|x| liveness.live_in(x)))
                .map_or(bp.stack.len(), |i| bp.stack.len() - 1 - i);
            bp.stack.popn(bp.dead_count);
        }

        plan_block(block, liveness, pinning, &last_use, bp);

        let children = dom_tree.successors(block_id);
        let stacks = repeat_n(bp.stack.clone(), children.len());
        for (child, stack) in zip(children, stacks) {
            block_contexts[child.index()].stack = stack;
        }
    }

    block_contexts
}

fn collect_last_use(proc: &ProcCfg, block_id: CfgId, capacity: usize) -> HashMap<Id, InstrIdx> {
    let mut last_use = HashMap::with_capacity(capacity);
    for (i, x, _) in proc.instructions(block_id).rev() {
        last_use.entry(x).or_insert(i);
    }
    last_use
}

fn plan_block(
    block: BasicBlockRef,
    liveness: &BlockLiveness,
    pinning: &BlockPinning,
    last_use: &HashMap<Id, InstrIdx>,
    bp: &mut BlockPlan,
) {
    bp.stack.extend(block.inputs().iter().rev().map(|&id| Some(id)));

    let priors = block.priors();
    bp.prior_action_offsets = vec![0; priors.len()].into_boxed_slice();

    for (i, (x, expr)) in priors.iter().enumerate() {
        let is_last_use = |y| !liveness.live_out(y) && last_use[&y] == InstrIdx::Prior(i);
        plan_expr(expr, *x, is_last_use, pinning, bp);
        bp.prior_action_offsets[i] = bp.actions.len();
    }

    plan_cont(
        &block.data().cont,
        liveness,
        pinning,
        last_use,
        bp,
    );
}

fn plan_cont(
    cont: &Cont,
    liveness: &BlockLiveness,
    pinning: &BlockPinning,
    last_use: &HashMap<Id, InstrIdx>,
    bp: &mut BlockPlan,
) {
    let is_live = |x| liveness.live_out(x) || last_use.get(&x) == Some(&InstrIdx::Cont);

    let topmost_pinned_through = bp.stack.contents()
        .iter()
        .rposition(|&x| x.is_some_and(|x| pinning.is_pinned_through(x)));
    let count_live = bp.stack.contents()
        .iter()
        .filter(|&x| x.is_some_and(is_live))
        .count();
    let target_height = max(count_live, topmost_pinned_through.map_or(0, |i| i + 1));

    let count_unpinned = bp.stack.contents()
        .iter()
        .filter(|&x| x.is_some_and(|x| is_live(x) && pinning.is_unpinned(x)))
        .count();

    let is_movable = |x: Option<Id>| x.is_none_or(|x| !pinning.is_pinned_through(x));

    let mut next_unpinned = (0..target_height).rev();
    let last_unpinned = next_unpinned
        .clone()
        .filter(|&i| is_movable(bp.stack.read_base(i)))
        .take(count_unpinned)
        .last();
    let mut next_pinout = (0..last_unpinned.unwrap_or(0)).rev();

    while bp.stack.len() > target_height {
        if let Some(x) = bp.stack[0] && is_live(x) {
            let index =
                if pinning.is_pinned_out(x) {
                    next_pinout.find(|&i| is_movable(bp.stack.read_base(i))).unwrap()
                } else {
                    next_unpinned.find(|&i| is_movable(bp.stack.read_base(i))).unwrap()
                };
            let depth = bp.stack.len() - 1 - index;
            bp.actions.push(Action::Swap(depth));
            bp.stack.swap(depth);
        } else {
            bp.actions.push(Action::Pop);
            bp.stack.popn(1);
        }
    }

    let should_move = |x: Id| !liveness.live_out(x) && last_use[&x] == InstrIdx::Cont;

    match *cont {
        Cont::Stop(_) => {}

        Cont::Ret(x) => {
            let offset = x.is_some() as usize;
            if offset > 0 {
                bp.actions.push(Action::Swap(offset));
            }
        }

        Cont::Jump(_, ref args) => {
            plan_args(args, false, should_move, pinning, bp);
            bp.stack.popn(args.len());
        }

        Cont::JumpIf { cond, then: _ } => {
            let should_move = should_move(cond) && !is_stack_top_pinned(&bp.stack, pinning);
            plan_var(cond, None, 0, should_move, bp);
            bp.stack.popn(1);
        }
    }
}

fn plan_expr(
    expr: &core::Expr,
    output: Option<Id>,
    is_last_use: impl Fn(Id) -> bool,
    pinning: &BlockPinning,
    bp: &mut BlockPlan,
) {
    use core::*;
    match expr {
        Expr::Const(_) => {
            bp.stack.push(output);
        }

        Expr::Var(x) => {
            let should_move = is_last_use(*x) && !is_stack_top_pinned(&bp.stack, pinning);
            plan_var(*x, output, 0, should_move, bp);
        }

        Expr::Op(_, args) => {
            plan_args(args, false, is_last_use, pinning, bp);
            bp.stack.popn(args.len());
            bp.stack.extend(output.map(Some));
        }

        Expr::Apply(_, args) => {
            plan_args(args, true, is_last_use, pinning, bp);
            bp.stack.popn(args.len() + 1);
            bp.stack.extend(output.map(Some));
        }

        Expr::Unit | Expr::IfThenElse(..) => panic!(),
    }
}

fn plan_args(
    args: &[Id],
    has_ret_label: bool,
    is_last_use: impl Fn(Id) -> bool,
    pinning: &BlockPinning,
    bp: &mut BlockPlan,
) {
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
            && bp.stack.read(move_count).is_none_or(|x| !pinning.is_pinned_through(x));
        if can_move && !should_move {
            allow_moves = false;
        }

        plan.push(ArgPlan { should_move, target_depth });
        move_count += should_move as usize;
    }

    if has_ret_label {
        bp.actions.push(Action::PushLabel);
        bp.stack.push(None);
        let offset = move_count;
        if offset > 0 {
            bp.actions.push(Action::Swap(offset));
            bp.stack.swap(offset);
        }
    }

    for (&arg, plan) in zip(args, plan).rev() {
        plan_var(arg, None, plan.target_depth, plan.should_move, bp);
    }
}

fn plan_var(
    x: Id,
    name: Option<Id>,
    target_depth: usize,
    should_move: bool,
    bp: &mut BlockPlan,
) {
    let depth = bp.stack.depth(Some(x));
    if should_move {
        if depth > 0 {
            bp.actions.push(Action::Swap(depth));
            if depth > 16 {
                bp.stack_log.push((x, bp.stack.read(0)));
            }
            bp.stack.swap(depth);
        }
        bp.stack.popn(1);
    } else {
        if depth >= 16 {
            bp.stack_log.push((x, None));
        }
        bp.actions.push(Action::Dup(depth));
    }
    bp.stack.push(name);

    if target_depth > 0 {
        bp.actions.push(Action::Swap(target_depth));
        bp.stack.swap(target_depth);
    }
}

fn is_stack_top_pinned(stack: &Stack<Option<Id>>, pinning: &BlockPinning) -> bool {
    stack.read(0).is_some_and(|y| pinning.is_pinned_through(y))
}
