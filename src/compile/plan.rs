use std::cmp::max;
use std::collections::HashMap;
use std::iter::{repeat_n, zip};

use smallvec::SmallVec;

use crate::core;
use crate::compile::{
    BasicBlockRef, BlockLiveness, BlockPinning, CfgId, Cont, InstrIdx, ProcAnalysis, ProcCfg, analyze
};
use crate::id::Id;
use crate::analysis::Procedure;
use crate::graph::{Dfs, EntryNode, Graph, Idx, Predecessors, Successors};
use crate::stack::Stack;
use crate::utils::exact_size_chain;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Action {
    Pop,
    PushLabel,
    Swap(usize),
    Dup(usize),
    Rload(usize),
    Rstore(usize),
}

#[derive(Clone, Default)]
pub struct BlockPlan {
    actions: Vec<Action>,
    actions_boundaries: Box<[usize]>,
    pub stack_log: Vec<Id>,
    pub stack: Stack<Option<Id>>,
    pub dead_count: usize,
}

impl BlockPlan {
    pub fn prior_actions(&self) -> impl Iterator<Item = impl Iterator<Item = Action>> {
        (0..self.actions_boundaries.len()).map(|i| {
            let start = i.checked_sub(1)
                .and_then(|j| self.actions_boundaries.get(j))
                .copied()
                .unwrap_or(0);
            let end = self.actions_boundaries[i];
            self.actions[start..end].iter().copied()
        })
    }

    pub fn cont_actions(&self) -> impl Iterator<Item = Action> {
        let start = self.actions_boundaries.last().copied().unwrap_or(0);
        self.actions[start..].iter().copied()
    }
}

pub fn plan_proc(proc: &ProcCfg) -> Box<[BlockPlan]> {
    let analysis = analyze(proc);
    let mut block_contexts: Box<[BlockPlan]> = vec![BlockPlan::default(); proc.blocks.len()].into_boxed_slice();

    if let Some(ret_target_var) = proc.ret_target_var() {
        block_contexts[proc.entry().index()].stack.push(Some(ret_target_var));
    }

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

    let spills = spill(proc, &analysis, &block_contexts);
    let mut spill_stacks = vec![None; proc.blocks.len()].into_boxed_slice();

    for visit in dom_tree.dfs() {
        if visit.exit {
            continue;
        }

        let block_id = visit.node;
        let block = proc.block(block_id);
        let block_spills = &spills[block_id.index()];
        let spill_stack = &mut spill_stacks[block_id.index()];

        if !block_spills.is_empty() && spill_stack.is_none() {
            let size = dom_tree.parent(block_id)
                .map(|parent_id| block_contexts[parent_id.index()].stack.len())
                .unwrap_or(0);
            *spill_stack = Some((0, Stack::from_iter(repeat_n(None, size))));
        }

        if let Some((spill_count, spill_stack)) = spill_stack {
            spill_stack.popn(block_contexts[block_id.index()].dead_count);
            spill_stack.extend(repeat_n(None, block.inputs().len()));

            if block.inputs().len() >= STACK_REACH {
                todo!("calling convention");
            }

            replan_block_spilled(
                block,
                block_spills,
                spill_count,
                spill_stack,
                &mut block_contexts[block_id.index()],
            );

            if *spill_count != 0 {
                let children = dom_tree.successors(block_id);
                let child_spill_stacks =
                    repeat_n(Some((*spill_count, spill_stack.clone())), children.len());
                for (child, spill_stack) in zip(children, child_spill_stacks) {
                    spill_stacks[child.index()] = spill_stack;
                }
            }
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
    bp.actions_boundaries = vec![0; priors.len()].into_boxed_slice();

    for (i, (x, expr)) in priors.iter().enumerate() {
        let is_last_use = |y| !liveness.live_out(y) && last_use[&y] == InstrIdx::Prior(i);
        plan_expr(expr, *x, is_last_use, pinning, bp);
        bp.actions_boundaries[i] = bp.actions.len();
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
        Cont::Ret { target_var, value } => {
            if target_var.is_some() && value.is_some() {
                bp.actions.push(Action::Swap(1));
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
                bp.stack_log.push(x);
            }
            bp.stack.swap(depth);
        }
        bp.stack.popn(1);
    } else {
        if depth >= 16 {
            bp.stack_log.push(x);
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

fn replan_block_spilled(
    block: BasicBlockRef,
    block_spills: &HashMap<Id, Spill>,
    spill_count: &mut usize,
    spill_stack: &mut Stack<Option<usize>>,
    bp: &mut BlockPlan,
) {
    use core::Expr;

    let mut new_actions = vec![];
    let mut new_actions_boundaries = vec![0; block.priors().len()].into_boxed_slice();

    for spill in block_spills.values() {
        if let Some(index) = spill.entry_index {
            spill_to(index, spill.register, &mut new_actions, spill_count, spill_stack);
        }
    }

    for (i, ((output, expr), site_actions)) in zip(block.priors(), bp.prior_actions()).enumerate() {
        for action in site_actions {
            replan_action_spilled(action, &mut new_actions, spill_count, spill_stack);
        }
        let pop_count = match expr {
            Expr::Var(_) => 1,
            Expr::Const(_) => 0,
            Expr::Op(_, args) => args.len(),
            Expr::Apply(_, args) => args.len() + 1,
            Expr::Unit | Expr::IfThenElse(..) => panic!(),
        };
        replan_popn_spilled(pop_count, &mut new_actions, spill_count, spill_stack);

        new_actions_boundaries[i] = new_actions.len();

        if let Some(output) = *output {
            spill_stack.push(None);
            if let Some(spill) = block_spills.get(&output) {
                spill_to(0, spill.register, &mut new_actions, spill_count, spill_stack);
            }
        }
    }

    for action in bp.cont_actions() {
        replan_action_spilled(action, &mut new_actions, spill_count, spill_stack);
    }
    let pop_count = match &block.data().cont {
        Cont::Ret { target_var, value } => exact_size_chain(target_var, value).len(),
        Cont::Jump(_, args) => args.len(),
        Cont::JumpIf { .. } => 1,
    };
    replan_popn_spilled(pop_count, &mut new_actions, spill_count, spill_stack);

    bp.actions = new_actions;
    bp.actions_boundaries = new_actions_boundaries;
}

fn spill_to(
    index: usize,
    register: usize,
    actions: &mut Vec<Action>,
    spill_count: &mut usize,
    spill_stack: &mut Stack<Option<usize>>,
) {
    actions.extend(rswap(index, register));
    assert!(spill_stack[index].is_none());
    *spill_count += 1;
    spill_stack[index] = Some(register);
}

fn spill_from(
    index: usize,
    actions: &mut Vec<Action>,
    spill_count: &mut usize,
    spill_stack: &mut Stack<Option<usize>>,
) {
    let register = spill_stack[index].unwrap();
    actions.extend(rswap(index, register));
    *spill_count -= 1;
    spill_stack[index] = None;
}

fn rswap(index: usize, register: usize) -> impl Iterator<Item = Action> {
    [
        Action::Rload(register),
        Action::Swap(index + 1),
        Action::Rstore(register),
    ].into_iter()
}

fn replan_action_spilled(
    action: Action,
    actions: &mut Vec<Action>,
    spill_count: &mut usize,
    spill_stack: &mut Stack<Option<usize>>,
) {
    match action {
        Action::Pop => {
            if let Some(register) = spill_stack[0] {
                actions.push(Action::Rstore(register));
                *spill_count -= 1;
            } else {
                actions.push(Action::Pop);
            }
            spill_stack.popn(1);
        }
        Action::PushLabel => {
            actions.push(Action::PushLabel);
            spill_stack.push(None);
        }
        Action::Swap(depth) => {
            if depth >= STACK_REACH {
                actions.extend(rswap(0, spill_stack[depth].unwrap()));
            } else {
                actions.push(Action::Swap(depth));
                spill_stack.swap(depth);
            }
        }
        Action::Dup(depth) => {
            if let Some(register) = spill_stack[depth] {
                actions.push(Action::Rload(register));
            } else {
                assert!(depth < STACK_REACH);
                actions.push(Action::Dup(depth));
            }
            spill_stack.push(None);
        }
        Action::Rload(_) | Action::Rstore(_) => panic!(),
    }
}

fn replan_popn_spilled(
    count: usize,
    actions: &mut Vec<Action>,
    spill_count: &mut usize,
    spill_stack: &mut Stack<Option<usize>>,
) {
    for index in 0..count {
        if spill_stack[index].is_some() {
            spill_from(index, actions, spill_count, spill_stack);
        }
    }
    spill_stack.popn(count);
}

const STACK_REACH: usize = 16;

#[derive(Clone, Copy)]
pub struct Spill {
    entry_index: Option<usize>,
    register: usize,
}

pub fn spill(
    proc: &ProcCfg,
    analysis: &ProcAnalysis,
    block_contexts: &[BlockPlan],
) -> Box<[HashMap<Id, Spill>]> {
    let dom_tree = analysis.dom_tree();
    let mut var_spill = HashMap::<Id, CfgId>::new();

    for block_id in proc.nodes() {
        let bp = &block_contexts[block_id.index()];
        for &var in &bp.stack_log {
            var_spill
                .entry(var)
                .and_modify(|block| *block = dom_tree.nca(*block, block_id))
                .or_insert(block_id);
        }
    }
    let spill_count = var_spill.len();

    let entry_index = |block_id: CfgId, var: Id| {
        let dead_count = block_contexts[block_id.index()].dead_count;
        let inputs_count = proc.block(block_id).inputs().len();
        let entry_reachable_count = STACK_REACH.saturating_sub(inputs_count);
        let parent_id = dom_tree.parent(block_id)?;
        let parent_stack = block_contexts[parent_id.index()].stack.contents();
        parent_stack
            .iter()
            .rev()
            .skip(dead_count)
            .take(entry_reachable_count)
            .position(|&slot| slot == Some(var))
            .map(|depth| inputs_count + depth)
    };

    let mut block_spills =
        vec![HashMap::new(); proc.node_count()].into_boxed_slice();

    for (var, mut block_id) in var_spill {
        let entry_index = loop {
            if !analysis.liveness(block_id).live_in(var) {
                break None;
            }
            if !analysis.pinning(block_id).is_pinned_through(var)
                && let Some(i) = entry_index(block_id, var)
            {
                break Some(i);
            }
            block_id = dom_tree.parent(block_id).unwrap();
        };

        block_spills[block_id.index()].insert(var, Spill { entry_index, register: 0 });
    }

    let mut registers: Vec<(usize, Option<Id>)> = Vec::with_capacity(spill_count);
    let mut free = 0;
    let mut log: Vec<(usize, Option<Id>)> = Vec::with_capacity(spill_count * 2);
    let mut checkpoints = Vec::with_capacity(dom_tree.height());

    for visit in dom_tree.dfs() {
        let block_id = visit.node;
        let liveness = analysis.liveness(block_id);

        if visit.exit {
            let checkpoint = checkpoints.pop().unwrap();
            for (i, var) in log.drain(checkpoint..).rev() {
                if var.is_some() {
                    registers.swap(i, free);
                    free += 1;
                } else {
                    free -= 1;
                };
                registers[i].1 = var;
            }
        } else {
            checkpoints.push(log.len());

            let mut i = 0;
            while let Some(&(_, Some(var))) = registers.get(i) {
                if liveness.live_in(var) {
                    i += 1;
                } else {
                    log.push((i, registers[i].1));
                    registers[i].1 = None;
                    free -= 1;
                    registers.swap(i, free);
                }
            }

            let start = free;
            free += block_spills[block_id.index()].len();
            registers.extend((registers.len()..free).map(|reg| (reg, None)));

            for (k, (&var, spill)) in block_spills[block_id.index()].iter_mut().enumerate() {
                let i = start + k;
                spill.register = registers[i].0;
                log.push((i, registers[i].1));
                registers[i].1 = Some(var);
            }
        }
    }

    block_spills
}
