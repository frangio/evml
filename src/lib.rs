#![allow(unused)]

mod runner;
mod opcodes;
mod scc;

use std::{collections::{HashMap, HashSet}, iter::{once, zip}, mem::take, num::NonZeroUsize};

use anyhow::{anyhow, bail, ensure, Context, Result};
use revm::{bytecode::opcode, primitives::U256};
pub use runner::run;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id(NonZeroUsize);

#[repr(usize)]
enum IdReserve {
    Root = NonZeroUsize::MIN.get(),
    Unallocated,
}

impl IdReserve {
    const fn into_non_zero(self) -> NonZeroUsize {
        NonZeroUsize::new(self as usize).unwrap()
    }
}

impl Id {
    const ROOT: Self = Id(IdReserve::Root.into_non_zero());
}

struct IdGen(NonZeroUsize);

impl IdGen {
    fn new() -> IdGen {
        IdGen(IdReserve::Unallocated.into_non_zero())
    }

    fn generate(&mut self) -> Id {
        let id = Id(self.0);
        self.0 = self.0.checked_add(1).expect("integer overflow");
        id
    }
}

pub mod core {
    use super::Id;
    use revm::primitives::U256;

    #[derive(PartialEq, Eq)]
    pub enum Val {
        Const(U256),
        Var(Id),
    }

    pub enum Expr {
        Val(Val),
        Op(u8, Vec<Val>),
    }

    pub enum TailExpr {
        Expr(Expr),
        Jump(Id, Vec<Id>),
    }

    pub enum BlockPrior {
        Let(Option<Id>, Expr),
        LetJoin(Id, Vec<Id>, Block),
    }

    pub struct Block {
        pub priors: Vec<BlockPrior>,
        pub tail: TailExpr,
    }
}

pub mod ast {
    use revm::primitives::U256;

    #[derive(PartialEq, Eq)]
    pub enum Val<T> {
        Const(U256),
        Var(T),
    }

    pub enum Expr<T> {
        Val(Val<T>),
        Op(u8, Vec<Val<T>>),
    }

    pub enum TailExpr<T> {
        Expr(Expr<T>),
        Jump(T, Vec<T>),
    }

    pub enum BlockPrior<T> {
        Let(Option<T>, Expr<T>),
        LetJoin(T, Vec<T>, Block<T>),
    }

    pub struct Block<T> {
        pub priors: Vec<BlockPrior<T>>,
        pub tail: TailExpr<T>,
    }
}

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

    fn entry(&mut self, x: Id) -> StackEntry<'_> {
        let index = self.0.iter()
            .rposition(|y| y.as_ref().is_some_and(|&y| y == x))
            .expect("unknown variable");
        StackEntry { stack: self, index }
    }
}

impl StackEntry<'_> {
    fn var(&self) -> Id {
        self.stack.0[self.index].expect("stack item is temporary")
    }

    fn set(&mut self, x: Id) {
        self.stack.0[self.index] = Some(x);
    }

    fn depth(&self) -> usize {
        self.stack.0.len() - 1 - self.index
    }

    fn swap(&mut self) {
        let top = self.stack.0.len() - 1;
        self.stack.0.swap(self.index, top);
    }
}

fn opcode_swap(depth: usize) -> u8 {
    assert!(depth > 0, "can't swap top of stack");
    assert!(depth <= 16, "stack too deep");
    opcode::SWAP1 + (depth - 1) as u8
}

fn opcode_dup(depth: usize) -> u8 {
    assert!(depth < 16, "stack too deep");
    opcode::DUP1 + depth as u8
}

fn instruction_push<const N: usize>(value: [u8; N]) -> impl Iterator<Item = u8> {
    assert!(N <= 32);
    let mut size = N;
    let mut value = value.into_iter().peekable();
    while value.next_if_eq(&0).is_some() {
        size -= 1;
    }
    once(opcode::PUSH0 + size as u8).chain(value)
}

fn compile_val_onto(
    val: &core::Val,
    stack: &mut Stack,
    should_swap: impl Fn(&StackEntry) -> bool,
    code: &mut Vec<u8>,
) {
    use core::*;
    match val {
        Val::Const(c) => {
            code.extend(instruction_push(c.to_be_bytes::<32>()));
        }

        Val::Var(x) => {
            let mut entry = stack.entry(*x);
            let depth = entry.depth();
            if !should_swap(&entry) {
                code.push(opcode_dup(depth));
            } else {
                if depth > 0 {
                    code.push(opcode_swap(depth));
                    entry.swap();
                }
                stack.popn(1);
            }
        }
    }
}

fn compile_expr_onto(
    expr: &core::Expr,
    stack: &mut Stack,
    is_last_use: impl Fn(Id) -> bool,
    code: &mut Vec<u8>,
) {
    use core::*;
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
                    code.push(opcode_swap(offset));
                    stack.swap(offset);
                }
            }

            code.push(*op);
            stack.popn(args.len());
        }
    }
}

struct BlockCode {
    code: Vec<u8>,
    refs: Vec<(usize, Id)>,
}

struct CompileQueue {
    buffer: Vec<(Id, Option<BlockCode>)>,
    joins: HashMap<Id, (Vec<Id>, core::Block, BlockLiveness, Option<Stack>)>,
    next: usize,
}

impl CompileQueue {
    fn new() -> Self {
        CompileQueue {
            buffer: Vec::new(),
            joins: HashMap::new(),
            next: 0,
        }
    }

    fn register(&mut self, id: Id, args: Vec<Id>, block: core::Block, liveness: BlockLiveness) {
        let other_join = self.joins.insert(id, (args, block, liveness, None));
        assert!(other_join.is_none(), "duplicate label");
    }

    fn get_args(&self, id: Id) -> &[Id] {
        let join = self.joins.get(&id).unwrap();
        &join.0
    }

    fn enqueue(&mut self, id: Id, stack: Stack) {
        let join = self.joins.get_mut(&id).unwrap();
        let other_stack = join.3.replace(stack);
        if let Some(_other_stack) = other_stack {
            todo!();
        } else {
            self.buffer.push((id, None));
        }
    }

    fn next(&mut self) -> Option<(Id, core::Block, BlockLiveness, Stack)> {
        let (k, _) = self.buffer.get(self.next)?;
        let (_, block, liveness, stack) = self.joins.remove(k).unwrap();
        self.next += 1;
        Some((*k, block, liveness, stack.unwrap()))
    }

    fn set_result(&mut self, id: Id, code: BlockCode) {
        let (k, result) = &mut self.buffer[self.next - 1];
        assert!(*k == id, "mismatched result");
        *result = Some(code);
    }

    fn into_results(self) -> Vec<(Id, BlockCode)> {
        self.buffer.into_iter().map(|(k, b)| (k, b.unwrap())).collect()
    }
}

fn compile_block(
    block: core::Block,
    mut liveness: BlockLiveness,
    mut stack: Stack,
    queue: &mut CompileQueue,
    join_uses: &HashMap<Id, HashSet<Id>>,
) -> BlockCode {
    use core::*;
    let mut joins_liveness = take(&mut liveness.joins).into_iter();
    let mut code = vec![];
    let mut refs = vec![];

    for (prior, is_last_use) in zip(block.priors, liveness.iter()) {
        match prior {
            BlockPrior::Let(x, e) => {
                compile_expr_onto(&e, &mut stack, is_last_use, &mut code);
                if let Some(x) = x {
                    stack.push(Some(x));
                }
            }

            BlockPrior::LetJoin(k, xs, b) => {
                let (j, liveness) = joins_liveness.next().unwrap();
                assert!(j == k);
                queue.register(k, xs, b, liveness);
            }
        }
    }

    match &block.tail {
        TailExpr::Expr(tail_expr) => {
            compile_expr_onto(tail_expr, &mut stack, |_| true, &mut code);
            let excess = stack.len();
            if excess > 0 {
                let ret = size_of(tail_expr);
                for _ in 0..ret {
                    code.push(opcode_swap(excess));
                    code.push(opcode::POP);
                }
                if excess > ret {
                    code.resize(code.len() + excess - ret, opcode::POP);
                }
            }
        }

        TailExpr::Jump(k, xs) => {
            let k_uses = join_uses.get(k).unwrap();
            let args = queue.get_args(*k);
            for (x, arg) in zip(xs, args) {
                let mut e = stack.entry(*x);
                if k_uses.contains(x) {
                    code.push(opcode_dup(e.depth()));
                    stack.push(Some(*arg));
                } else {
                    e.set(*arg);
                }
            }
            queue.enqueue(*k, stack);
            refs.push((code.len(), *k));
            code.push(opcode::CODESIZE);
            code.push(opcode::JUMP);
        }
    }

    BlockCode { code, refs }
}

pub fn compile(block: core::Block) -> Vec<u8> {
    let mut queue = CompileQueue::new();

    let (liveness, join_uses) = analyze_liveness(&block);
    let entry = compile_block(block, liveness, Stack::new(), &mut queue, &join_uses);

    while let Some((k, block, liveness, stack)) = queue.next() {
        let code = compile_block(block, liveness, stack, &mut queue, &join_uses);
        queue.set_result(k, code);
    }

    link(entry, queue.into_results())
}

fn link_block(
    block: &BlockCode,
    locs: &HashMap<Id, usize>,
    pending_refs: &mut Vec<(usize, Id)>,
    code: &mut Vec<u8>,
) {
    let mut start = 0;
    for &(pos, j) in &block.refs {
        code.extend(&block.code[start..pos]);
        start = pos + 1;
        assert!(block.code[pos..pos + 2] == [opcode::CODESIZE, opcode::JUMP]);
        match locs.get(&j) {
            Some(x) => {
                code.extend(instruction_push(x.to_be_bytes()))
            }
            None => {
                pending_refs.push((code.len(), j));
                code.extend([opcode::PUSH2, 0, 0]);
            }
        }
    }
    code.extend(&block.code[start..]);
}

fn link(entry: BlockCode, blocks: Vec<(Id, BlockCode)>) -> Vec<u8> {
    let mut locs: HashMap<Id, usize> = HashMap::new();
    let mut code = Vec::new();
    let mut pending_refs = Vec::new();

    link_block(&entry, &locs, &mut pending_refs, &mut code);

    for (k, block) in blocks {
        if let Some((pos, _)) = pending_refs.pop_if(|(pos, j)| *j == k && *pos + 4 == code.len()) {
            assert!(code[pos..] == [opcode::PUSH2, 0, 0, opcode::JUMP]);
            code.truncate(pos);
        }

        let other_loc = locs.insert(k, code.len());
        assert!(other_loc.is_none(), "duplicate id");

        code.push(opcode::JUMPDEST);

        link_block(&block, &locs, &mut pending_refs, &mut code);
    }

    for (pos, j) in pending_refs {
        assert!(code[pos..pos + 4] == [opcode::PUSH2, 0, 0, opcode::JUMP]);
        let x = locs.get(&j).unwrap();
        code[pos + 1..pos + 2].copy_from_slice(&x.to_be_bytes());
    }

    code
}

struct BlockLiveness {
    last_use: Vec<(Id, usize)>,
    joins: Vec<(Id, BlockLiveness)>,
}

impl BlockLiveness {
    fn iter(&self) -> impl Iterator<Item = impl Fn(Id) -> bool> + use<'_> {
        let mut next_start = 0;
        (0..).map(move |block_pos| {
            let end = self.last_use.len();
            let mut iter = self.last_use.iter().skip(next_start);
            let curr_start = iter.position(|&(_, p)| p == block_pos).unwrap_or(end);
            next_start = iter.position(|&(_, p)| p != block_pos).unwrap_or(end);
            move |x| self.last_use[curr_start..next_start].iter().any(|&(y, _)| x == y)
        })
    }
}

fn analyze_liveness_expr(expr: &core::Expr, block_pos: usize, last_use: &mut HashMap<Id, usize>) {
    use core::*;
    let mut analyze_val = |val| {
        if let &Val::Var(x) = val {
            last_use.insert(x, block_pos);
        }
    };

    match expr {
        Expr::Val(val) => analyze_val(val),
        Expr::Op(_, args) => {
            for arg in args {
                analyze_val(arg);
            }
        }
    }
}

fn analyze_liveness_block(block: &core::Block, join_uses: &mut HashMap<Id, HashSet<Id>>) -> BlockLiveness {
    use core::*;
    let mut last_use = HashMap::new();
    let mut joins = Vec::new();

    for (block_pos, prior) in block.priors.iter().enumerate() {
        match prior {
            BlockPrior::Let(x, expr) => {
                if let Some(x) = x {
                    let other_pos = last_use.insert(*x, block_pos);
                    assert!(other_pos.is_none());
                }
                analyze_liveness_expr(expr, block_pos, &mut last_use);
            }

            BlockPrior::LetJoin(k, xs, b) => {
                let k_liveness = analyze_liveness_block(b, join_uses);
                let mut k_uses = HashSet::with_capacity(k_liveness.last_use.len());
                for &(y, _) in &k_liveness.last_use {
                    if xs.contains(&y) {
                        continue;
                    }
                    if last_use.insert(y, block_pos).is_some() {
                        k_uses.insert(y);
                    }
                }
                joins.push((*k, k_liveness));
                join_uses.insert(*k, k_uses);
            }
        }
    }

    let tail_pos = block.priors.len();
    match &block.tail {
        TailExpr::Expr(tail_expr) => {
            analyze_liveness_expr(tail_expr, tail_pos, &mut last_use);
        }

        TailExpr::Jump(k, args) => {
            for arg in args {
                last_use.insert(*arg, tail_pos);
            }
            for x in join_uses.get(k).unwrap() {
                last_use.insert(*x, tail_pos);
            }
        }
    }

    let mut last_use = Vec::from_iter(last_use);
    last_use.sort_unstable_by(|(_, i), (_, j)| i.cmp(j));

    BlockLiveness { last_use, joins }
}

fn analyze_liveness(block: &core::Block) -> (BlockLiveness, HashMap<Id, HashSet<Id>>) {
    let mut join_uses = HashMap::new();
    let block_liveness = analyze_liveness_block(block, &mut join_uses);
    (block_liveness, join_uses)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Type {
    Val,
    Join(usize),
}

fn size_of(expr: &core::Expr) -> usize {
    use core::*;
    match expr {
        Expr::Val(_) => 1,
        Expr::Op(op, _) => opcodes::info(*op).unwrap().outputs,
    }
}

fn type_check_expr(expr: &core::Expr, env: &HashMap<Id, Type>) -> Result<usize> {
    use core::*;
    let type_check_val = |v: &Val<Id>| -> Result<usize> {
        if let Val::Var(x) = v {
            ensure!(env.get(x).copied() == Some(Type::Val), "variable is not a value");
        }
        Ok(1)
    };

    match expr {
        Expr::Val(v) => type_check_val(v),

        Expr::Op(op, args) => {
            let Some(info) = opcodes::info(*op) else { bail!("unknown opcode {op:#04x?}") };
            ensure!(args.len() == info.inputs);
            for arg in args {
                type_check_val(arg)?;
            }
            Ok(info.outputs)
        }
    }
}

fn type_check_block(block: &core::Block, mut env: HashMap<Id, Type>) -> Result<()> {
    use core::*;
    for prior in &block.priors {
        match prior {
            BlockPrior::Let(x, e) => {
                let outputs = type_check_expr(e, &env)?;
                ensure!(outputs == x.iter().count(), "void operation can't be assigned");
                if let Some(x) = x {
                    env.insert(*x, Type::Val);
                }
            }

            BlockPrior::LetJoin(k, xs, block) => {
                env.insert(*k, Type::Join(xs.len()));
                let mut env = env.clone();
                for x in xs {
                    env.insert(*x, Type::Val);
                }
                type_check_block(block, env)?;
            }
        }
    }

    match &block.tail {
        TailExpr::Expr(expr) => {
            type_check_expr(expr, &env)?;
        }

        TailExpr::Jump(k, xs) => {
            let &Type::Join(arity) = env.get(k).unwrap() else {
                bail!("cannot jump to value")
            };
            ensure!(xs.len() == arity, "bad jump argument count");
        }
    }

    Ok(())
}

pub fn type_check(block: &core::Block) -> Result<()> {
    let env = HashMap::new();
    type_check_block(block, env)
}

fn resolve_val(val: &ast::Val<String>, env: &HashMap<&String, Id>) -> Result<core::Val> {
    Ok(match val {
        ast::Val::Const(c) => core::Val::Const(*c),
        ast::Val::Var(x) => {
            core::Val::Var(*env.get(x).with_context(|| format!("unbound variable {x}"))?)
        }
    })
}

fn resolve_expr(expr: &ast::Expr<String>, env: &HashMap<&String, Id>) -> Result<core::Expr> {
    Ok(match expr {
        ast::Expr::Val(val) => core::Expr::Val(resolve_val(val, env)?),
        ast::Expr::Op(op, vals) => {
            let vals = vals.iter().map(|val| resolve_val(val, env)).collect::<Result<_>>()?;
            core::Expr::Op(*op, vals)
        }
    })
}

fn resolve_block<'a>(
    block: &'a ast::Block<String>,
    ids: &mut IdGen,
    mut env: HashMap<&'a String, Id>,
) -> Result<core::Block> {
    let mut priors = Vec::with_capacity(block.priors.len());

    for prior in &block.priors {
        match prior {
            BlockPrior::Let(x, expr) => {
                let expr = resolve_expr(expr, &env)?;
                let y = x.as_ref().map(|x| {
                    let y = ids.generate();
                    env.insert(x, y);
                    y
                });
                priors.push(core::BlockPrior::Let(y, expr));
            }

            BlockPrior::LetJoin(k, xs, block) => {
                let j = ids.generate();
                env.insert(k, j);
                let mut env = env.clone();
                let ys = xs.iter().map(|x| {
                    let y = ids.generate();
                    env.insert(x, y);
                    y
                }).collect();
                let block = resolve_block(block, ids, env)?;
                priors.push(core::BlockPrior::LetJoin(j, ys, block));
            }
        }
    }

    let tail = match &block.tail {
        ast::TailExpr::Expr(expr) => core::TailExpr::Expr(resolve_expr(expr, &env)?),
        ast::TailExpr::Jump(k, xs) => {
            let k = *env.get(k).with_context(|| format!("unbound label {k}"))?;
            let xs = xs.iter().map(|x| {
                env.get(x).copied().with_context(|| format!("unbound variable {x}"))
            }).collect::<Result<_>>()?;
            core::TailExpr::Jump(k, xs)
        }
    };

    Ok(core::Block { priors, tail })
}

pub fn resolve(block: &ast::Block<String>) -> Result<core::Block> {
    let mut ids = IdGen::new();
    let env = HashMap::new();
    resolve_block(block, &mut ids, env)
}

pub fn parse(source: &str) -> Result<ast::Block<String>> {
    use chumsky::prelude::*;
    use ast::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Block<String>, extra::Err<Rich<'a, char>>> {
        let val_const = text::digits(10)
            .to_slice()
            .try_map(|digits: &str, span| {
                digits
                    .parse::<U256>()
                    .map_err(|e| Rich::custom(span, e.to_string()))
                    .map(Val::Const)
            });

        let val_var = text::ident()
            .map(|x: &str| Val::Var(x.to_owned()));

        let val = choice((
            val_const,
            val_var,
        )).padded();

        let expr_val = val.map(Expr::Val);

        let expr_op = just('@')
            .ignore_then(text::ident())
            .try_map(|opcode_name: &str, span| {
                opcodes::lookup(opcode_name)
                    .ok_or_else(|| Rich::custom(span, format!("unknown opcode {opcode_name}")))
            })
            .then(
                val.separated_by(just(','))
                    .collect::<Vec<_>>()
                    .delimited_by(just('('), just(')'))
            )
            .map(|(op, args)| Expr::Op(op, args));

        let expr = choice((
            expr_op,
            expr_val,
        )).padded();

        let args = text::ident()
            .map(|id: &str| id.to_owned())
            .padded()
            .separated_by(just(','))
            .collect::<Vec<_>>()
            .delimited_by(just('('), just(')'))
            .padded();

        let tail_expr_jump = text::keyword("jump")
            .padded()
            .ignore_then(
                text::ident().map(|id: &str| id.to_owned()),
            )
            .padded()
            .then(args)
            .map(|(k, xs)| TailExpr::Jump(k, xs));


        let tail_expr = choice((
            tail_expr_jump,
            expr.map(TailExpr::Expr),
        ));

        let block_let = text::keyword("let")
            .padded()
            .ignore_then(
                choice((
                    just('_').to(None),
                    text::ident().map(|id: &str| Some(id.to_owned())),
                ))
            )
            .padded()
            .then_ignore(just('='))
            .then(expr)
            .then_ignore(just(';'))
            .map(|(x, e)| BlockPrior::Let(x, e));

        let block = recursive(|block| {
            let block_join = text::keyword("join")
                .padded()
                .ignore_then(text::ident().map(|id: &str| id.to_owned()))
                .padded()
                .then(args)
                .then(
                    block
                        .padded()
                        .delimited_by(just('{'), just('}'))
                )
                .padded()
                .map(|((k, xs), b)| BlockPrior::LetJoin(k, xs, b));


            choice((block_let, block_join))
                .padded()
                .repeated()
                .collect()
                .then(tail_expr)
                .padded()
                .map(|(priors, tail)| Block { priors, tail })
        });

        block.then_ignore(end())
    }

    let b = parser()
        .parse(source)
        .into_result()
        .map_err(|es| anyhow!(es[0].to_string()))?;

    Ok(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! id {
        ($n:expr) => { Id(::std::num::NonZeroUsize::new($n).unwrap()) }
    }

    #[test]
    fn test_const() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Expr(Val(Const(U256::from(42)))),
        };
        let bytecode = compile(block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_op_div() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Expr(Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))])),
        };
        let bytecode = compile(block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_val() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Val(Const(U256::from(2)))),
            ],
            tail: Expr(Op(0x04, vec![Const(U256::from(84)), Var(id!(1))])),
        };
        let bytecode = compile(block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))])),
            ],
            tail: Expr(Val(Var(id!(1)))),
        };
        let bytecode = compile(block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op_reuse() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Val(Const(U256::from(42)))),
            ],
            tail: Expr(Op(0x04, vec![Var(id!(1)), Var(id!(1))])),
        };
        let bytecode = compile(block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(1)]);
    }

    #[test]
    fn test_let_unused() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Val(Const(U256::from(100)))),
                Let(Some(id!(2)), Val(Const(U256::from(100)))),
            ],
            tail: Expr(Val(Const(U256::from(42)))),
        };
        let bytecode = compile(block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_join_jump() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Val(Const(U256::from(21)))),
                LetJoin(id!(2), vec![id!(3)], Block {
                    priors: vec![],
                    tail: Expr(Op(0x01, vec![Var(id!(3)), Var(id!(1))])),
                }),
            ],
            tail: Jump(id!(2), vec![id!(1)]),
        };
        let bytecode = compile(block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    #[ignore]
    fn test_join_jump_rec() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![
                LetJoin(id!(1), vec![], Block {
                    priors: vec![],
                    tail: Jump(id!(1), vec![]),
                }),
            ],
            tail: Jump(id!(1), vec![]),
        };
        let bytecode = compile(block);
        assert_eq!(bytecode, [opcode::JUMPDEST, opcode::PUSH0, opcode::JUMP]);
    }

    #[test]
    fn test_type_check_div_ok() {
        use super::ast::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Expr(Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))])),
        };
        assert!(type_check(&block).is_ok());
    }

    #[test]
    fn test_type_check_div_err() {
        use super::ast::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Expr(Op(0x04, vec![Const(U256::from(84))])),
        };
        assert!(type_check(&block).is_err());
    }

    #[test]
    fn test_type_check_pop_err() {
        use super::ast::{Block, BlockPrior::*, Expr::*, TailExpr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Op(0x50, vec![Const(U256::from(42))])),
            ],
            tail: Expr(Val(Const(U256::from(0)))),
        };
        assert!(type_check(&block).is_err());
    }
}
