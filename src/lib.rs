#![allow(unused)]

mod runner;
mod opcodes;
mod scc;
mod graph;
mod analysis;

use std::{collections::HashMap, iter::{chain, once, zip}, num::NonZeroUsize, slice};

use anyhow::{anyhow, bail, ensure, Context, Result};
use revm::{bytecode::opcode, primitives::U256};
pub use runner::run;

use crate::analysis::{Instruction, Procedure, liveness};
use crate::graph::{DepthFirstPostorder, SingletonGraph, Successors};

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

    pub enum BlockPrior<T> {
        Let(Option<T>, Expr<T>),
    }

    pub struct Block<T> {
        pub priors: Vec<BlockPrior<T>>,
        pub tail: Expr<T>,
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

    pub enum BlockPrior {
        Let(Option<Id>, Expr),
    }

    pub struct Block {
        pub priors: Vec<BlockPrior>,
        pub tail: Expr,
    }
}

pub mod asm {
    use super::Id;
    use revm::primitives::U256;

    pub enum Instr {
        Pop,
        Push(U256),
        Swap(usize),
        Dup(usize),
        Op(u8),
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
            if !should_swap(&entry) {
                code.push(Instr::Dup(depth));
            } else {
                if depth > 0 {
                    code.push(Instr::Swap(depth));
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
    }
}

fn compile_block(
    block: core::Block,
    mut liveness: &BlockLiveness,
    mut stack: Stack,
) -> Vec<asm::Instr> {
    use core::*;
    use asm::*;

    let mut code = vec![];

    for (i, prior) in block.priors.into_iter().enumerate() {
        let is_last_use = |x| liveness[&x].last_use == Some(i);
        match prior {
            BlockPrior::Let(x, e) => {
                compile_expr_onto(&e, &mut stack, is_last_use, &mut code);
                if let Some(x) = x {
                    stack.push(Some(x));
                }
            }

        }
    }

    compile_expr_onto(&block.tail, &mut stack, |_| true, &mut code);
    let excess = stack.len();
    if excess > 0 {
        let ret = size_of(&block.tail);
        for _ in 0..ret {
            code.push(Instr::Swap(excess));
            code.push(Instr::Pop);
        }
        if excess > ret {
            code.resize_with(code.len() + excess - ret, || Instr::Pop);
        }
    }

    code
}

pub fn compile(block: core::Block) -> Vec<asm::Instr> {
    let analysis = analyze(&block);
    compile_block(block, &analysis.liveness[&Id::ROOT], Stack::new())
}

pub fn assemble(code: &[asm::Instr]) -> Vec<u8> {
    use asm::Instr::*;
    let mut bytecode = Vec::with_capacity(code.len());
    for instr in code {
        match instr {
            Pop => bytecode.push(opcode::POP),
            Push(value) => bytecode.extend(instruction_push(value.to_be_bytes::<32>())),
            Swap(depth) => bytecode.push(opcode_swap(*depth)),
            Dup(depth) => bytecode.push(opcode_dup(*depth)),
            Op(op) => bytecode.push(*op),
        }
    }
    bytecode
}

struct BlockInstruction<'a> {
    block: &'a core::Block,
    index: usize,
}

impl Instruction for BlockInstruction<'_> {
    type VarId = Id;

    fn index(&self) -> usize {
        self.index
    }

    fn defs(&self) -> impl Iterator<Item = Self::VarId> {
        self.block.priors.get(self.index)
            .and_then(|core::BlockPrior::Let(x, _)| *x)
            .into_iter()
    }

    fn uses(&self) -> impl Iterator<Item = Self::VarId> {
        use core::*;
        let expr = match self.block.priors.get(self.index) {
            Some(BlockPrior::Let(_, e)) => e,
            None => &self.block.tail,
        };
        let vals = match expr {
            Expr::Val(val) => slice::from_ref(val),
            Expr::Op(_, args) => args,
        };
        vals.iter().filter_map(|val| match val {
            Val::Var(id) => Some(*id),
            Val::Const(_) => None,
        })
    }
}

impl Procedure for core::Block {
    type BlockId = Id;
    type VarId = Id;

    fn cfg(&self) -> impl DepthFirstPostorder<Node = Self::BlockId> + Successors {
        SingletonGraph(Id::ROOT)
    }

    fn instructions(
        &self,
        _b: Self::BlockId,
    ) -> impl DoubleEndedIterator<Item: Instruction<VarId = Self::VarId>> {
        (0..=self.priors.len()).map(|i| BlockInstruction { block: self, index: i })
    }
}

type Liveness = analysis::Liveness<core::Block>;
type BlockLiveness = analysis::BlockLiveness<core::Block>;

struct Analysis {
    liveness: Liveness,
}

fn analyze(block: &core::Block) -> Analysis {
    let liveness = liveness(block);
    Analysis { liveness }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Type {
    Val,
}

fn size_of(expr: &core::Expr) -> usize {
    use core::*;
    match expr {
        Expr::Val(_) => 1,
        Expr::Op(op, _) => opcodes::info(*op).unwrap().outputs,
    }
}

fn type_check_expr(expr: &ast::Expr<Id>, env: &HashMap<Id, Type>) -> Result<usize> {
    use ast::*;
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

fn type_check_block(block: &ast::Block<Id>, mut env: HashMap<Id, Type>) -> Result<()> {
    use ast::*;
    for prior in &block.priors {
        match prior {
            BlockPrior::Let(x, e) => {
                let outputs = type_check_expr(e, &env)?;
                ensure!(outputs == x.iter().count(), "void operation can't be assigned");
                if let Some(x) = x {
                    env.insert(*x, Type::Val);
                }
            }

        }
    }

    type_check_expr(&block.tail, &env)?;

    Ok(())
}

pub fn type_check(block: &ast::Block<Id>) -> Result<()> {
    let env = HashMap::new();
    type_check_block(block, env)
}

fn elaborate_val(val: ast::Val<Id>) -> core::Val {
    match val {
        ast::Val::Const(c) => core::Val::Const(c),
        ast::Val::Var(x) => core::Val::Var(x),
    }
}

fn elaborate_expr(expr: ast::Expr<Id>) -> core::Expr {
    match expr {
        ast::Expr::Val(val) => core::Expr::Val(elaborate_val(val)),
        ast::Expr::Op(op, vals) => {
            core::Expr::Op(op, vals.into_iter().map(elaborate_val).collect())
        }
    }
}

pub fn elaborate(block: ast::Block<Id>) -> core::Block {
    let priors = block.priors.into_iter().map(|prior| {
        match prior {
            ast::BlockPrior::Let(x, expr) => {
                core::BlockPrior::Let(x, elaborate_expr(expr))
            }
        }
    }).collect();

    let tail = elaborate_expr(block.tail);

    core::Block { priors, tail }
}

fn resolve_val(val: &ast::Val<&str>, env: &HashMap<&str, Id>) -> Result<ast::Val<Id>> {
    use ast::*;
    Ok(match val {
        Val::Const(c) => Val::Const(*c),
        Val::Var(x) => {
            Val::Var(*env.get(x).with_context(|| format!("unbound variable {x}"))?)
        }
    })
}

fn resolve_expr(expr: &ast::Expr<&str>, env: &HashMap<&str, Id>) -> Result<ast::Expr<Id>> {
    use ast::*;
    Ok(match expr {
        Expr::Val(val) => Expr::Val(resolve_val(val, env)?),
        Expr::Op(op, vals) => {
            let vals = vals.iter().map(|val| resolve_val(val, env)).collect::<Result<_>>()?;
            Expr::Op(*op, vals)
        }
    })
}

fn resolve_block<'a>(
    block: &ast::Block<&'a str>,
    ids: &mut IdGen,
    mut env: HashMap<&'a str, Id>,
) -> Result<ast::Block<Id>> {
    use ast::*;

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
                priors.push(BlockPrior::Let(y, expr));
            }

        }
    }

    let tail = resolve_expr(&block.tail, &env)?;

    Ok(Block { priors, tail })
}

pub fn resolve(block: &ast::Block<&str>) -> Result<ast::Block<Id>> {
    let mut ids = IdGen::new();
    let env = HashMap::new();
    resolve_block(block, &mut ids, env)
}

pub fn parse(source: &str) -> Result<ast::Block<&str>> {
    use chumsky::prelude::*;
    use ast::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Block<&'a str>, extra::Err<Rich<'a, char>>> {
        let val_const = text::digits(10)
            .to_slice()
            .try_map(|digits: &str, span| {
                digits
                    .parse::<U256>()
                    .map_err(|e| Rich::custom(span, e.to_string()))
                    .map(Val::Const)
            });

        let val_var = text::ident()
            .map(|x: &str| Val::Var(x));

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

        let block_let = text::keyword("let")
            .padded()
            .ignore_then(
                choice((
                    just('_').to(None),
                    text::ident().map(Some),
                ))
            )
            .padded()
            .then_ignore(just('='))
            .then(expr.clone())
            .then_ignore(just(';'))
            .map(|(x, e)| BlockPrior::Let(x, e));

        let block = block_let
            .padded()
            .repeated()
            .collect()
            .then(expr)
            .padded()
            .map(|(priors, tail)| Block { priors, tail });

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
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Val(Const(U256::from(42))),
        };
        let code = compile(block);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_op_div() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))]),
        };
        let code = compile(block);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_val() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Val(Const(U256::from(2)))),
            ],
            tail: Op(0x04, vec![Const(U256::from(84)), Var(id!(1))]),
        };
        let code = compile(block);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))])),
            ],
            tail: Val(Var(id!(1))),
        };
        let code = compile(block);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op_reuse() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Val(Const(U256::from(42)))),
            ],
            tail: Op(0x04, vec![Var(id!(1)), Var(id!(1))]),
        };
        let code = compile(block);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(1)]);
    }

    #[test]
    fn test_let_unused() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Val(Const(U256::from(100)))),
                Let(Some(id!(2)), Val(Const(U256::from(100)))),
            ],
            tail: Val(Const(U256::from(42))),
        };
        let code = compile(block);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_type_check_div_ok() {
        use super::ast::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))]),
        };
        assert!(type_check(&block).is_ok());
    }

    #[test]
    fn test_type_check_div_err() {
        use super::ast::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84))]),
        };
        assert!(type_check(&block).is_err());
    }

    #[test]
    fn test_type_check_pop_err() {
        use super::ast::{Block, BlockPrior::*, Expr::*, Val::*};
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Op(0x50, vec![Const(U256::from(42))])),
            ],
            tail: Val(Const(U256::from(0))),
        };
        assert!(type_check(&block).is_err());
    }
}
