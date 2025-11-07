mod runner;
mod opcodes;

use std::{collections::HashMap, iter::{once, zip}, num::NonZeroUsize};

use anyhow::{anyhow, bail, ensure, Context, Result};
use revm::{bytecode::opcode, primitives::U256};
pub use runner::run;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id(NonZeroUsize);

struct IdGen(NonZeroUsize);

impl IdGen {
    fn new() -> IdGen {
        IdGen(NonZeroUsize::MIN)
    }

    fn generate(&mut self) -> Id {
        let id = Id(self.0);
        self.0 = self.0.checked_add(1).expect("integer overflow");
        id
    }
}

#[derive(PartialEq, Eq)]
pub enum Val<Id> {
    Const(U256),
    Var(Id),
}

pub enum Expr<Id> {
    Val(Val<Id>),
    Op(u8, Vec<Val<Id>>),
}

pub enum BlockPrior<Id> {
    Let(Option<Id>, Expr<Id>),
}

pub struct Block<Id> {
    priors: Vec<BlockPrior<Id>>,
    tail: Expr<Id>,
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
    val: &Val<Id>,
    stack: &mut Stack,
    should_swap: impl Fn(&StackEntry) -> bool,
    code: &mut Vec<u8>,
) {
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
    expr: &Expr<Id>,
    stack: &mut Stack,
    is_last_use: impl Fn(Id) -> bool,
    code: &mut Vec<u8>,
) {
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

pub fn compile(block: &Block<Id>) -> Vec<u8> {
    let liveness = analyze_liveness(block);
    let mut stack = Stack::new();
    let mut code = vec![];

    for (prior, is_last_use) in zip(&block.priors, liveness.iter()) {
        match prior {
            BlockPrior::Let(x, e) => {
                compile_expr_onto(e, &mut stack, is_last_use, &mut code);
                if let Some(x) = x {
                    stack.push(Some(*x));
                }
            }
        }
    }

    compile_expr_onto(&block.tail, &mut stack, |_| true, &mut code);

    let excess = stack.len();
    if excess > 0 {
        let ret = type_check_expr(&block.tail).expect("type error");
        for _ in 0..ret {
            code.push(opcode_swap(excess));
            code.push(opcode::POP);
        }
        if excess > ret {
            code.resize(code.len() + excess - ret, opcode::POP);
        }
    }

    code
}

struct BlockLiveness {
    last_use: Vec<(Id, usize)>,
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

fn analyze_liveness_expr(expr: &Expr<Id>, block_pos: usize, last_use: &mut HashMap<Id, usize>) {
    let mut analyze_val = |val| {
        if let &Val::Var(x) = val {
            last_use.insert(x, block_pos).expect("unbound variable");
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

fn analyze_liveness(block: &Block<Id>) -> BlockLiveness {
    let mut last_use: HashMap<Id, usize> = HashMap::new();

    for (block_pos, prior) in block.priors.iter().enumerate() {
        match prior {
            BlockPrior::Let(x, expr) => {
                if let Some(x) = x {
                    last_use.insert(*x, block_pos);
                }
                analyze_liveness_expr(expr, block_pos, &mut last_use);
            }
        }
    }

    analyze_liveness_expr(&block.tail, block.priors.len(), &mut last_use);

    let mut last_use = Vec::from_iter(last_use);
    last_use.sort_unstable_by(|(_, i), (_, j)| i.cmp(j));

    BlockLiveness { last_use }
}

fn type_check_expr(expr: &Expr<Id>) -> Result<usize> {
    match expr {
        Expr::Val(_) => Ok(1),
        Expr::Op(op, args) => {
            let Some(info) = opcodes::info(*op) else { bail!("unknown opcode {op:#04x?}") };
            ensure!(args.len() == info.inputs);
            Ok(info.outputs)
        }
    }
}

pub fn type_check(block: &Block<Id>) -> Result<()> {
    for prior in &block.priors {
        match prior {
            BlockPrior::Let(x, e) => {
                let outputs = type_check_expr(e)?;
                ensure!(outputs == x.iter().count(), "void operation can't be assigned");
            }
        }
    }
    type_check_expr(&block.tail)?;
    Ok(())
}

fn resolve_val(val: &Val<String>, env: &HashMap<&String, Id>) -> Result<Val<Id>> {
    Ok(match val {
        Val::Const(c) => Val::Const(*c),
        Val::Var(x) => {
            Val::Var(*env.get(x).with_context(|| format!("unbound variable {x}"))?)
        }
    })
}

fn resolve_expr(expr: &Expr<String>, env: &HashMap<&String, Id>) -> Result<Expr<Id>> {
    Ok(match expr {
        Expr::Val(val) => Expr::Val(resolve_val(val, env)?),
        Expr::Op(op, vals) => {
            let vals = vals.iter().map(|val| resolve_val(val, env)).collect::<Result<_>>()?;
            Expr::Op(*op, vals)
        }
    })
}

pub fn resolve(block: &Block<String>) -> Result<Block<Id>> {
    let mut env: HashMap<&String, Id> = HashMap::new();

    let mut ids = IdGen::new();
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

pub fn parse(source: &str) -> Result<Block<String>> {
    use chumsky::prelude::*;

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

        let block_let = text::keyword("let")
            .ignore_then(text::whitespace())
            .ignore_then(
                choice((
                    just('_').to(None),
                    text::ident().map(|id: &str| Some(id.to_owned())),
                ))
            )
            .then_ignore(text::whitespace())
            .then_ignore(just('='))
            .then(expr)
            .then_ignore(just(';'));

        let block = block_let
            .padded()
            .map(|(x, e)| BlockPrior::Let(x, e))
            .repeated()
            .collect()
            .then(expr)
            .map(|(priors, tail)| Block { priors, tail });

        block.padded().then_ignore(end())
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
    use super::{BlockPrior::*, Expr::*, Val::*};

    macro_rules! id {
        ($n:expr) => { Id(::std::num::NonZeroUsize::new($n).unwrap()) }
    }

    #[test]
    fn test_const() {
        let block = Block {
            priors: vec![],
            tail: Val(Const(U256::from(42))),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_op_div() {
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))]),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_val() {
        let block = Block {
            priors: vec![
                Let(Some(id!(1)), Val(Const(U256::from(2)))),
            ],
            tail: Op(0x04, vec![Const(U256::from(84)), Var(id!(1))]),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op() {
        let block = Block {
            priors: vec![
                BlockPrior::Let(Some(id!(1)), Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))])),
            ],
            tail: Val(Var(id!(1))),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op_reuse() {
        let block = Block {
            priors: vec![
                BlockPrior::Let(Some(id!(1)), Val(Const(U256::from(42)))),
            ],
            tail: Op(0x04, vec![Var(id!(1)), Var(id!(1))]),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(1)]);
    }

    #[test]
    fn test_let_unused() {
        let block = Block {
            priors: vec![
                BlockPrior::Let(Some(id!(1)), Val(Const(U256::from(100)))),
                BlockPrior::Let(Some(id!(2)), Val(Const(U256::from(100)))),
            ],
            tail: Val(Const(U256::from(42))),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_type_check_div_ok() {
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))]),
        };
        assert!(type_check(&block).is_ok());
    }

    #[test]
    fn test_type_check_div_err() {
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84))]),
        };
        assert!(type_check(&block).is_err());
    }

    #[test]
    fn test_type_check_pop_err() {
        let block = Block {
            priors: vec![
                BlockPrior::Let(Some(id!(1)), Op(0x50, vec![Const(U256::from(42))])),
            ],
            tail: Val(Const(U256::from(0))),
        };
        assert!(type_check(&block).is_err());
    }
}
