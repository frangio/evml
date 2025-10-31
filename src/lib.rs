mod runner;
mod opcodes;

use std::collections::HashMap;

use anyhow::{anyhow, bail, ensure, Context, Result};
use revm::{bytecode::opcode, primitives::U256};
pub use runner::run;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id(usize);

pub enum Val<Id> {
    Const(U256),
    Var(Id),
}

pub enum Expr<Id> {
    Val(Val<Id>),
    Op(u8, Vec<Val<Id>>),
}

pub struct Block<Id> {
    lets: Vec<(Id, Expr<Id>)>,
    tail: Expr<Id>,
}

struct Stack(Vec<Option<(Id, usize)>>);
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
        let mut removed = self.0.drain(self.0.len() - count..);
        assert!(removed.all(|x| x.is_none_or(|x| x.1 == 0)));
    }

    fn push(&mut self, x: Option<(Id, usize)>) {
        self.0.push(x);
    }

    fn swap(&mut self, depth: usize) {
        let top = self.0.len() - 1;
        let index = top - depth;
        self.0.swap(index, top);
    }

    fn entry(&mut self, x: Id) -> StackEntry<'_> {
        let index = self.0.iter()
            .rposition(|y| y.as_ref().is_some_and(|y| y.0 == x))
            .expect("unknown variable");
        StackEntry { stack: self, index }
    }
}

impl StackEntry<'_> {
    fn occurs(&mut self) -> &mut usize {
        let item = &mut self.stack.0[self.index];
        let item = item.as_mut().expect("stack item is temporary");
        &mut item.1
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

fn compile_val_onto(val: &Val<Id>, stack: &mut Stack, code: &mut Vec<u8>) {
    match val {
        Val::Const(c) => {
            code.push(opcode::PUSH32);
            code.extend_from_slice(&c.to_be_bytes::<32>());
        }

        Val::Var(x) => {
            let mut entry = stack.entry(*x);
            let depth = entry.depth();
            let occurs = entry.occurs();
            *occurs -= 1;
            if *occurs > 0 {
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

fn compile_expr_onto(expr: &Expr<Id>, stack: &mut Stack, code: &mut Vec<u8>) {
    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, stack, code);
        }

        Expr::Op(op, args) => {
            let mut seen_counts = HashMap::with_capacity(args.len());
            let stack_delta = args.iter().filter(|v| {
                match v {
                    Val::Const(_) => true,
                    Val::Var(x) => {
                        let seen_count = seen_counts.entry(*x).or_insert(0);
                        *seen_count += 1;
                        *stack.entry(*x).occurs() > *seen_count
                    }
                }
            }).count();
            let target_stack_len = stack.len() + stack_delta;

            for (i, arg) in args.iter().enumerate().rev() {
                compile_val_onto(arg, stack, code);
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

fn count_occurs_val(val: &Val<Id>, counts: &mut HashMap<Id, usize>) {
    if let Val::Var(x) = val {
        let x_count = counts.get_mut(x).expect("variable not found");
        *x_count += 1;
    }
}

fn count_occurs_expr(expr: &Expr<Id>, counts: &mut HashMap<Id, usize>) {
    match expr {
        Expr::Val(val) => count_occurs_val(val, counts),
        Expr::Op(_, args) => {
            for arg in args {
                count_occurs_val(arg, counts);
            }
        }
    }
}

fn count_occurs(block: &Block<Id>) -> HashMap<Id, usize> {
    let mut counts = HashMap::new();
    for (x, expr) in &block.lets {
        counts.insert(*x, 0);
        count_occurs_expr(expr, &mut counts);
    }
    count_occurs_expr(&block.tail, &mut counts);
    counts
}

pub fn compile(block: &Block<Id>) -> Vec<u8> {
    let counts = count_occurs(block);
    let mut stack = Stack::new();
    let mut code = vec![];
    for (x, e) in &block.lets {
        compile_expr_onto(e, &mut stack, &mut code);
        let x_count = *counts.get(x).expect("variable not found");
        if x_count > 0 {
            stack.push(Some((*x, x_count)));
        } else {
            code.push(opcode::POP);
        }
    }
    compile_expr_onto(&block.tail, &mut stack, &mut code);
    code
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
    for (_, e) in &block.lets {
        let outputs = type_check_expr(e)?;
        ensure!(outputs == 1, "void operation can't be assigned");
    }
    type_check_expr(&block.tail)?;
    Ok(())
}

fn resolve_val(val: &Val<String>, env: &HashMap<String, Id>) -> Result<Val<Id>> {
    Ok(match val {
        Val::Const(c) => Val::Const(*c),
        Val::Var(x) => {
            Val::Var(*env.get(x).with_context(|| format!("unbound variable {x}"))?)
        }
    })
}

fn resolve_expr(expr: &Expr<String>, env: &HashMap<String, Id>) -> Result<Expr<Id>> {
    Ok(match expr {
        Expr::Val(val) => Expr::Val(resolve_val(val, env)?),
        Expr::Op(op, vals) => {
            let vals = vals.iter().map(|val| resolve_val(val, env)).collect::<Result<_>>()?;
            Expr::Op(*op, vals)
        }
    })
}

pub fn resolve(block: &Block<String>) -> Result<Block<Id>> {
    let mut next_id = 0;
    let mut env: HashMap<String, Id> = HashMap::new();

    let mut lets = Vec::with_capacity(block.lets.len());

    for (x, expr) in &block.lets {
        let expr = resolve_expr(expr, &env)?;

        let y = Id(next_id);
        next_id += 1;

        env.insert(x.clone(), y);

        lets.push((y, expr));
    }

    let tail = resolve_expr(&block.tail, &env)?;

    Ok(Block { lets, tail })
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
            .ignore_then(text::digits(16).to_slice())
            .try_map(|digits: &str, span| {
                u8::from_str_radix(digits, 16)
                    .map_err(|e| Rich::custom(span, e.to_string()))
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
            .ignore_then(text::ident().map(ToOwned::to_owned))
            .then_ignore(text::whitespace())
            .then_ignore(just('='))
            .then(expr)
            .then_ignore(just(';'));

        let block = block_let
            .padded()
            .repeated()
            .collect()
            .then(expr)
            .map(|(lets, tail)| Block { lets, tail });

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

    #[test]
    fn test_const() {
        let block = Block {
            lets: vec![],
            tail: Expr::Val(Val::Const(U256::from(42))),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_op_div() {
        let block = Block {
            lets: vec![],
            tail: Expr::Op(0x04, vec![Val::Const(U256::from(84)), Val::Const(U256::from(2))]),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_val() {
        let block = Block {
            lets: vec![
                (Id(0), Expr::Val(Val::Const(U256::from(2)))),
            ],
            tail: Expr::Op(0x04, vec![Val::Const(U256::from(84)), Val::Var(Id(0))]),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op() {
        let block = Block {
            lets: vec![
                (Id(0), Expr::Op(0x04, vec![Val::Const(U256::from(84)), Val::Const(U256::from(2))])),
            ],
            tail: Expr::Val(Val::Var(Id(0))),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op_reuse() {
        let block = Block {
            lets: vec![
                (Id(0), Expr::Val(Val::Const(U256::from(42)))),
            ],
            tail: Expr::Op(0x04, vec![Val::Var(Id(0)), Val::Var(Id(0))]),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(1)]);
    }

    #[test]
    fn test_let_unused() {
        let block = Block {
            lets: vec![
                (Id(0), Expr::Val(Val::Const(U256::from(100)))),
            ],
            tail: Expr::Val(Val::Const(U256::from(42))),
        };
        let bytecode = compile(&block);
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_type_check_div_ok() {
        let block = Block {
            lets: vec![],
            tail: Expr::Op(0x04, vec![Val::Const(U256::from(84)), Val::Const(U256::from(2))]),
        };
        assert!(type_check(&block).is_ok());
    }

    #[test]
    fn test_type_check_div_err() {
        let block = Block {
            lets: vec![],
            tail: Expr::Op(0x04, vec![Val::Const(U256::from(84))]),
        };
        assert!(type_check(&block).is_err());
    }

    #[test]
    fn test_type_check_pop_err() {
        let block = Block {
            lets: vec![
                (Id(0), Expr::Op(0x50, vec![Val::Const(U256::from(42))])),
            ],
            tail: Expr::Val(Val::Const(U256::from(0))),
        };
        assert!(type_check(&block).is_err());
    }
}
