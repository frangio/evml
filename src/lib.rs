mod runner;

use std::collections::HashMap;

use anyhow::{anyhow, Context, Result};
use revm::{bytecode::opcode, primitives::U256};
pub use runner::run;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Id(usize);

#[derive(Clone)]
pub enum Val<Id> {
    Const(U256),
    Var(Id),
}

#[derive(Clone)]
pub enum Expr<Id> {
    Val(Val<Id>),
    Op(u8, Vec<Val<Id>>),
}

pub struct Block<Id> {
    lets: Vec<(Id, Expr<Id>)>,
    tail: Expr<Id>,
}

struct Stack(Vec<Option<Id>>);

impl Stack {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn truncate(&mut self, size: usize) {
        self.0.truncate(size);
    }

    fn push(&mut self, x: Option<Id>) {
        self.0.push(x);
    }

    fn position(&self, x: Id) -> usize {
        let pos = self.0.iter().rposition(|&y| y == Some(x)).expect("unknown variable");
        self.0.len() - 1 - pos
    }
}

fn compile_val_onto(val: &Val<Id>, stack: &mut Stack, code: &mut Vec<u8>) {
    match val {
        Val::Const(c) => {
            code.push(opcode::PUSH32);
            code.extend_from_slice(&c.to_be_bytes::<32>());
        }

        Val::Var(x) => {
            let depth = stack.position(*x);
            code.push(opcode::DUP1 + u8::try_from(depth).expect("stack too deep"));
        }
    }
}

fn compile_expr_onto(expr: &Expr<Id>, stack: &mut Stack, code: &mut Vec<u8>) {
    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, stack, code);
        }

        Expr::Op(op, args) => {
            let size = stack.len();
            for arg in args.iter().rev() {
                compile_val_onto(arg, stack, code);
                stack.push(None);
            }
            stack.truncate(size);
            code.push(*op);
        }
    }
}

pub fn compile(block: &Block<Id>) -> Vec<u8> {
    let mut stack = Stack::new();
    let mut code = vec![];
    for (x, v) in &block.lets {
        compile_expr_onto(v, &mut stack, &mut code);
        stack.push(Some(*x));
    }
    compile_expr_onto(&block.tail, &mut stack, &mut code);
    code
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
        assert_eq!(stack, vec![U256::from(2), U256::from(42)]);
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
        assert_eq!(stack, vec![U256::from(42); 2]);
    }
}
