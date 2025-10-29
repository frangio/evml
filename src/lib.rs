mod runner;

use std::collections::HashMap;

use anyhow::{anyhow, Context, Result};
use revm::{bytecode::opcode, primitives::U256};
pub use runner::run;

#[derive(Clone, Copy)]
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
    lets: Vec<(Id, Val<Id>)>,
    tail: Expr<Id>,
}

fn compile_val_onto(val: &Val<Id>, code: &mut Vec<u8>) {
    match val {
        Val::Const(c) => {
            code.push(opcode::PUSH32);
            code.extend_from_slice(&c.to_be_bytes::<32>());
        }

        Val::Var(_) => todo!(),
    }
}

fn compile_expr_onto(expr: &Expr<Id>, code: &mut Vec<u8>) {
    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, code);
        }

        Expr::Op(op, args) => {
            for arg in args.iter().rev() {
                compile_val_onto(arg, code);
            }
            code.push(*op);
        }
    }
}

pub fn compile(block: &Block<Id>) -> Vec<u8> {
    let mut code = vec![];
    for let_ in &block.lets {
        compile_val_onto(&let_.1, &mut code);
    }
    compile_expr_onto(&block.tail, &mut code);
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

    for (x, val) in &block.lets {
        let val = resolve_val(val, &env)?;

        let y = Id(next_id);
        next_id += 1;

        env.insert(x.clone(), y);

        lets.push((y, val));
    }

    let tail = resolve_expr(&block.tail, &env)?;

    Ok(Block { lets, tail })
}

pub fn parse(source: &str) -> Result<Block<String>> {
    use chumsky::prelude::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Block<String>, extra::Err<Rich<'a, char>>> {
        let val = text::digits(10)
            .to_slice()
            .try_map(|digits: &str, span| {
                digits
                    .parse::<U256>()
                    .map_err(|e| Rich::custom(span, e.to_string()))
                    .map(Val::Const)
            })
            .padded();

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
        ));

        let block_let = text::keyword("let")
            .ignore_then(text::whitespace())
            .ignore_then(text::ident().map(ToOwned::to_owned))
            .then_ignore(text::whitespace())
            .then_ignore(just('='))
            .then(val)
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
}
