mod runner;

use std::{env, fs::read_to_string};

use anyhow::{anyhow, Result};
use revm::{bytecode::opcode, primitives::U256};
use runner::run;

enum Val {
    Const(U256),
}

enum Expr {
    Val(Val),
}

fn compile_val_onto(val: &Val, code: &mut Vec<u8>) -> Result<()> {
    match val {
        Val::Const(c) => {
            code.push(opcode::PUSH32);
            code.extend_from_slice(&c.to_be_bytes::<32>());
        }
    }

    Ok(())
}

fn compile(expr: &Expr) -> Result<Vec<u8>> {
    let mut code = vec![];

    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, &mut code)?;
        }
    }

    Ok(code)
}

fn parse(source: &str) -> Result<Expr> {
    use chumsky::prelude::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Expr, extra::Err<Rich<'a, char>>> {
        let val = text::int(10)
            .try_map(|digits: &str, span| {
                digits
                    .parse::<U256>()
                    .map(Val::Const)
                    .map_err(|e| Rich::custom(span, e.to_string()))
            })
            .padded();

        let expr = val.map(Expr::Val);

        expr.then_ignore(end())
    }

    let e = parser()
        .parse(source)
        .into_result()
        .map_err(|es| anyhow!(es[0].to_string()))?;

    Ok(e)
}

fn main() -> Result<()> {
    let script_path = env::args().nth(1).ok_or(anyhow!("missing script argument"))?;
    let source = read_to_string(script_path)?;
    let expr = parse(&source)?;
    let code = compile(&expr)?;
    let stack = run(&code)?;
    dbg!(stack);
    Ok(())
}
