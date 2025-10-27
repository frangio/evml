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
    Op(u8, Vec<Val>),
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

        Expr::Op(op, args) => {
            for arg in args.iter().rev() {
                compile_val_onto(arg, &mut code)?;
            }
            code.push(*op);
        }
    }

    Ok(code)
}

fn parse(source: &str) -> Result<Expr> {
    use chumsky::prelude::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Expr, extra::Err<Rich<'a, char>>> {
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

        expr.padded().then_ignore(end())
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
    let (result, stack) = run(&code)?;

    eprintln!("=== CODE ====");
    for line in code.chunks(32) {
        eprintln!("{}", line.iter().map(|b| format!("{b:02x?}")).collect::<String>());
    }
    eprintln!("=== RESULT ==");
    eprintln!("{result:#?}");
    eprintln!("=== STACK ===");
    eprintln!("{stack:#?}");

    Ok(())
}
