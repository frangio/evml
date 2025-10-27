mod runner;

use std::{env, fs::read_to_string};
use anyhow::{anyhow, Result};
use revm::{bytecode::opcode, primitives::U256};
use runner::run;

type Id = String;

enum Val {
    Const(U256),
}

enum Expr {
    Val(Val),
    Op(u8, Vec<Val>),
}

struct Block {
    lets: Vec<(Id, Val)>,
    tail: Expr,
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

fn compile_expr_onto(expr: &Expr, code: &mut Vec<u8>) -> Result<()> {
    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, code)?;
        }

        Expr::Op(op, args) => {
            for arg in args.iter().rev() {
                compile_val_onto(arg, code)?;
            }
            code.push(*op);
        }
    }
    Ok(())
}

fn compile(block: &Block) -> Result<Vec<u8>> {
    let mut code = vec![];
    for let_ in &block.lets {
        compile_val_onto(&let_.1, &mut code)?;
    }
    compile_expr_onto(&block.tail, &mut code)?;
    Ok(code)
}

fn parse(source: &str) -> Result<Block> {
    use chumsky::prelude::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Block, extra::Err<Rich<'a, char>>> {
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

fn main() -> Result<()> {
    let script_path = env::args().nth(1).ok_or(anyhow!("missing script argument"))?;
    let source = read_to_string(script_path)?;
    let block = parse(&source)?;
    let code = compile(&block)?;
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
