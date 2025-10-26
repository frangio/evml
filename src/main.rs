mod runner;

use std::{env, fs::read_to_string};

use anyhow::{Error, Result};
use revm::{bytecode::opcode, primitives::U256};
use runner::run;

enum Expr {
    Const(U256),
}

fn compile(expr: &Expr) -> Result<Vec<u8>> {
    match expr {
        Expr::Const(c) => {
            let mut code = vec![opcode::PUSH32];
            code.extend_from_slice(&c.to_be_bytes::<32>());
            Ok(code)
        }
    }
}

fn parse(source: &str) -> Result<Expr> {
    use chumsky::prelude::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Expr> {
        text::int(10).try_map(|n: &'a str, _|
            Ok(Expr::Val(Val::Const(n.parse().map_err(|_| EmptyErr::default())?)))
        ).padded().then_ignore(end())
    }

    let e = parser()
        .parse(source)
        .into_result()
        .map_err(|es| Error::msg("parsing failed").context(es[0]))?;

    Ok(e)
}

fn main() -> Result<()> {
    let script_path = env::args().nth(1).ok_or(Error::msg("missing script argument"))?;
    let source = read_to_string(script_path)?;
    let expr = parse(&source)?;
    let code = compile(&expr)?;
    let stack = run(&code)?;
    dbg!(stack);
    Ok(())
}
