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
    let c: U256 = source.trim().parse()?;
    Ok(Expr::Const(c))
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
