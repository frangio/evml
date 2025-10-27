use std::{env, fs::read_to_string};
use anyhow::{anyhow, Result};
use evml::{parse, compile, run};

fn main() -> Result<()> {
    let script_path = env::args().nth(1).ok_or(anyhow!("missing script argument"))?;
    let source = read_to_string(script_path)?;
    let block = parse(&source)?;
    let code = compile(&block);
    let result = run(&code);

    eprintln!("=== CODE ====");
    for line in code.chunks(32) {
        eprintln!("{}", line.iter().map(|b| format!("{b:02x?}")).collect::<String>());
    }

    eprintln!("=== RESULT ==");
    match result {
        Ok(stack) => eprintln!("Stack: {stack:#?}"),
        Err(error) => eprintln!("Error: {error:?}"),
    }

    Ok(())
}
