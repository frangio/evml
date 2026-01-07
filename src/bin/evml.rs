use std::{env, fs::read_to_string};
use anyhow::{anyhow, Result};
use evml::{compile_from_source, run};
use revm::{bytecode::Bytecode, primitives::{Bytes, U256}};

fn disasm(code: &[u8]) -> String {
    let mut asm = String::new();
    let bytecode = Bytecode::new_legacy(Bytes::copy_from_slice(code));
    let mut iter = bytecode.iter_opcodes();
    while let pos = iter.position() && pos < code.len() {
        let opcode = iter.peek_opcode().unwrap();
        let name = opcode.as_str();
        if name == "JUMPDEST" {
            asm.push_str(&format!("[{pos}:] "));
        }
        asm.push_str(name);
        let imm = opcode.info().immediate_size() as usize;
        if imm > 0 {
            let val = U256::from_be_slice(&code[pos+1..pos+1+imm]);
            asm.push(' ');
            asm.push_str(&val.to_string());
        }
        asm.push(' ');
        iter.skip_to_next_opcode();
    }
    asm
}

fn main() -> Result<()> {
    let script_path = env::args().nth(1).ok_or(anyhow!("missing script argument"))?;
    let source = read_to_string(script_path)?;
    let bytecode = compile_from_source(&source)?;
    let asm = disasm(&bytecode);
    let result = run(&bytecode);

    eprintln!("=== CODE ====");
    eprintln!("{asm}");

    eprintln!("=== RESULT ==");
    match result {
        Ok(stack) => eprintln!("Stack: {stack:#?}"),
        Err(error) => eprintln!("Error: {error:?}"),
    }

    Ok(())
}
