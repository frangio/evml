use evml::{compile_from_source, run};
use revm::{
    bytecode::Bytecode,
    primitives::{Bytes, U256},
};
use std::{fs, path::PathBuf};

fn disasm(code: &[u8]) -> String {
    let bytecode = Bytecode::new_legacy(Bytes::copy_from_slice(code));
    let mut iter = bytecode.iter_opcodes();
    let mut asm = Vec::new();

    while let pos = iter.position() && pos < code.len() {
        let opcode = iter.peek_opcode().unwrap();
        let name = opcode.as_str();
        let imm = opcode.info().immediate_size() as usize;

        let mut instr = String::new();
        if name == "JUMPDEST" {
            instr.push_str(&format!("[{pos}:] "));
        }
        instr.push_str(name);
        if imm > 0 {
            let val = U256::from_be_slice(&code[pos + 1..pos + 1 + imm]);
            instr.push(' ');
            instr.push_str(&val.to_string());
        }
        asm.push(instr);

        iter.skip_to_next_opcode();
    }

    asm.join("\n")
}

fn snapshot_example(name: &str, source: &str) {
    let bytecode = compile_from_source(source).unwrap();
    let stack = run(&bytecode).unwrap();

    insta::assert_snapshot!(format!("{name}_assembly"), disasm(&bytecode));
    insta::assert_yaml_snapshot!(format!("{name}_stack"), stack);
}

fn example_paths() -> Vec<PathBuf> {
    let mut paths = fs::read_dir("examples")
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "ev"))
        .collect::<Vec<_>>();
    paths.sort();
    paths
}

#[test]
fn snapshot_examples() {
    for path in example_paths() {
        let name = path.file_stem().unwrap().to_str().unwrap();
        let source = fs::read_to_string(&path).unwrap();
        snapshot_example(name, &source);
    }
}
