use std::{collections::HashMap, iter::once};
use crate::{asm, id::Id, opcodes, utils::exact_size_chain};

pub fn assemble(code: &[asm::Instr]) -> Vec<u8> {
    use asm::Instr::*;

    const MAX_CODE_SIZE: usize = 24 * 1024;

    let mut label_offsets: HashMap<Id, usize> = HashMap::new();
    let mut pc = 0usize;
    for instr in code {
        match instr {
            JumpDest(id) => {
                if label_offsets.insert(*id, pc).is_some() {
                    panic!("duplicate label");
                }
                pc += 1;
            }
            Push(value) => pc += instruction_push(value.to_be_bytes::<32>()).len(),
            PushLabel(_id) => pc += 3,
            Pop | JumpIf | Jump | Stop | Op(_) | Swap(_) | Dup(_) => pc += 1,
        }
    }
    assert!(pc <= MAX_CODE_SIZE, "bytecode too large");

    let mut bytecode = Vec::with_capacity(code.len());
    for instr in code {
        match instr {
            Pop => bytecode.push(opcodes::POP),
            Push(value) => bytecode.extend(instruction_push(value.to_be_bytes::<32>())),
            Swap(depth) => bytecode.push(opcode_swap(*depth)),
            Dup(depth) => bytecode.push(opcode_dup(*depth)),
            Op(op) => bytecode.push(*op),
            JumpDest(id) => {
                let expected = label_offsets[id];
                assert!(bytecode.len() == expected);
                bytecode.push(opcodes::JUMPDEST);
            }
            PushLabel(id) => {
                let offset = label_offsets[id];
                let offset: u16 = offset.try_into().unwrap();
                bytecode.push(opcodes::PUSH2);
                bytecode.extend(offset.to_be_bytes());
            }
            JumpIf => bytecode.push(opcodes::JUMPI),
            Jump => bytecode.push(opcodes::JUMP),
            Stop => bytecode.push(opcodes::STOP),
        }
    }
    bytecode
}

fn opcode_swap(depth: usize) -> u8 {
    assert!(depth > 0, "can't swap top of stack");
    assert!(depth <= 16, "stack too deep");
    opcodes::SWAP1 + (depth - 1) as u8
}

fn opcode_dup(depth: usize) -> u8 {
    assert!(depth < 16, "stack too deep");
    opcodes::DUP1 + depth as u8
}

fn instruction_push<const N: usize>(value: [u8; N]) -> impl ExactSizeIterator<Item = u8> {
    assert!(N <= 32);
    let mut value = value.into_iter().peekable();
    while value.next_if_eq(&0).is_some() {}
    exact_size_chain(
        once(opcodes::PUSH0 + value.len() as u8),
        value,
    )
}
