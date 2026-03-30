use std::{collections::HashMap, sync::LazyLock};

pub const MLOAD: u8 = 0x51;
pub const MSTORE: u8 = 0x52;
pub const STOP: u8 = 0x00;
pub const JUMP: u8 = 0x56;
pub const JUMPI: u8 = 0x57;
pub const POP: u8 = 0x50;
pub const JUMPDEST: u8 = 0x5b;
pub const PUSH0: u8 = 0x5f;
pub const PUSH2: u8 = 0x61;
pub const DUP1: u8 = 0x80;
pub const SWAP1: u8 = 0x90;

#[derive(Clone, Copy)]
pub struct OpcodeInfo<N = u8> {
    pub inputs: N,
    pub outputs: N,
}

struct OpcodeData {
    info: [Option<OpcodeInfo>; 256],
    by_name: HashMap<&'static str, u8>,
}

static OPCODE_DATA: LazyLock<OpcodeData> = LazyLock::new(|| {
    let mut data = OpcodeData {
        info: [None; 256],
        by_name: HashMap::new(),
    };

    let mut add = |opcode, name, inputs, outputs| {
        data.info[opcode as usize] = Some(OpcodeInfo { inputs, outputs });
        data.by_name.insert(name, opcode);
    };

    add(0x01, "add", 2, 1);
    add(0x02, "mul", 2, 1);
    add(0x03, "sub", 2, 1);
    add(0x04, "div", 2, 1);
    add(0x05, "sdiv", 2, 1);
    add(0x06, "mod", 2, 1);
    add(0x07, "smod", 2, 1);
    add(0x08, "addmod", 3, 1);
    add(0x09, "mulmod", 3, 1);
    add(0x0A, "exp", 2, 1);
    add(0x0B, "signextend", 2, 1);
    add(0x10, "lt", 2, 1);
    add(0x11, "gt", 2, 1);
    add(0x12, "slt", 2, 1);
    add(0x13, "sgt", 2, 1);
    add(0x14, "eq", 2, 1);
    add(0x15, "iszero", 1, 1);
    add(0x16, "and", 2, 1);
    add(0x17, "or", 2, 1);
    add(0x18, "xor", 2, 1);
    add(0x19, "not", 1, 1);
    add(0x1A, "byte", 2, 1);
    add(0x1B, "shl", 2, 1);
    add(0x1C, "shr", 2, 1);
    add(0x1D, "sar", 2, 1);
    add(0x20, "keccak256", 2, 1);
    add(0x30, "address", 0, 1);
    add(0x31, "balance", 1, 1);
    add(0x32, "origin", 0, 1);
    add(0x33, "caller", 0, 1);
    add(0x34, "callvalue", 0, 1);
    add(0x35, "calldataload", 1, 1);
    add(0x36, "calldatasize", 0, 1);
    add(0x37, "calldatacopy", 3, 0);
    add(0x38, "codesize", 0, 1);
    add(0x39, "codecopy", 3, 0);
    add(0x3A, "gasprice", 0, 1);
    add(0x3B, "extcodesize", 1, 1);
    add(0x3C, "extcodecopy", 4, 0);
    add(0x3D, "returndatasize", 0, 1);
    add(0x3E, "returndatacopy", 3, 0);
    add(0x3F, "extcodehash", 1, 1);
    add(0x40, "blockhash", 1, 1);
    add(0x41, "coinbase", 0, 1);
    add(0x42, "timestamp", 0, 1);
    add(0x43, "number", 0, 1);
    add(0x44, "difficulty", 0, 1);
    add(0x45, "gaslimit", 0, 1);
    add(0x46, "chainid", 0, 1);
    add(0x47, "selfbalance", 0, 1);
    add(0x48, "basefee", 0, 1);
    add(0x49, "blobhash", 1, 1);
    add(0x4A, "blobbasefee", 0, 1);
    add(0x50, "pop", 1, 0);
    add(0x51, "mload", 1, 1);
    add(0x52, "mstore", 2, 0);
    add(0x53, "mstore8", 2, 0);
    add(0x54, "sload", 1, 1);
    add(0x55, "sstore", 2, 0);
    add(0x58, "pc", 0, 1);
    add(0x59, "msize", 0, 1);
    add(0x5A, "gas", 0, 1);
    add(0x5B, "jumpdest", 0, 0);
    add(0x5C, "tload", 1, 1);
    add(0x5D, "tstore", 2, 0);
    add(0x5E, "mcopy", 3, 0);
    add(0xA0, "log0", 2, 0);
    add(0xA1, "log1", 3, 0);
    add(0xA2, "log2", 4, 0);
    add(0xA3, "log3", 5, 0);
    add(0xA4, "log4", 6, 0);
    add(0xF0, "create", 3, 1);
    add(0xF1, "call", 7, 1);
    add(0xF2, "callcode", 7, 1);
    add(0xF4, "delegatecall", 6, 1);
    add(0xF5, "create2", 4, 1);
    add(0xF7, "returndataload", 1, 1);
    add(0xFA, "staticcall", 6, 1);

    add(0x00, "stop", 0, 0);

    data
});

pub fn info(opcode: u8) -> Option<OpcodeInfo<usize>> {
    OPCODE_DATA.info[opcode as usize].map(|info| {
        OpcodeInfo {
            inputs: usize::from(info.inputs),
            outputs: usize::from(info.outputs),
        }
    })
}

pub fn lookup(name: &str) -> Option<u8> {
    OPCODE_DATA.by_name.get(name).copied()
}
