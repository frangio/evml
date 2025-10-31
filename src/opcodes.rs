use std::{collections::HashMap, sync::LazyLock};

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

    add(0x01, "ADD", 2, 1);
    add(0x02, "MUL", 2, 1);
    add(0x03, "SUB", 2, 1);
    add(0x04, "DIV", 2, 1);
    add(0x05, "SDIV", 2, 1);
    add(0x06, "MOD", 2, 1);
    add(0x07, "SMOD", 2, 1);
    add(0x08, "ADDMOD", 3, 1);
    add(0x09, "MULMOD", 3, 1);
    add(0x0A, "EXP", 2, 1);
    add(0x0B, "SIGNEXTEND", 2, 1);
    add(0x10, "LT", 2, 1);
    add(0x11, "GT", 2, 1);
    add(0x12, "SLT", 2, 1);
    add(0x13, "SGT", 2, 1);
    add(0x14, "EQ", 2, 1);
    add(0x15, "ISZERO", 1, 1);
    add(0x16, "AND", 2, 1);
    add(0x17, "OR", 2, 1);
    add(0x18, "XOR", 2, 1);
    add(0x19, "NOT", 1, 1);
    add(0x1A, "BYTE", 2, 1);
    add(0x1B, "SHL", 2, 1);
    add(0x1C, "SHR", 2, 1);
    add(0x1D, "SAR", 2, 1);
    add(0x20, "KECCAK256", 2, 1);
    add(0x30, "ADDRESS", 0, 1);
    add(0x31, "BALANCE", 1, 1);
    add(0x32, "ORIGIN", 0, 1);
    add(0x33, "CALLER", 0, 1);
    add(0x34, "CALLVALUE", 0, 1);
    add(0x35, "CALLDATALOAD", 1, 1);
    add(0x36, "CALLDATASIZE", 0, 1);
    add(0x37, "CALLDATACOPY", 3, 0);
    add(0x38, "CODESIZE", 0, 1);
    add(0x39, "CODECOPY", 3, 0);
    add(0x3A, "GASPRICE", 0, 1);
    add(0x3B, "EXTCODESIZE", 1, 1);
    add(0x3C, "EXTCODECOPY", 4, 0);
    add(0x3D, "RETURNDATASIZE", 0, 1);
    add(0x3E, "RETURNDATACOPY", 3, 0);
    add(0x3F, "EXTCODEHASH", 1, 1);
    add(0x40, "BLOCKHASH", 1, 1);
    add(0x41, "COINBASE", 0, 1);
    add(0x42, "TIMESTAMP", 0, 1);
    add(0x43, "NUMBER", 0, 1);
    add(0x44, "DIFFICULTY", 0, 1);
    add(0x45, "GASLIMIT", 0, 1);
    add(0x46, "CHAINID", 0, 1);
    add(0x47, "SELFBALANCE", 0, 1);
    add(0x48, "BASEFEE", 0, 1);
    add(0x49, "BLOBHASH", 1, 1);
    add(0x4A, "BLOBBASEFEE", 0, 1);
    add(0x50, "POP", 1, 0);
    add(0x51, "MLOAD", 1, 1);
    add(0x52, "MSTORE", 2, 0);
    add(0x53, "MSTORE8", 2, 0);
    add(0x54, "SLOAD", 1, 1);
    add(0x55, "SSTORE", 2, 0);
    add(0x58, "PC", 0, 1);
    add(0x59, "MSIZE", 0, 1);
    add(0x5A, "GAS", 0, 1);
    add(0x5B, "JUMPDEST", 0, 0);
    add(0x5C, "TLOAD", 1, 1);
    add(0x5D, "TSTORE", 2, 0);
    add(0x5E, "MCOPY", 3, 0);
    add(0xA0, "LOG0", 2, 0);
    add(0xA1, "LOG1", 3, 0);
    add(0xA2, "LOG2", 4, 0);
    add(0xA3, "LOG3", 5, 0);
    add(0xA4, "LOG4", 6, 0);
    add(0xF0, "CREATE", 3, 1);
    add(0xF1, "CALL", 7, 1);
    add(0xF2, "CALLCODE", 7, 1);
    add(0xF4, "DELEGATECALL", 6, 1);
    add(0xF5, "CREATE2", 4, 1);
    add(0xF7, "RETURNDATALOAD", 1, 1);
    add(0xFA, "STATICCALL", 6, 1);

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
