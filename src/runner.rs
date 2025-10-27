use std::fmt::Debug;

use anyhow::Result;
use revm::context::tx::TxEnvBuilder;
use revm::handler::instructions::EthInstructions;
use revm::handler::{EthFrame, EthPrecompiles};
use revm::interpreter::interpreter::EthInterpreter;
use revm::interpreter::interpreter_types::LoopControl;
use revm::interpreter::{InstructionResult, Interpreter};
use revm::primitives::{Bytes, U256};
use revm::{Context, InspectEvm, Inspector, MainContext};

type Evm<INSP = ()> = revm::context::Evm<Context, INSP, EthInstructions<EthInterpreter, Context>, EthPrecompiles, EthFrame>;

struct StackInspector(Option<(InstructionResult, Vec<U256>)>);

impl<CTX> Inspector<CTX> for StackInspector {
    fn step_end(&mut self, interp: &mut Interpreter, _context: &mut CTX) {
        if interp.bytecode.is_end() {
            let result = interp.bytecode.instruction_result().unwrap();
            let stack = std::mem::take(&mut interp.stack).into_data();
            self.0 = Some((result, stack));
        }
    }
}

pub fn run(code: &[u8]) -> Result<(impl Debug + use<>, Vec<U256>)> {
    let mut evm = Evm::new_with_inspector(
        Context::mainnet(),
        StackInspector(None),
        EthInstructions::default(),
        EthPrecompiles::default(),
    );

    let tx = TxEnvBuilder::new()
        .create()
        .data(Bytes::copy_from_slice(code))
        .build_fill();

    evm.inspect_one_tx(tx)?;

    Ok(evm.inspector.0.expect("execution did not stop"))
}
