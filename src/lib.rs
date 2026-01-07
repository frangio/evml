mod runner;
mod opcodes;
mod graph;
mod analysis;
mod parse;
mod resolve;
mod type_check;
mod lower;
mod compile;
mod assemble;
mod utils;
mod id;

pub use parse::parse;
pub use resolve::resolve;
pub use runner::run;
pub use type_check::type_check;
pub use lower::lower;
pub use compile::compile;
pub use assemble::assemble;
pub use id::{Id, IdGen};

use anyhow::Result;
use revm::primitives::U256;

pub mod ast {
    use crate::U256;

    pub enum Val<T> {
        Const(U256),
        Var(T),
    }

    pub enum Expr<T> {
        Unit,
        Val(Val<T>),
        Op(u8, Vec<Val<T>>),
        Apply(T, Vec<Val<T>>),
        IfThenElse(Box<(Expr<T>, [Block<T>; 2])>),
    }

    pub enum BlockPrior<T> {
        Let(Option<T>, Expr<T>),
    }

    pub struct Block<T> {
        pub priors: Vec<BlockPrior<T>>,
        pub tail: Expr<T>,
    }

    pub struct Proc<T> {
        pub args: Vec<T>,
        pub rets: usize,
        pub body: Block<T>,
    }

    pub struct Program<T> {
        pub procs: Vec<(T, Proc<T>)>,
    }
}

pub mod core {
    use crate::{Id, U256};

    #[derive(PartialEq, Eq, Debug)]
    pub enum Val {
        Const(U256),
        Var(Id),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub enum Expr {
        Unit,
        Val(Val),
        Op(u8, Vec<Val>),
        Apply(Id, Vec<Val>),
        IfThenElse(Id, Box<[Block; 2]>),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub enum TailExpr {
        Unit,
        Var(Id),
        Apply(Id, Vec<Val>),
        IfThenElse(Id, Box<[Block; 2]>),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub enum BlockPrior {
        Let(Option<Id>, Expr),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub struct Block {
        pub priors: Vec<BlockPrior>,
        pub tail: TailExpr,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub struct Proc {
        pub args: Vec<Id>,
        pub rets: usize,
        pub body: Block,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub struct Program {
        pub main: Block,
        pub rets: usize,
        pub procs: Vec<(Id, Proc)>,
    }

    impl Default for Val {
        fn default() -> Self {
            Val::Const(Default::default())
        }
    }

    impl Default for Expr {
        fn default() -> Self {
            Expr::Val(Default::default())
        }
    }

    impl Default for BlockPrior {
        fn default() -> Self {
            BlockPrior::Let(None, Default::default())
        }
    }
}

pub mod asm {
    use crate::{Id, U256};

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Instr {
        Pop,
        Push(U256),
        Swap(usize),
        Dup(usize),
        Op(u8),
        JumpDest(Id),
        PushLabel(Id),
        JumpIf,
        Jump,
        Stop,
    }
}

pub fn compile_from_source(source: &str) -> Result<Vec<u8>> {
    let mut ids = IdGen::new();
    let ast = parse(source)?;
    let ast = resolve(&ast, &mut ids)?;
    type_check(&ast)?;
    let ir = lower(ast, &mut ids);
    let code = compile(ir, &mut ids);
    Ok(assemble(&code))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_e2e_result(result: U256, source: &str) {
        let bytecode = compile_from_source(source).unwrap();
        let stack = run(&bytecode).expect("execution failed");
        assert_eq!(stack, vec![result]);
    }

    #[test]
    fn test_e2e_const() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                42
            }
        "#);
    }

    #[test]
    fn test_e2e_op_div() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                @div(84, 2)
            }
        "#);
    }

    #[test]
    fn test_e2e_let_val() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                let x = 2;
                @div(84, x)
            }
        "#);
    }

    #[test]
    fn test_e2e_let_op() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                let x = @div(84, 2);
                x
            }
        "#);
    }

    #[test]
    fn test_e2e_let_op_reuse() {
        assert_e2e_result(U256::from(1), r#"
            fn main() -> u256 {
                let x = 42;
                @div(x, x)
            }
        "#);
    }

    #[test]
    fn test_e2e_let_unused() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                let x = 100;
                let y = 100;
                42
            }
        "#);
    }
}
