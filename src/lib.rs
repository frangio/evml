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
mod stack;
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
        Op(u8, Box<[Val<T>]>),
        Apply(T, Box<[Val<T>]>),
        IfThenElse(Box<(Expr<T>, [Block<T>; 2])>),
    }

    pub struct Block<T> {
        pub priors: Vec<(Option<T>, Expr<T>)>,
        pub tail: Expr<T>,
    }

    pub struct Proc<T> {
        pub args: Box<[T]>,
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
        Op(u8, Box<[Val]>),
        Apply(Id, Box<[Val]>),
        IfThenElse(Id, Box<[Block; 2]>),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub enum TailExpr {
        Unit,
        Var(Id),
        Apply(Id, Box<[Val]>),
        IfThenElse(Id, Box<[Block; 2]>),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub struct Block {
        pub priors: Vec<(Option<Id>, Expr)>,
        pub tail: TailExpr,
    }

    #[derive(PartialEq, Eq, Debug)]
    pub struct Proc {
        pub args: Box<[Id]>,
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

    #[test]
    fn test_e2e_if_else() {
        assert_e2e_result(U256::from(1), r#"
            fn main() -> u256 {
                if 1 { 1 } else { 0 }
            }
        "#);
        assert_e2e_result(U256::from(0), r#"
            fn main() -> u256 {
                if 0 { 1 } else { 0 }
            }
        "#);
    }

    #[test]
    fn test_e2e_if_with_condition_expr() {
        assert_e2e_result(U256::from(10), r#"
            fn main() -> u256 {
                if @gt(5, 3) { 10 } else { 20 }
            }
        "#);
    }

    #[test]
    fn test_e2e_apply() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                double(21)
            }
            fn double(x) -> u256 {
                @mul(x, 2)
            }
        "#);
    }

    #[test]
    fn test_e2e_apply_multiple_args() {
        assert_e2e_result(U256::from(11), r#"
            fn main() -> u256 {
                let x = 7;
                add(3, x, 1)
            }
            fn add(a, b, c) -> u256 {
                let r = @add(a, b);
                @add(r, c)
            }
        "#);
    }

    #[test]
    fn test_e2e_repeated_apply() {
        assert_e2e_result(U256::from(16), r#"
            fn main() -> u256 {
                let x = double(4);
                double(x)
            }
            fn double(x) -> u256 {
                @mul(x, 2)
            }
        "#);
    }

    #[test]
    fn test_e2e_if_with_var_cond() {
        assert_e2e_result(U256::from(1), r#"
            fn main() -> u256 {
                let cond = 1;
                let ret = 1;
                if cond { ret } else { 0 }
            }
        "#);
    }

    #[test]
    fn test_e2e_if_nested() {
        assert_e2e_result(U256::from(11), r#"
            fn main() -> u256 {
                let a = 1;
                let b = 0;
                let c = 10;
                let d = 11;
                let e = 12;
                if a {
                    if b { c } else { d }
                } else {
                    e
                }
            }
        "#);
    }

    #[test]
    fn test_e2e_if_in_apply() {
        assert_e2e_result(U256::from(10), r#"
            fn main() -> u256 {
                choose(1)
            }
            fn choose(x) -> u256 {
                if x { 10 } else { 20 }
            }
        "#);
    }

    #[test]
    fn test_e2e_if_without_else() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                let _ = if 1 {
                    let _ = @mstore(0, 42);
                };
                @mload(0)
            }
        "#);
    }

    #[test]
    fn test_e2e_tail_call_in_main() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                identity(42)
            }
            fn identity(x) -> u256 {
                x
            }
        "#);
    }

    #[test]
    fn test_e2e_tail_call_in_proc() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                outer(21)
            }
            fn outer(x) -> u256 {
                inner(x)
            }
            fn inner(x) -> u256 {
                @mul(x, 2)
            }
        "#);
    }

    #[test]
    fn test_e2e_apply_three_args() {
        assert_e2e_result(U256::from(15), r#"
            fn main() -> u256 {
                add_three(5, 7, 3)
            }
            fn add_three(a, b, c) -> u256 {
                let ab = @add(a, b);
                @add(ab, c)
            }
        "#);
    }

    #[test]
    fn test_e2e_stack_management_across_if() {
        assert_e2e_result(U256::from(3), r#"
            fn main() -> u256 {
                let a = 1;
                let b = 2;
                let dead = 99;
                let r = if 1 { a } else { b };
                @add(r, b)
            }
        "#);
    }

    #[test]
    fn test_e2e_void_tail_op() {
        assert_e2e_result(U256::from(99), r#"
            fn main() -> u256 {
                store_and_load()
            }
            fn store_and_load() -> u256 {
                let _ = store(99);
                @mload(0)
            }
            fn store(x) {
                @mstore(0, x)
            }
        "#);
    }
}
