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

    #[derive(Debug)]
    pub enum Expr<T> {
        Unit,
        Const(U256),
        Var(T),
        Op(u8, Box<[Expr<T>]>),
        Apply(T, Box<[Expr<T>]>),
        IfThenElse(Box<(Expr<T>, [Block<T>; 2])>),
    }

    #[derive(Debug)]
    pub struct Block<T> {
        pub priors: Vec<(Option<T>, Expr<T>)>,
        pub tail: Expr<T>,
    }

    #[derive(Debug)]
    pub struct Proc<T> {
        pub args: Box<[T]>,
        pub rets: usize,
        pub body: Block<T>,
    }

    #[derive(Debug)]
    pub struct Program<T> {
        pub procs: Vec<(T, Proc<T>)>,
    }
}

pub mod core {
    use crate::{Id, U256};

    #[derive(PartialEq, Eq, Debug)]
    pub enum Expr {
        Unit,
        Const(U256),
        Var(Id),
        Op(u8, Box<[Id]>),
        Apply(Id, Box<[Id]>),
        IfThenElse(Id, Box<[Block; 2]>),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub enum TailExpr {
        Unit,
        Var(Id),
        Apply(Id, Box<[Id]>),
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

    impl Default for Expr {
        fn default() -> Self {
            Expr::Const(Default::default())
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
        assert_e2e_result(U256::from(42), "fn main() -> u256 { 42 }");
    }

    #[test]
    fn test_e2e_op() {
        assert_e2e_result(U256::from(42), "fn main() -> u256 { @div(84, 2) }");
    }

    #[test]
    fn test_e2e_let() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                let x = 2;
                let y = @div(84, x);
                let unused = 99;
                y
            }
        "#);
    }

    #[test]
    fn test_e2e_if() {
        assert_e2e_result(U256::from(1), "fn main() -> u256 { if 1 { 1 } else { 0 } }");
        assert_e2e_result(U256::from(0), "fn main() -> u256 { if 0 { 1 } else { 0 } }");
        assert_e2e_result(U256::from(10), "fn main() -> u256 { if @gt(5, 3) { 10 } else { 20 } }");
    }

    #[test]
    fn test_e2e_if_nested() {
        assert_e2e_result(U256::from(11), r#"
            fn main() -> u256 {
                let a = 1;
                let b = 0;
                if a { if b { 10 } else { 11 } } else { 12 }
            }
        "#);
    }

    #[test]
    fn test_e2e_if_without_else() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                if 1 { @mstore(0, 42) };
                @mload(0)
            }
        "#);
    }

    #[test]
    fn test_e2e_apply() {
        assert_e2e_result(U256::from(16), r#"
            fn main() -> u256 {
                let x = double(4);
                double(x)
            }
            fn double(x) -> u256 { @mul(x, 2) }
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
    fn test_e2e_args_left_to_right() {
        assert_e2e_result(U256::from(12), r#"
            fn main() -> u256 {
                @mstore(0, 5);
                @add(store_and_return_old(7), store_and_return_old(11))
            }
            fn store_and_return_old(x) -> u256 {
                let old = @mload(0);
                @mstore(0, x);
                old
            }
        "#);
    }

    #[test]
    fn test_e2e_apply_args_eval_left_to_right() {
        assert_e2e_result(U256::from(12), r#"
            fn main() -> u256 {
                @mstore(0, 5);
                add(store_and_return_old(7), store_and_return_old(11))
            }
            fn add(a, b) -> u256 { @add(a, b) }
            fn store_and_return_old(x) -> u256 {
                let old = @mload(0);
                @mstore(0, x);
                old
            }
        "#);
    }

    #[test]
    fn test_e2e_tail_call() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 { outer(21) }
            fn outer(x) -> u256 { inner(x) }
            fn inner(x) -> u256 { @mul(x, 2) }
        "#);
    }

    #[test]
    fn test_e2e_if_in_apply() {
        assert_e2e_result(U256::from(10), r#"
            fn main() -> u256 { choose(1) }
            fn choose(x) -> u256 { if x { 10 } else { 20 } }
        "#);
    }

    #[test]
    fn test_e2e_void_proc() {
        assert_e2e_result(U256::from(99), r#"
            fn main() -> u256 {
                store(99);
                @mload(0)
            }
            fn store(x) { @mstore(0, x) }
        "#);
    }

    #[test]
    fn test_e2e_expr_statement_requires_void() {
        assert!(compile_from_source(r#"
            fn main() -> u256 {
                1;
                2
            }
        "#).is_err());
    }

    #[test]
    fn test_e2e_stack_across_if() {
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
    fn test_e2e_recursive() {
        assert_e2e_result(U256::from(55), r#"
            fn main() -> u256 {
                fib(10)
            }
            fn fib(n) -> u256 {
                let c = @lt(n, 2);
                if c {
                    n
                } else {
                    let a = @sub(n, 1);
                    let b = @sub(n, 2);
                    let fa = fib(a);
                    let fb = fib(b);
                    @add(fa, fb)
                }
            }
        "#);
    }

    #[test]
    fn test_e2e_mutual_recursion() {
        assert_e2e_result(U256::from(1), r#"
            fn main() -> u256 { is_even(4) }
            fn is_even(n) -> u256 {
                if n {
                    let m = @sub(n, 1);
                    is_odd(m)
                } else { 1 }
            }
            fn is_odd(n) -> u256 {
                if n {
                    let m = @sub(n, 1);
                    is_even(m)
                } else { 0 }
            }
        "#);
    }

    #[test]
    fn test_e2e_if_as_prior() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                let x = if 1 { 21 } else { 0 };
                let y = if 1 { 21 } else { 0 };
                @add(x, y)
            }
        "#);
    }
}
