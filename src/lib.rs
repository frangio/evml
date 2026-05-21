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
    pub enum Stmt<T> {
        Let(Option<T>, Expr<T>),
        Func(T, Func<T>),
    }

    #[derive(Debug)]
    pub struct Block<T> {
        pub stmts: Vec<Stmt<T>>,
        pub tail: Expr<T>,
    }

    #[derive(Debug)]
    pub struct Func<T> {
        pub args: Box<[T]>,
        pub rets: usize,
        pub body: Block<T>,
    }

    #[derive(Debug)]
    pub struct Program<T> {
        pub funcs: Vec<(T, Func<T>)>,
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
        Join(Box<[Id]>, usize, Box<Block>),
        IfThenElse(Id, Box<[Block; 2]>),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub enum TailExpr {
        Unit,
        Var(Id),
        Apply(Id, Box<[Id]>),
        Jump(Id, Box<[Id]>),
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
    fn test_e2e_spill_with_swap16() {
        assert_e2e_result(U256::from(1), r#"
            fn main() -> u256 {
                let a1 = 1;
                let a2 = 2;
                let a3 = 3;
                let a4 = 4;
                let a5 = 5;
                let a6 = 6;
                let a7 = 7;
                let a8 = 8;
                let a9 = 9;
                let a10 = 10;
                let a11 = 11;
                let a12 = 12;
                let a13 = 13;
                let a14 = 14;
                let a15 = 15;
                let a16 = 16;
                let a17 = 17;
                let a18 = 18;
                let a19 = a1;
                let x = @add(a2, a3);
                a19
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
    fn test_e2e_local_func() {
        assert_e2e_result(U256::from(42), r#"
            fn main() -> u256 {
                fn f(x) -> u256 { @mul(x, 2) }
                f(21)
            }
        "#);
    }

    #[test]
    fn test_e2e_recursive_local_func() {
        assert_e2e_result(U256::from(0), r#"
            fn main() -> u256 {
                fn f(x) -> u256 {
                    if x { f(@sub(x, 1)) } else { x }
                }
                f(3)
            }
        "#);
    }

    #[test]
    fn test_e2e_multi_arg_local_func() {
        assert_e2e_result(U256::from(120), r#"
            fn main() -> u256 {
                fn fact(n, acc) -> u256 {
                    if n {
                        fact(@sub(n, 1), @mul(acc, n))
                    } else {
                        acc
                    }
                }

                fact(5, 1)
            }
        "#);
    }

    #[test]
    fn test_e2e_local_func_captures_live_values_from_branch_calls() {
        assert_e2e_result(U256::from(44), r#"
            fn main() -> u256 {
                let a = 5;
                let b = 7;

                fn k(x, y) -> u256 {
                    @add(@add(x, y), @mul(a, b))
                }

                if 0 {
                    k(1, 2)
                } else {
                    k(3, 6)
                }
            }
        "#);
    }

    #[test]
    fn test_e2e_local_func_pins_many_captures_across_join() {
        assert_e2e_result(U256::from(178), r#"
            fn main() -> u256 {
                let a1 = 1;
                let a2 = 2;
                let a3 = 3;
                let a4 = 4;
                let a5 = 5;
                let a6 = 6;
                let a7 = 7;
                let a8 = 8;
                let a9 = 9;
                let a10 = 10;
                let a11 = 11;
                let a12 = 12;
                let a13 = 13;
                let a14 = 14;
                let a15 = 15;
                let a16 = 16;
                let a17 = 17;
                let a18 = 18;

                fn k(x, y) -> u256 {
                    let s1 = @add(a1, a2);
                    let s2 = @add(a3, a4);
                    let s3 = @add(a5, a6);
                    let s4 = @add(a7, a8);
                    let s5 = @add(a9, a10);
                    let s6 = @add(a11, a12);
                    let s7 = @add(a13, a14);
                    let s8 = @add(a15, a16);
                    let s9 = @add(a17, a18);
                    let t1 = @add(s1, s2);
                    let t2 = @add(s3, s4);
                    let t3 = @add(s5, s6);
                    let t4 = @add(s7, s8);
                    let total = @add(@add(@add(t1, t2), @add(t3, t4)), s9);
                    @add(@add(x, y), total)
                }

                if 0 {
                    k(50, 60)
                } else {
                    k(3, 4)
                }
            }
        "#);
    }

    #[test]
    fn test_e2e_recursive_local_func_captures_live_values() {
        assert_e2e_result(U256::from(46), r#"
            fn main() -> u256 {
                let step = 2;
                let scale = 3;
                let bias = 12;

                fn loop(n, x, y) -> u256 {
                    if n {
                        loop(@sub(n, 1), @add(x, step), @mul(y, scale))
                    } else {
                        @add(@add(x, y), bias)
                    }
                }

                loop(3, 1, 1)
            }
        "#);
    }

    #[test]
    fn test_e2e_local_func_captures_split_continuation_and_value() {
        assert_e2e_result(U256::from(40), r#"
            fn main() -> u256 {
                let result = if 1 {
                    let offset = 11;

                    fn k(x, y) -> u256 {
                        @add(@add(x, y), offset)
                    }

                    if 0 {
                        k(1, 2)
                    } else {
                        k(4, 5)
                    }
                } else {
                    3
                };

                @mul(result, 2)
            }
        "#);
    }

    #[test]
    fn test_e2e_local_func_captures_block_continuation() {
        assert_e2e_result(U256::from(11), r#"
            fn main() -> u256 {
                let y = if 1 {
                    fn k(x) -> u256 { x }
                    k(10)
                } else {
                    20
                };
                @add(y, 1)
            }
        "#);
    }

    #[test]
    fn test_e2e_local_func_rejects_outer_block_continuation() {
        assert!(compile_from_source(r#"
            fn main() -> u256 {
                fn k(x) -> u256 { x }
                let y = if 1 {
                    k(10)
                } else {
                    20
                };
                @add(y, 1)
            }
        "#).is_err());
    }

    #[test]
    fn test_e2e_if_in_apply() {
        assert_e2e_result(U256::from(10), r#"
            fn main() -> u256 { choose(1) }
            fn choose(x) -> u256 { if x { 10 } else { 20 } }
        "#);
    }

    #[test]
    fn test_e2e_apply_in_if_expr() {
        assert_e2e_result(U256::from(9), r#"
            fn main() -> u256 {
                let x = if 1 { double(4) } else { double(5) };
                @add(x, 1)
            }
            fn double(x) -> u256 { @mul(x, 2) }
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
