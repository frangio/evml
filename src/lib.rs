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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::generate_ids;

    fn program(main: core::Block, rets: usize) -> core::Program {
        core::Program { main, rets, procs: vec![] }
    }

    #[test]
    fn test_const() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { r in ids };
        let block = Block {
            priors: vec![Let(Some(r), Val(Const(U256::from(42))))],
            tail: TailExpr::Var(r),
        };
        let code = compile(program(block, 1), &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_op_div() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { r in ids };
        let block = Block {
            priors: vec![Let(Some(r), Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))]))],
            tail: TailExpr::Var(r),
        };
        let code = compile(program(block, 1), &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_val() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { x, r in ids };
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(2)))),
                Let(Some(r), Op(0x04, vec![Const(U256::from(84)), Var(x)])),
            ],
            tail: TailExpr::Var(r),
        };
        let code = compile(program(block, 1), &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { x in ids };
        let block = Block {
            priors: vec![
                Let(Some(x), Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))])),
            ],
            tail: TailExpr::Var(x),
        };
        let code = compile(program(block, 1), &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op_reuse() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { x, r in ids };
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(42)))),
                Let(Some(r), Op(0x04, vec![Var(x), Var(x)])),
            ],
            tail: TailExpr::Var(r),
        };
        let code = compile(program(block, 1), &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(1)]);
    }

    #[test]
    fn test_let_unused() {
        use super::core::{Block, BlockPrior::*, Expr::*, TailExpr, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { x, y, r in ids };
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(100)))),
                Let(Some(y), Val(Const(U256::from(100)))),
                Let(Some(r), Val(Const(U256::from(42)))),
            ],
            tail: TailExpr::Var(r),
        };
        let code = compile(program(block, 1), &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_type_check_div_ok() {
        use super::ast::{Block, Expr::*, Proc, Program, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { main in ids };
        let program = Program {
            procs: vec![(main, Proc {
                args: vec![],
                rets: 1,
                body: Block {
                    priors: vec![],
                    tail: Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))]),
                },
            })],
        };
        assert!(type_check(&program).is_ok());
    }

    #[test]
    fn test_type_check_div_err() {
        use super::ast::{Block, Expr::*, Proc, Program, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { main in ids };
        let program = Program {
            procs: vec![(main, Proc {
                args: vec![],
                rets: 1,
                body: Block {
                    priors: vec![],
                    tail: Op(0x04, vec![Const(U256::from(84))]),
                },
            })],
        };
        assert!(type_check(&program).is_err());
    }

    #[test]
    fn test_type_check_pop_err() {
        use super::ast::{Block, BlockPrior::*, Expr::*, Proc, Program, Val::*};
        let mut ids = IdGen::new();
        generate_ids! { main, x in ids };
        let program = Program {
            procs: vec![(main, Proc {
                args: vec![],
                rets: 0,
                body: Block {
                    priors: vec![
                        Let(Some(x), Op(0x50, vec![Const(U256::from(42))])),
                    ],
                    tail: Val(Const(U256::from(0))),
                },
            })],
        };
        assert!(type_check(&program).is_err());
    }

    #[test]
    fn test_parse_if_then_else() {
        let source = "fn main() -> u256 { let c = 1; if c { @add(c, 1) } else { c } }";
        let program = parse(source).expect("parse failed");
        let mut ids = IdGen::new();
        let resolved = resolve(&program, &mut ids).expect("resolve failed");
        type_check(&resolved).expect("type check failed");
    }

    #[test]
    fn test_parse_if_then_else_expr_cond() {
        let source = "fn main() -> u256 { let c = 1; if @eq(c, 1) { 2 } else { 3 } }";
        let program = parse(source).expect("parse failed");
        let mut ids = IdGen::new();
        let resolved = resolve(&program, &mut ids).expect("resolve failed");
        type_check(&resolved).expect("type check failed");
    }
}
