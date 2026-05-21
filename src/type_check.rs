use std::collections::HashMap;
use anyhow::{bail, ensure, Result};
use crate::{Id, ast, opcodes};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Type {
    Val,
    Proc { args: usize, rets: usize },
    Join { args: usize, rets: usize, depth: usize },
}

pub fn type_check(program: &ast::Program<Id>) -> Result<()> {
    let mut env = HashMap::with_capacity(program.funcs.len());
    for (name, func) in &program.funcs {
        env.insert(*name, Type::Proc { args: func.args.len(), rets: func.rets });
    }
    for (_, func) in &program.funcs {
        type_check_func(func, &env)?;
    }
    Ok(())
}

fn type_check_func(f: &ast::Func<Id>, env: &HashMap<Id, Type>) -> Result<()> {
    let mut env = env.clone();
    env.reserve(f.args.len());
    for &arg in &f.args {
        env.insert(arg, Type::Val);
    }
    let rets = type_check_block(&f.body, env, 0)?;
    ensure!(rets == f.rets, "function return size mismatch");
    Ok(())
}

fn type_check_block(block: &ast::Block<Id>, mut env: HashMap<Id, Type>, tail_depth: usize) -> Result<usize> {
    for stmt in &block.stmts {
        match stmt {
            ast::Stmt::Let(x, e) => {
                let outputs = type_check_expr(e, &env, tail_depth, false)?;
                ensure!(outputs == x.iter().count(), "void operation can't be assigned");
                if let Some(x) = x {
                    env.insert(*x, Type::Val);
                }
            }
            ast::Stmt::Func(name, f) => {
                env.insert(*name, Type::Join { args: f.args.len(), rets: f.rets, depth: tail_depth });
                type_check_func(f, &env)?;
            }
        }
    }

    type_check_expr(&block.tail, &env, tail_depth, true)
}

fn type_check_expr(expr: &ast::Expr<Id>, env: &HashMap<Id, Type>, tail_depth: usize, at_tail: bool) -> Result<usize> {
    use crate::ast::*;

    let type_check_arg = |expr: &Expr<Id>| -> Result<()> {
        ensure!(
            type_check_expr(expr, env, tail_depth, false)? == 1,
            "argument expression must produce one value"
        );
        Ok(())
    };

    match expr {
        Expr::Unit => Ok(0),
        Expr::Const(_) => Ok(1),
        Expr::Var(x) => {
            ensure!(env.get(x).copied() == Some(Type::Val), "variable is not a value");
            Ok(1)
        }

        Expr::Op(op, args) => {
            let Some(info) = opcodes::info(*op) else { bail!("unknown opcode {op:#04x?}") };
            ensure!(args.len() == info.inputs);
            for arg in args {
                type_check_arg(arg)?;
            }
            Ok(info.outputs)
        }

        Expr::Apply(f, args) => {
            let (expected_args, rets) = match env.get(f).copied() {
                Some(Type::Proc { args, rets }) => (args, rets),
                Some(Type::Join { args, rets, depth: join_depth }) => {
                    ensure!(at_tail, "function can only be called in tail position");
                    ensure!(tail_depth == join_depth, "function can only be called at tail of defining scope");
                    (args, rets)
                }
                _ => bail!("not a procedure or function"),
            };
            ensure!(args.len() == expected_args, "wrong number of arguments");
            for arg in args {
                type_check_arg(arg)?;
            }
            Ok(rets)
        }

        Expr::IfThenElse(cond_then_else) => {
            let (cond, then_else) = cond_then_else.as_ref();
            let outputs = type_check_expr(cond, env, tail_depth, false)?;
            ensure!(outputs == 1, "if condition must be a value");
            let branch_depth = if at_tail { tail_depth } else { tail_depth + 1 };
            let then_outputs = type_check_block(&then_else[0], env.clone(), branch_depth)?;
            let else_outputs = type_check_block(&then_else[1], env.clone(), branch_depth)?;
            ensure!(then_outputs == else_outputs, "if branches return different stack sizes");
            Ok(then_outputs)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{U256, id::{generate_ids, IdGen}};

    #[test]
    fn test_type_check_div_ok() {
        use super::ast::{Block, Expr::*, Func, Program};
        let mut ids = IdGen::new();
        generate_ids! { main in ids };
        let program = Program {
            funcs: vec![(
                main,
                Func {
                    args: Box::new([]),
                    rets: 1,
                    body: Block {
                        stmts: vec![],
                        tail: Op(0x04, Box::new([Const(U256::from(84)), Const(U256::from(2))])),
                    },
                },
            )],
        };
        assert!(type_check(&program).is_ok());
    }

    #[test]
    fn test_type_check_div_err() {
        use super::ast::{Block, Expr::*, Func, Program};
        let mut ids = IdGen::new();
        generate_ids! { main in ids };
        let program = Program {
            funcs: vec![(
                main,
                Func {
                    args: Box::new([]),
                    rets: 1,
                    body: Block {
                        stmts: vec![],
                        tail: Op(0x04, Box::new([Const(U256::from(84))])),
                    },
                },
            )],
        };
        assert!(type_check(&program).is_err());
    }

    #[test]
    fn test_type_check_pop_err() {
        use super::ast::{Block, Expr::*, Func, Program, Stmt::*};
        let mut ids = IdGen::new();
        generate_ids! { main, x in ids };
        let program = Program {
            funcs: vec![(
                main,
                Func {
                    args: Box::new([]),
                    rets: 0,
                    body: Block {
                        stmts: vec![Let(Some(x), Op(0x50, Box::new([Const(U256::from(42))])))],
                        tail: Const(U256::from(0)),
                    },
                },
            )],
        };
        assert!(type_check(&program).is_err());
    }

    #[test]
    fn test_type_check_rejects_void_arg_expr() {
        use super::ast::{Block, Expr::*, Func, Program};
        let mut ids = IdGen::new();
        generate_ids! { main in ids };
        let program = Program {
            funcs: vec![(
                main,
                Func {
                    args: Box::new([]),
                    rets: 1,
                    body: Block {
                        stmts: vec![],
                        tail: Op(
                            0x01,
                            Box::new([
                                Op(0x50, Box::new([Const(U256::from(42))])),
                                Const(U256::from(1)),
                            ]),
                        ),
                    },
                },
            )],
        };
        assert!(type_check(&program).is_err());
    }

    #[test]
    fn test_type_check_func_ok() {
        let mut ids = IdGen::new();
        let ast = crate::parse("fn main() -> u256 { fn f(x) -> u256 { @add(x, 1) } f(0) }")
            .unwrap();
        let ast = crate::resolve(&ast, &mut ids).unwrap();
        assert!(type_check(&ast).is_ok());
    }

    #[test]
    fn test_type_check_func_wrong_args() {
        let mut ids = IdGen::new();
        let ast = crate::parse("fn main() -> u256 { fn f(x) -> u256 { @add(x, 1) } f(0, 0) }")
            .unwrap();
        let ast = crate::resolve(&ast, &mut ids).unwrap();
        assert!(type_check(&ast).is_err());
    }

    #[test]
    fn test_type_check_func_multiple_args() {
        let mut ids = IdGen::new();
        let ast = crate::parse("fn main() -> u256 { fn f(x, y) -> u256 { @add(x, y) } f(0, 0) }")
            .unwrap();
        let ast = crate::resolve(&ast, &mut ids).unwrap();
        assert!(type_check(&ast).is_ok());
    }

    #[test]
    fn test_type_check_func_only_tail_calls() {
        let mut ids = IdGen::new();
        let ast =
            crate::parse("fn main() -> u256 { fn f(x) -> u256 { @add(x, 1) } let x = f(0); x }")
                .unwrap();
        let ast = crate::resolve(&ast, &mut ids).unwrap();
        assert!(type_check(&ast).is_err());
    }

    #[test]
    fn test_type_check_func_in_tail_if_branch() {
        let mut ids = IdGen::new();
        let ast = crate::parse(
            "fn main() -> u256 { fn f(x) -> u256 { @add(x, 1) } if 1 { f(0) } else { 0 } }",
        )
        .unwrap();
        let ast = crate::resolve(&ast, &mut ids).unwrap();
        assert!(type_check(&ast).is_ok());
    }

    #[test]
    fn test_type_check_func_recursive() {
        let mut ids = IdGen::new();
        let ast = crate::parse(
            "fn main() -> u256 { fn f(x) -> u256 { if x { f(@sub(x, 1)) } else { 0 } } f(3) }",
        )
        .unwrap();
        let ast = crate::resolve(&ast, &mut ids).unwrap();
        assert!(type_check(&ast).is_ok());
    }
}
