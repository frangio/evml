use std::collections::HashMap;
use anyhow::{bail, ensure, Result};
use crate::{Id, ast, opcodes};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Type {
    Val,
    Proc { args: usize, rets: usize },
}

pub fn type_check(program: &ast::Program<Id>) -> Result<()> {
    let mut env = HashMap::with_capacity(program.procs.len());
    for (id, proc) in &program.procs {
        env.insert(*id, Type::Proc { args: proc.args.len(), rets: proc.rets });
    }
    for (_, proc) in &program.procs {
        type_check_proc(proc, &env)?;
    }
    Ok(())
}

fn type_check_proc(proc: &ast::Proc<Id>, prog_env: &HashMap<Id, Type>) -> Result<()> {
    let mut env = prog_env.clone();
    env.reserve(proc.args.len());
    for &arg in &proc.args {
        env.insert(arg, Type::Val);
    }
    let rets = type_check_block(&proc.body, env)?;
    ensure!(rets == proc.rets, "procedure return size mismatch");
    Ok(())
}

fn type_check_block(block: &ast::Block<Id>, mut env: HashMap<Id, Type>) -> Result<usize> {
    use crate::ast::*;
    for prior in &block.priors {
        match prior {
            BlockPrior::Let(x, e) => {
                let outputs = type_check_expr(e, &env)?;
                ensure!(outputs == x.iter().count(), "void operation can't be assigned");
                if let Some(x) = x {
                    env.insert(*x, Type::Val);
                }
            }

        }
    }

    type_check_expr(&block.tail, &env)
}

fn type_check_expr(expr: &ast::Expr<Id>, env: &HashMap<Id, Type>) -> Result<usize> {
    use crate::ast::*;
    let type_check_val = |v: &Val<Id>| -> Result<usize> {
        if let Val::Var(x) = v {
            ensure!(env.get(x).copied() == Some(Type::Val), "variable is not a value");
        }
        Ok(1)
    };

    match expr {
        Expr::Unit => Ok(0),

        Expr::Val(v) => type_check_val(v),

        Expr::Op(op, args) => {
            let Some(info) = opcodes::info(*op) else { bail!("unknown opcode {op:#04x?}") };
            ensure!(args.len() == info.inputs);
            for arg in args {
                type_check_val(arg)?;
            }
            Ok(info.outputs)
        }

        Expr::Apply(f, args) => {
            let Some(Type::Proc { args: expected_args, rets }) = env.get(f).copied() else {
                bail!("not a procedure");
            };
            ensure!(args.len() == expected_args, "wrong number of arguments");
            for arg in args {
                type_check_val(arg)?;
            }
            Ok(rets)
        }

        Expr::IfThenElse(cond_then_else) => {
            let (cond, then_else) = cond_then_else.as_ref();
            let outputs = type_check_expr(cond, env)?;
            ensure!(outputs == 1, "if condition must be a value");
            let then_outputs = type_check_block(&then_else[0], env.clone())?;
            let else_outputs = type_check_block(&then_else[1], env.clone())?;
            ensure!(then_outputs == else_outputs, "if branches return different stack sizes");
            Ok(then_outputs)
        }
    }
}
