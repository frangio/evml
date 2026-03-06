use std::{collections::HashMap, iter::zip};
use anyhow::{bail, Result, Context};
use crate::{ast::*, id::{Id, IdGen}};

pub fn resolve(program: &Program<&str>, ids: &mut IdGen) -> Result<Program<Id>> {
    let mut prog_env = HashMap::with_capacity(program.procs.len());

    for &(name, _) in &program.procs {
        let id = ids.generate();
        if prog_env.insert(name, id).is_some() {
            bail!("duplicate procedure {name}");
        }
    }

    let mut procs = Vec::with_capacity(program.procs.len());

    for (name, proc) in &program.procs {
        let id = prog_env[name];
        let proc = resolve_proc(proc, ids, &prog_env)?;
        procs.push((id, proc));
    }

    Ok(Program { procs })
}

fn resolve_proc(proc: &Proc<&str>, ids: &mut IdGen, prog_env: &HashMap<&str, Id>) -> Result<Proc<Id>> {
    let mut env = prog_env.clone();
    env.reserve(proc.args.len());
    let args = proc.args.iter().map(|_| ids.generate()).collect::<Box<[_]>>();
    let first = args.first().copied();
    for (&arg, &id) in zip(&proc.args, &args) {
        if env.insert(arg, id) >= first {
            bail!("duplicate argument {arg}");
        }
    }
    let body = resolve_block(&proc.body, ids, env)?;
    Ok(Proc { args, rets: proc.rets, body })
}

fn resolve_block<'a>(
    block: &Block<&'a str>,
    ids: &mut IdGen,
    mut env: HashMap<&'a str, Id>,
) -> Result<Block<Id>> {
    let mut priors = Vec::with_capacity(block.priors.len());

    for (x, expr) in &block.priors {
        let expr = resolve_expr(expr, ids, &env)?;
        let y = x.as_ref().map(|x| {
            let y = ids.generate();
            env.insert(x, y);
            y
        });
        priors.push((y, expr));
    }

    let tail = resolve_expr(&block.tail, ids, &env)?;

    Ok(Block { priors, tail })
}

fn resolve_expr(
    expr: &Expr<&str>,
    ids: &mut IdGen,
    env: &HashMap<&str, Id>,
) -> Result<Expr<Id>> {
    Ok(match expr {
        Expr::Unit => Expr::Unit,
        Expr::Const(c) => Expr::Const(*c),
        Expr::Var(x) => Expr::Var(*env.get(x).with_context(|| format!("unbound variable {x}"))?),
        Expr::Op(op, args) => {
            let args = args.iter().map(|expr| resolve_expr(expr, ids, env)).collect::<Result<_>>()?;
            Expr::Op(*op, args)
        }
        Expr::Apply(f, args) => {
            let f = *env.get(f).with_context(|| format!("unbound procedure {f}"))?;
            let args = args.iter().map(|expr| resolve_expr(expr, ids, env)).collect::<Result<_>>()?;
            Expr::Apply(f, args)
        }
        Expr::IfThenElse(cond_then_else) => {
            let (cond, then_else) = cond_then_else.as_ref();
            let cond = resolve_expr(cond, ids, env)?;
            let [then_block, else_block] = then_else;
            let then_block = resolve_block(then_block, ids, env.clone())?;
            let else_block = resolve_block(else_block, ids, env.clone())?;
            Expr::IfThenElse(Box::new((cond, [then_block, else_block])))
        }
    })
}
