use std::{collections::HashMap, iter::zip};
use anyhow::{bail, Result, Context};
use crate::{ast::*, id::{Id, IdGen}};

pub fn resolve(program: &Program<&str>, ids: &mut IdGen) -> Result<Program<Id>> {
    let mut prog_env = HashMap::with_capacity(program.funcs.len());

    for &(name, _) in &program.funcs {
        let id = ids.generate();
        if prog_env.insert(name, id).is_some() {
            bail!("duplicate procedure {name}");
        }
    }

    let mut funcs = Vec::with_capacity(program.funcs.len());

    for (name, f) in &program.funcs {
        let id = prog_env[name];
        let f = resolve_func(f, ids, &prog_env)?;
        funcs.push((id, f));
    }

    Ok(Program { funcs })
}

fn resolve_func(f: &Func<&str>, ids: &mut IdGen, prog_env: &HashMap<&str, Id>) -> Result<Func<Id>> {
    let mut env = prog_env.clone();
    env.reserve(f.args.len());
    let args = resolve_args(&f.args, ids, &mut env)?;
    let body = resolve_block(&f.body, ids, env)?;
    Ok(Func { args, rets: f.rets, body })
}

fn resolve_args<'a>(
    args: &[&'a str],
    ids: &mut IdGen,
    env: &mut HashMap<&'a str, Id>,
) -> Result<Box<[Id]>> {
    let resolved_args = args.iter().map(|_| ids.generate()).collect::<Box<[_]>>();
    let first = resolved_args.first().copied();
    for (&arg, &id) in zip(args, &resolved_args) {
        if env.insert(arg, id) >= first {
            bail!("duplicate argument {arg}");
        }
    }
    Ok(resolved_args)
}

fn resolve_block<'a>(
    block: &Block<&'a str>,
    ids: &mut IdGen,
    mut env: HashMap<&'a str, Id>,
) -> Result<Block<Id>> {
    let mut stmts = Vec::with_capacity(block.stmts.len());

    for stmt in &block.stmts {
        match stmt {
            Stmt::Let(x, expr) => {
                let expr = resolve_expr(expr, ids, &env)?;
                let x = x.map(|x| {
                    let y = ids.generate();
                    env.insert(x, y);
                    y
                });
                stmts.push(Stmt::Let(x, expr));
            }
            Stmt::Func(name, f) => {
                let y = ids.generate();
                env.insert(name, y);
                stmts.push(Stmt::Func(y, resolve_func(f, ids, &env)?));
            }
        }
    }

    let tail = resolve_expr(&block.tail, ids, &env)?;

    Ok(Block { stmts, tail })
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
