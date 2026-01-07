use crate::{ast, core, opcodes, Id, IdGen};

pub fn lower(program: ast::Program<Id>, ids: &mut IdGen) -> core::Program {
    let mut procs_iter = program.procs.into_iter();
    let (_, main_proc) = procs_iter.next().expect("no procs in program");
    assert!(main_proc.args.is_empty());
    let main = lower_block(main_proc.body, ids);
    let procs = procs_iter.map(|(name, ast::Proc { args, rets, body })| {
        let body = lower_block(body, ids);
        (name, core::Proc { args, rets, body })
    }).collect();
    core::Program { main, rets: main_proc.rets, procs }
}

fn lower_block(block: ast::Block<Id>, ids: &mut IdGen) -> core::Block {
    let mut priors = Vec::with_capacity(block.priors.len());

    for prior in block.priors {
        match prior {
            ast::BlockPrior::Let(x, expr) => {
                let expr = lower_expr(expr, &mut priors, ids);
                priors.push(core::BlockPrior::Let(x, expr));
            }
        }
    }

    let tail = lower_expr(block.tail, &mut priors, ids);
    let tail = expr_to_tail(tail, &mut priors, ids);

    core::Block { priors, tail }
}

fn lower_expr(
    expr: ast::Expr<Id>,
    priors: &mut Vec<core::BlockPrior>,
    ids: &mut IdGen,
) -> core::Expr {
    match expr {
        ast::Expr::Unit => core::Expr::Unit,
        ast::Expr::Val(val) => core::Expr::Val(lower_val(val)),
        ast::Expr::Op(op, vals) => {
            core::Expr::Op(op, vals.into_iter().map(lower_val).collect())
        }
        ast::Expr::Apply(proc_id, vals) => {
            core::Expr::Apply(proc_id, vals.into_iter().map(lower_val).collect())
        }
        ast::Expr::IfThenElse(cond_then_else) => {
            let (cond, then_else) = *cond_then_else;
            let cond = match lower_expr(cond, priors, ids) {
                core::Expr::Val(core::Val::Var(x)) => x,
                expr => {
                    let x = ids.generate();
                    priors.push(core::BlockPrior::Let(Some(x), expr));
                    x
                }
            };
            let [then_block, else_block] = then_else;
            let then_block = lower_block(then_block, ids);
            let else_block = lower_block(else_block, ids);
            core::Expr::IfThenElse(
                cond,
                Box::new([then_block, else_block]),
            )
        }
    }
}

fn expr_to_tail(
    expr: core::Expr,
    priors: &mut Vec<core::BlockPrior>,
    ids: &mut IdGen,
) -> core::TailExpr {
    match expr {
        core::Expr::Unit => core::TailExpr::Unit,
        core::Expr::Val(core::Val::Var(x)) => core::TailExpr::Var(x),

        core::Expr::Val(core::Val::Const(c)) => {
            let x = ids.generate();
            priors.push(core::BlockPrior::Let(Some(x), core::Expr::Val(core::Val::Const(c))));
            core::TailExpr::Var(x)
        }

        core::Expr::Op(op, _) => {
            if opcodes::info(op).unwrap().outputs == 0 {
                priors.push(core::BlockPrior::Let(None, expr));
                core::TailExpr::Unit
            } else {
                let x = ids.generate();
                priors.push(core::BlockPrior::Let(Some(x), expr));
                core::TailExpr::Var(x)
            }
        }

        core::Expr::Apply(proc_id, vals) => {
            core::TailExpr::Apply(proc_id, vals)
        }

        core::Expr::IfThenElse(cond, blocks) => {
            core::TailExpr::IfThenElse(cond, blocks)
        }
    }
}

fn lower_val(val: ast::Val<Id>) -> core::Val {
    match val {
        ast::Val::Const(c) => core::Val::Const(c),
        ast::Val::Var(x) => core::Val::Var(x),
    }
}
