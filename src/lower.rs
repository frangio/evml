use crate::{ast, core, opcodes};
use crate::id::{Id, IdGen};

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

    for (x, expr) in block.priors {
        let expr = lower_expr(expr, &mut priors, ids);
        priors.push((x, expr));
    }

    let tail = lower_expr(block.tail, &mut priors, ids);
    let tail = expr_to_tail(tail, &mut priors, ids);

    core::Block { priors, tail }
}

fn lower_expr(
    expr: ast::Expr<Id>,
    priors: &mut Vec<(Option<Id>, core::Expr)>,
    ids: &mut IdGen,
) -> core::Expr {
    match expr {
        ast::Expr::Unit => core::Expr::Unit,
        ast::Expr::Val(v) => core::Expr::Val(lower_val(v)),
        ast::Expr::Op(op, args) => {
            core::Expr::Op(op, args.into_iter().map(|arg| lower_expr_to_val(arg, priors, ids)).collect())
        }
        ast::Expr::Apply(f, args) => {
            core::Expr::Apply(f, args.into_iter().map(|arg| lower_expr_to_val(arg, priors, ids)).collect())
        }
        ast::Expr::IfThenElse(cond_then_else) => {
            let (cond, then_else) = *cond_then_else;
            let cond = lower_expr_to_var(cond, priors, ids);
            let [then_block, else_block] = then_else;
            let then_block = lower_block(then_block, ids);
            let else_block = lower_block(else_block, ids);
            core::Expr::IfThenElse(cond, Box::new([then_block, else_block]))
        }
    }
}

fn lower_expr_to_val(
    expr: ast::Expr<Id>,
    priors: &mut Vec<(Option<Id>, core::Expr)>,
    ids: &mut IdGen,
) -> core::Val {
    match lower_expr(expr, priors, ids) {
        core::Expr::Val(val) => val,
        expr => {
            let x = ids.generate();
            priors.push((Some(x), expr));
            core::Val::Var(x)
        }
    }
}

fn lower_expr_to_var(
    expr: ast::Expr<Id>,
    priors: &mut Vec<(Option<Id>, core::Expr)>,
    ids: &mut IdGen,
) -> Id {
    match lower_expr_to_val(expr, priors, ids) {
        core::Val::Var(x) => x,
        core::Val::Const(c) => {
            let x = ids.generate();
            priors.push((Some(x), core::Expr::Val(core::Val::Const(c))));
            x
        }
    }
}

fn expr_to_tail(
    expr: core::Expr,
    priors: &mut Vec<(Option<Id>, core::Expr)>,
    ids: &mut IdGen,
) -> core::TailExpr {
    match expr {
        core::Expr::Unit => core::TailExpr::Unit,
        core::Expr::Val(core::Val::Var(x)) => core::TailExpr::Var(x),

        core::Expr::Val(core::Val::Const(c)) => {
            let x = ids.generate();
            priors.push((Some(x), core::Expr::Val(core::Val::Const(c))));
            core::TailExpr::Var(x)
        }

        core::Expr::Op(op, _) => {
            if opcodes::info(op).unwrap().outputs == 0 {
                priors.push((None, expr));
                core::TailExpr::Unit
            } else {
                let x = ids.generate();
                priors.push((Some(x), expr));
                core::TailExpr::Var(x)
            }
        }

        core::Expr::Apply(f, args) => {
            core::TailExpr::Apply(f, args)
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
