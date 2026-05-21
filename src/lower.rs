use std::collections::HashSet;

use crate::id::{Id, IdGen};
use crate::{ast, core, opcodes};

pub fn lower(program: ast::Program<Id>, ids: &mut IdGen) -> core::Program {
    let mut funcs_iter = program.funcs.into_iter();
    let (_, main_func) = funcs_iter.next().expect("no funcs in program");
    assert!(main_func.args.is_empty());
    let main = lower_block(main_func.body, ids, &mut HashSet::new());
    let procs = funcs_iter
        .map(|(name, ast::Func { args, rets, body })| {
            let body = lower_block(body, ids, &mut HashSet::new());
            (name, core::Proc { args, rets, body })
        })
        .collect();
    core::Program { main, rets: main_func.rets, procs }
}

fn lower_block(block: ast::Block<Id>, ids: &mut IdGen, joins: &mut HashSet<Id>) -> core::Block {
    let mut priors = Vec::with_capacity(block.stmts.len());

    for stmt in block.stmts {
        match stmt {
            ast::Stmt::Let(x, expr) => {
                let expr = lower_expr(expr, &mut priors, ids, joins);
                priors.push((x, expr));
            }

            ast::Stmt::Func(name, ast::Func { args, rets, body }) => {
                joins.insert(name);
                let body = lower_block(body, ids, joins);
                let expr = core::Expr::Join(args, rets, Box::new(body));
                priors.push((Some(name), expr));
            }
        }
    }

    let tail = lower_expr(block.tail, &mut priors, ids, joins);
    let tail = expr_to_tail(tail, &mut priors, ids, joins);

    core::Block { priors, tail }
}

fn lower_expr(
    expr: ast::Expr<Id>,
    priors: &mut Vec<(Option<Id>, core::Expr)>,
    ids: &mut IdGen,
    joins: &mut HashSet<Id>,
) -> core::Expr {
    match expr {
        ast::Expr::Unit => core::Expr::Unit,
        ast::Expr::Const(c) => core::Expr::Const(c),
        ast::Expr::Var(x) => core::Expr::Var(x),
        ast::Expr::Op(op, args) => {
            core::Expr::Op(op, args.into_iter().map(|arg| lower_expr_to_var(arg, priors, ids, joins)).collect())
        }
        ast::Expr::Apply(f, args) => {
            core::Expr::Apply(f, args.into_iter().map(|arg| lower_expr_to_var(arg, priors, ids, joins)).collect())
        }
        ast::Expr::IfThenElse(cond_then_else) => {
            let (cond, then_else) = *cond_then_else;
            let cond = lower_expr_to_var(cond, priors, ids, joins);
            let [then_block, else_block] = then_else;
            let then_block = lower_block(then_block, ids, joins);
            let else_block = lower_block(else_block, ids, joins);
            core::Expr::IfThenElse(cond, Box::new([then_block, else_block]))
        }
    }
}

fn lower_expr_to_var(
    expr: ast::Expr<Id>,
    priors: &mut Vec<(Option<Id>, core::Expr)>,
    ids: &mut IdGen,
    joins: &mut HashSet<Id>,
) -> Id {
    match lower_expr(expr, priors, ids, joins) {
        core::Expr::Var(x) => x,
        core::Expr::Const(c) => {
            let x = ids.generate();
            priors.push((Some(x), core::Expr::Const(c)));
            x
        }
        expr => {
            let x = ids.generate();
            priors.push((Some(x), expr));
            x
        }
    }
}

fn expr_to_tail(
    expr: core::Expr,
    priors: &mut Vec<(Option<Id>, core::Expr)>,
    ids: &mut IdGen,
    joins: &HashSet<Id>,
) -> core::TailExpr {
    match expr {
        core::Expr::Unit => core::TailExpr::Unit,
        core::Expr::Var(x) => core::TailExpr::Var(x),

        core::Expr::Const(c) => {
            let x = ids.generate();
            priors.push((Some(x), core::Expr::Const(c)));
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
            if joins.contains(&f) {
                core::TailExpr::Jump(f, args)
            } else {
                core::TailExpr::Apply(f, args)
            }
        }

        core::Expr::IfThenElse(cond, blocks) => {
            core::TailExpr::IfThenElse(cond, blocks)
        }

        core::Expr::Join(_, _, _) => panic!("joins not allowed in tail expression"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse, resolve};

    #[test]
    fn test_lower_func() {
        let mut ids = IdGen::new();
        let ast = parse("fn main() -> u256 { fn f(x) -> u256 { @add(x, 1) } f(0) }").unwrap();
        let ast = resolve(&ast, &mut ids).unwrap();
        let ir = lower(ast, &mut ids);

        let (Some(f), core::Expr::Join(args, rets, body)) = &ir.main.priors[0] else {
            panic!("expected lowered join");
        };
        let [x] = args.as_ref() else {
            panic!("expected one join argument");
        };
        assert_eq!(rets, &1);
        assert!(matches!(body.tail, core::TailExpr::Var(_)));
        assert!(matches!(ir.main.tail, core::TailExpr::Jump(target, _) if target == *f));
        assert_ne!(f, x);
    }
}
