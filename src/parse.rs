use anyhow::{anyhow, Result};
use crate::{U256, ast::{self, *}, opcodes};

pub fn parse(source: &str) -> Result<ast::Program<&str>> {
    use chumsky::prelude::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Program<&'a str>, extra::Err<Rich<'a, char>>> {
        let rets = just("->")
            .padded()
            .ignore_then(text::keyword("u256"))
            .to(1usize)
            .padded()
            .or_not()
            .map(|r| r.unwrap_or(0));

        let args = text::ident()
            .padded()
            .separated_by(just(','))
            .collect::<Vec<_>>()
            .delimited_by(just('('), just(')'))
            .padded();

        let expr_const = text::digits(10)
            .to_slice()
            .try_map(|digits: &str, span| {
                digits
                    .parse::<U256>()
                    .map_err(|e| Rich::custom(span, e.to_string()))
                    .map(Expr::Const)
            });

        let expr_var = text::ident().map(|x: &str| Expr::Var(x));

        let func = recursive(|func| {
            let block = recursive(|block| {
                let expr = recursive(|expr| {
                    let expr_op = just('@')
                        .ignore_then(text::ident())
                        .try_map(|opcode_name: &str, span| {
                            opcodes::lookup(opcode_name).ok_or_else(|| {
                                Rich::custom(span, format!("unknown opcode {opcode_name}"))
                            })
                        })
                        .then(
                            expr.clone()
                                .separated_by(just(','))
                                .collect::<Vec<_>>()
                                .delimited_by(just('('), just(')')),
                        )
                        .map(|(op, args)| Expr::Op(op, args.into_boxed_slice()));

                    let expr_apply = text::ident()
                        .then(
                            expr.clone()
                                .separated_by(just(','))
                                .collect::<Vec<_>>()
                                .delimited_by(just('('), just(')')),
                        )
                        .map(|(f, args)| Expr::Apply(f, args.into_boxed_slice()));

                    let expr_if = text::keyword("if")
                        .padded()
                        .ignore_then(expr.clone())
                        .then(block.clone().delimited_by(just('{'), just('}')).padded())
                        .then(
                            text::keyword("else")
                                .padded()
                                .ignore_then(block.clone().delimited_by(just('{'), just('}')).padded())
                                .or_not(),
                        )
                        .map(|((cond, then_block), else_block)| {
                            let else_block = else_block.unwrap_or(Block {
                                stmts: vec![],
                                tail: Expr::Unit,
                            });
                            Expr::IfThenElse(Box::new((cond, [then_block, else_block])))
                        });

                    choice((
                        expr_if,
                        expr_op,
                        expr_apply,
                        expr_const.clone(),
                        expr_var.clone(),
                    ))
                    .padded()
                });

                let block_let = text::keyword("let")
                    .padded()
                    .ignore_then(choice((
                        just('_').to(None),
                        text::ident().map(Some),
                    )))
                    .padded()
                    .then_ignore(just('='))
                    .then(expr.clone())
                    .map(|(name, expr)| Stmt::Let(name, expr));

                let block_func = func.clone().map(|(name, func)| Stmt::Func(name, func));

                let block_expr = expr.clone().map(|expr| Stmt::Let(None, expr));

                let block_stmt = choice((
                    block_func,
                    choice((
                        block_let,
                        block_expr,
                    ))
                    .then_ignore(just(';')),
                ));

                block_stmt
                    .padded()
                    .repeated()
                    .collect()
                    .then(expr.or_not())
                    .padded()
                    .map(|(stmts, tail)| Block { stmts, tail: tail.unwrap_or(Expr::Unit) })
            });

            text::keyword("fn")
                .padded()
                .ignore_then(text::ident())
                .then(args.clone())
                .then(rets.clone())
                .then(block.delimited_by(just('{'), just('}')).padded())
                .map(|(((name, args), rets), body)| {
                    (name, Func { args: args.into_boxed_slice(), rets, body })
                })
        });

        func.padded()
            .repeated()
            .collect::<Vec<_>>()
            .map(|funcs| Program { funcs })
            .then_ignore(end())
    }

    let p = parser()
        .parse(source)
        .into_result()
        .map_err(|es| anyhow!(es[0].to_string()))?;

    Ok(p)
}
