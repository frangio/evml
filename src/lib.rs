mod runner;
mod opcodes;
mod graph;
mod analysis;
mod compile;
mod utils;

pub use runner::run;
pub use compile::*;

use std::{collections::HashMap, iter::once, num::NonZeroUsize};

use anyhow::{anyhow, bail, ensure, Context, Result};
use revm::{bytecode::opcode, primitives::U256};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Id(NonZeroUsize);

#[cfg_attr(test, derive(Clone))]
pub struct IdGen(NonZeroUsize);

impl IdGen {
    pub fn new() -> IdGen {
        IdGen(NonZeroUsize::MIN)
    }

    fn generate(&mut self) -> Id {
        let id = Id(self.0);
        self.0 = self.0.checked_add(1).expect("integer overflow");
        id
    }
}

#[cfg(test)]
macro_rules! generate_ids {
    ($ids:ident => $($id:ident),+) => {
        $(let $id = $ids.generate();)+
    };
}
#[cfg(test)]
pub(crate) use generate_ids;

use crate::utils::exact_size_chain;

pub mod ast {
    use revm::primitives::U256;

    pub enum Val<T> {
        Const(U256),
        Var(T),
    }

    pub enum Expr<T> {
        Unit,
        Val(Val<T>),
        Op(u8, Vec<Val<T>>),
        IfThenElse(Box<(Expr<T>, [Block<T>; 2])>),
    }

    pub enum BlockPrior<T> {
        Let(Option<T>, Expr<T>),
    }

    pub struct Block<T> {
        pub priors: Vec<BlockPrior<T>>,
        pub tail: Expr<T>,
    }
}

pub mod core {
    use super::Id;
    use revm::primitives::U256;

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
        IfThenElse(Val, Box<[Block; 2]>),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub enum BlockPrior {
        Let(Option<Id>, Expr),
    }

    #[derive(PartialEq, Eq, Debug)]
    pub struct Block {
        pub priors: Vec<BlockPrior>,
        pub tail: Expr,
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
    use super::Id;
    use revm::primitives::U256;

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

pub fn assemble(code: &[asm::Instr]) -> Vec<u8> {
    use asm::Instr::*;

    const MAX_CODE_SIZE: usize = 24 * 1024;

    let mut label_offsets: HashMap<Id, usize> = HashMap::new();
    let mut pc = 0usize;
    for instr in code {
        match instr {
            JumpDest(id) => {
                if label_offsets.insert(*id, pc).is_some() {
                    panic!("duplicate label");
                }
                pc += 1;
            }
            Push(value) => pc += instruction_push(value.to_be_bytes::<32>()).len(),
            PushLabel(_id) => pc += 3,
            Pop | JumpIf | Jump | Stop | Op(_) | Swap(_) | Dup(_) => pc += 1,
        }
    }
    assert!(pc <= MAX_CODE_SIZE, "bytecode too large");

    let mut bytecode = Vec::with_capacity(code.len());
    for instr in code {
        match instr {
            Pop => bytecode.push(opcode::POP),
            Push(value) => bytecode.extend(instruction_push(value.to_be_bytes::<32>())),
            Swap(depth) => bytecode.push(opcode_swap(*depth)),
            Dup(depth) => bytecode.push(opcode_dup(*depth)),
            Op(op) => bytecode.push(*op),
            JumpDest(id) => {
                let expected = label_offsets[id];
                assert!(bytecode.len() == expected);
                bytecode.push(opcode::JUMPDEST);
            }
            PushLabel(id) => {
                let offset = label_offsets[id];
                let offset: u16 = offset.try_into().unwrap();
                bytecode.push(opcode::PUSH2);
                bytecode.extend(offset.to_be_bytes());
            }
            JumpIf => bytecode.push(opcode::JUMPI),
            Jump => bytecode.push(opcode::JUMP),
            Stop => bytecode.push(opcode::STOP),
        }
    }
    bytecode
}

fn opcode_swap(depth: usize) -> u8 {
    assert!(depth > 0, "can't swap top of stack");
    assert!(depth <= 16, "stack too deep");
    opcode::SWAP1 + (depth - 1) as u8
}

fn opcode_dup(depth: usize) -> u8 {
    assert!(depth < 16, "stack too deep");
    opcode::DUP1 + depth as u8
}

fn instruction_push<const N: usize>(value: [u8; N]) -> impl ExactSizeIterator<Item = u8> {
    assert!(N <= 32);
    let mut value = value.into_iter().peekable();
    while value.next_if_eq(&0).is_some() {}
    exact_size_chain(
        once(opcode::PUSH0 + value.len() as u8),
        value,
    )
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Type {
    Val,
}

pub fn type_check(block: &ast::Block<Id>) -> Result<()> {
    let env = HashMap::new();
    type_check_block(block, env)?;
    Ok(())
}

fn type_check_block(block: &ast::Block<Id>, mut env: HashMap<Id, Type>) -> Result<usize> {
    use ast::*;
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
    use ast::*;
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

pub fn lower(block: ast::Block<Id>, ids: &mut IdGen) -> core::Block {
    lower_block(block, ids)
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
        ast::Expr::IfThenElse(cond_then_else) => {
            let (cond, then_else) = *cond_then_else;
            let cond = match lower_expr(cond, priors, ids) {
                core::Expr::Val(val) => val,
                expr => {
                    let x = ids.generate();
                    priors.push(core::BlockPrior::Let(Some(x), expr));
                    core::Val::Var(x)
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

fn lower_val(val: ast::Val<Id>) -> core::Val {
    match val {
        ast::Val::Const(c) => core::Val::Const(c),
        ast::Val::Var(x) => core::Val::Var(x),
    }
}

pub fn resolve(block: &ast::Block<&str>, ids: &mut IdGen) -> Result<ast::Block<Id>> {
    let env = HashMap::new();
    resolve_block(block, ids, env)
}

fn resolve_block<'a>(
    block: &ast::Block<&'a str>,
    ids: &mut IdGen,
    mut env: HashMap<&'a str, Id>,
) -> Result<ast::Block<Id>> {
    use ast::*;

    let mut priors = Vec::with_capacity(block.priors.len());

    for prior in &block.priors {
        match prior {
            BlockPrior::Let(x, expr) => {
                let expr = resolve_expr(expr, ids, &env)?;
                let y = x.as_ref().map(|x| {
                    let y = ids.generate();
                    env.insert(x, y);
                    y
                });
                priors.push(BlockPrior::Let(y, expr));
            }

        }
    }

    let tail = resolve_expr(&block.tail, ids, &env)?;

    Ok(Block { priors, tail })
}

fn resolve_expr(
    expr: &ast::Expr<&str>,
    ids: &mut IdGen,
    env: &HashMap<&str, Id>,
) -> Result<ast::Expr<Id>> {
    use ast::*;
    Ok(match expr {
        Expr::Unit => Expr::Unit,
        Expr::Val(val) => Expr::Val(resolve_val(val, env)?),
        Expr::Op(op, vals) => {
            let vals = vals.iter().map(|val| resolve_val(val, env)).collect::<Result<_>>()?;
            Expr::Op(*op, vals)
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

fn resolve_val(val: &ast::Val<&str>, env: &HashMap<&str, Id>) -> Result<ast::Val<Id>> {
    use ast::*;
    Ok(match val {
        Val::Const(c) => Val::Const(*c),
        Val::Var(x) => {
            Val::Var(*env.get(x).with_context(|| format!("unbound variable {x}"))?)
        }
    })
}

pub fn parse(source: &str) -> Result<ast::Block<&str>> {
    use chumsky::prelude::*;
    use ast::*;

    fn parser<'a>() -> impl Parser<'a, &'a str, Block<&'a str>, extra::Err<Rich<'a, char>>> {
        let val_const = text::digits(10)
            .to_slice()
            .try_map(|digits: &str, span| {
                digits
                    .parse::<U256>()
                    .map_err(|e| Rich::custom(span, e.to_string()))
                    .map(Val::Const)
            });

        let val_var = text::ident()
            .map(|x: &str| Val::Var(x));

        let val = choice((
            val_const,
            val_var,
        )).padded();

        let block = recursive(|block| {
            let expr = recursive(|expr| {
                let expr_val = val.map(Expr::Val);

                let expr_op = just('@')
                    .ignore_then(text::ident())
                    .try_map(|opcode_name: &str, span| {
                        opcodes::lookup(opcode_name)
                            .ok_or_else(|| Rich::custom(span, format!("unknown opcode {opcode_name}")))
                    })
                    .then(
                        val.separated_by(just(','))
                            .collect::<Vec<_>>()
                            .delimited_by(just('('), just(')'))
                    )
                    .map(|(op, args)| Expr::Op(op, args));

                let expr_if = text::keyword("if")
                    .padded()
                    .ignore_then(expr.clone())
                    .then(block.clone().delimited_by(just('{'), just('}')).padded())
                    .then_ignore(text::keyword("else").padded())
                    .then(block.clone().delimited_by(just('{'), just('}')).padded())
                    .map(|((cond, then_block), else_block)| {
                        Expr::IfThenElse(Box::new((cond, [then_block, else_block])))
                    });

                choice((
                    expr_if,
                    expr_op,
                    expr_val,
                ))
                .padded()
            });

            let block_let = text::keyword("let")
                .padded()
                .ignore_then(
                    choice((
                        just('_').to(None),
                        text::ident().map(Some),
                    ))
                )
                .padded()
                .then_ignore(just('='))
                .then(expr.clone())
                .then_ignore(just(';'))
                .map(|(x, e)| BlockPrior::Let(x, e));

            block_let
                .padded()
                .repeated()
                .collect()
                .then(expr)
                .padded()
                .map(|(priors, tail)| Block { priors, tail })
        });

        block.then_ignore(end())
    }

    let b = parser()
        .parse(source)
        .into_result()
        .map_err(|es| anyhow!(es[0].to_string()))?;

    Ok(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const() {
        use super::core::{Block, Expr::*, Val::*};
        let mut ids = IdGen::new();
        let block = Block {
            priors: vec![],
            tail: Val(Const(U256::from(42))),
        };
        let code = compile(block, &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_op_div() {
        use super::core::{Block, Expr::*, Val::*};
        let mut ids = IdGen::new();
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))]),
        };
        let code = compile(block, &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_val() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let mut ids = IdGen::new();
        generate_ids!(ids => x);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(2)))),
            ],
            tail: Op(0x04, vec![Const(U256::from(84)), Var(x)]),
        };
        let code = compile(block, &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let mut ids = IdGen::new();
        generate_ids!(ids => x);
        let block = Block {
            priors: vec![
                Let(Some(x), Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))])),
            ],
            tail: Val(Var(x)),
        };
        let code = compile(block, &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_let_op_reuse() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let mut ids = IdGen::new();
        generate_ids!(ids => x);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(42)))),
            ],
            tail: Op(0x04, vec![Var(x), Var(x)]),
        };
        let code = compile(block, &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(1)]);
    }

    #[test]
    fn test_let_unused() {
        use super::core::{Block, BlockPrior::*, Expr::*, Val::*};
        let mut ids = IdGen::new();
        generate_ids!(ids => x, y);
        let block = Block {
            priors: vec![
                Let(Some(x), Val(Const(U256::from(100)))),
                Let(Some(y), Val(Const(U256::from(100)))),
            ],
            tail: Val(Const(U256::from(42))),
        };
        let code = compile(block, &mut ids);
        let stack = run(&assemble(&code)).expect("execution failed");
        assert_eq!(stack, vec![U256::from(42)]);
    }

    #[test]
    fn test_type_check_div_ok() {
        use super::ast::{Block, Expr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84)), Const(U256::from(2))]),
        };
        assert!(type_check(&block).is_ok());
    }

    #[test]
    fn test_type_check_div_err() {
        use super::ast::{Block, Expr::*, Val::*};
        let block = Block {
            priors: vec![],
            tail: Op(0x04, vec![Const(U256::from(84))]),
        };
        assert!(type_check(&block).is_err());
    }

    #[test]
    fn test_type_check_pop_err() {
        use super::ast::{Block, BlockPrior::*, Expr::*, Val::*};
        let mut ids = IdGen::new();
        generate_ids!(ids => x);
        let block = Block {
            priors: vec![
                Let(Some(x), Op(0x50, vec![Const(U256::from(42))])),
            ],
            tail: Val(Const(U256::from(0))),
        };
        assert!(type_check(&block).is_err());
    }

    #[test]
    fn test_parse_if_then_else() {
        let source = "let c = 1; if c { @add(c, 1) } else { c }";
        let block = parse(source).expect("parse failed");
        let mut ids = IdGen::new();
        let resolved = resolve(&block, &mut ids).expect("resolve failed");
        type_check(&resolved).expect("type check failed");
        let _lowered = lower(resolved, &mut ids);
    }

    #[test]
    fn test_parse_if_then_else_expr_cond() {
        let source = "let c = 1; if @eq(c, 1) { 2 } else { 3 }";
        let block = parse(source).expect("parse failed");
        let mut ids = IdGen::new();
        let resolved = resolve(&block, &mut ids).expect("resolve failed");
        type_check(&resolved).expect("type check failed");
        let _lowered = lower(resolved, &mut ids);
    }
}
