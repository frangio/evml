use std::slice;

use crate::{core, asm, opcodes, Id};
use crate::analysis::{self, Instruction, Procedure, liveness};
use crate::graph::{DepthFirstPostorder, SingletonGraph, Successors};

fn size_of(expr: &core::Expr) -> usize {
    use core::*;
    match expr {
        Expr::Val(_) => 1,
        Expr::Op(op, _) => opcodes::info(*op).unwrap().outputs,
    }
}

struct Stack(Vec<Option<Id>>);
struct StackEntry<'a> {
    stack: &'a mut Stack,
    index: usize,
}

impl Stack {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn popn(&mut self, count: usize) {
        self.0.truncate(self.0.len() - count);
    }

    fn push(&mut self, x: Option<Id>) {
        self.0.push(x);
    }

    fn swap(&mut self, depth: usize) {
        let top = self.0.len() - 1;
        let index = top - depth;
        self.0.swap(index, top);
    }

    fn entry(&mut self, x: Id) -> StackEntry<'_> {
        let index = self.0.iter()
            .rposition(|y| y.as_ref().is_some_and(|&y| y == x))
            .expect("unknown variable");
        StackEntry { stack: self, index }
    }
}

impl StackEntry<'_> {
    fn var(&self) -> Id {
        self.stack.0[self.index].expect("stack item is temporary")
    }

    fn set(&mut self, x: Id) {
        self.stack.0[self.index] = Some(x);
    }

    fn depth(&self) -> usize {
        self.stack.0.len() - 1 - self.index
    }

    fn swap(&mut self) {
        let top = self.stack.0.len() - 1;
        self.stack.0.swap(self.index, top);
    }
}

fn compile_val_onto(
    val: &core::Val,
    stack: &mut Stack,
    should_swap: impl Fn(&StackEntry) -> bool,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;
    match val {
        Val::Const(c) => {
            code.push(Instr::Push(*c));
        }

        Val::Var(x) => {
            let mut entry = stack.entry(*x);
            let depth = entry.depth();
            if !should_swap(&entry) {
                code.push(Instr::Dup(depth));
            } else {
                if depth > 0 {
                    code.push(Instr::Swap(depth));
                    entry.swap();
                }
                stack.popn(1);
            }
        }
    }
}

fn compile_expr_onto(
    expr: &core::Expr,
    stack: &mut Stack,
    is_last_use: impl Fn(Id) -> bool,
    code: &mut Vec<asm::Instr>,
) {
    use core::*;
    use asm::*;
    match expr {
        Expr::Val(val) => {
            compile_val_onto(val, stack, |e| is_last_use(e.var()), code);
        }

        Expr::Op(op, args) => {
            let should_swap  = |x, i| {
                is_last_use(x) && !args[..i].contains(&Val::Var(x))
            };

            let stack_delta = args.iter().enumerate().filter(|&(i, v)| {
                match v {
                    Val::Const(_) => true,
                    Val::Var(x) => !should_swap(*x, i),
                }
            }).count();

            let target_stack_len = stack.len() + stack_delta;

            for (i, v) in args.iter().enumerate().rev() {
                let should_swap = |e: &StackEntry| should_swap(e.var(), i);
                compile_val_onto(v, stack, should_swap, code);
                stack.push(None);
                let rem_delta = target_stack_len - stack.len();
                let offset = i - rem_delta;
                if offset > 0 {
                    code.push(Instr::Swap(offset));
                    stack.swap(offset);
                }
            }

            code.push(Instr::Op(*op));
            stack.popn(args.len());
        }
    }
}

fn compile_block(
    block: core::Block,
    mut liveness: &BlockLiveness,
    mut stack: Stack,
) -> Vec<asm::Instr> {
    use core::*;
    use asm::*;

    let mut code = vec![];

    for (i, prior) in block.priors.into_iter().enumerate() {
        let is_last_use = |x| liveness[&x].last_use == Some(i);
        match prior {
            BlockPrior::Let(x, e) => {
                compile_expr_onto(&e, &mut stack, is_last_use, &mut code);
                if let Some(x) = x {
                    stack.push(Some(x));
                }
            }

        }
    }

    compile_expr_onto(&block.tail, &mut stack, |_| true, &mut code);
    let excess = stack.len();
    if excess > 0 {
        let ret = size_of(&block.tail);
        for _ in 0..ret {
            code.push(Instr::Swap(excess));
            code.push(Instr::Pop);
        }
        if excess > ret {
            code.resize_with(code.len() + excess - ret, || Instr::Pop);
        }
    }

    code
}

pub fn compile(block: core::Block) -> Vec<asm::Instr> {
    let analysis = analyze(&block);
    compile_block(block, &analysis.liveness[&Id::ROOT], Stack::new())
}

struct BlockInstruction<'a> {
    block: &'a core::Block,
    index: usize,
}

impl Instruction for BlockInstruction<'_> {
    type VarId = Id;

    fn index(&self) -> usize {
        self.index
    }

    fn defs(&self) -> impl Iterator<Item = Self::VarId> {
        self.block.priors.get(self.index)
            .and_then(|core::BlockPrior::Let(x, _)| *x)
            .into_iter()
    }

    fn uses(&self) -> impl Iterator<Item = Self::VarId> {
        use core::*;
        let expr = match self.block.priors.get(self.index) {
            Some(BlockPrior::Let(_, e)) => e,
            None => &self.block.tail,
        };
        let vals = match expr {
            Expr::Val(val) => slice::from_ref(val),
            Expr::Op(_, args) => args,
        };
        vals.iter().filter_map(|val| match val {
            Val::Var(id) => Some(*id),
            Val::Const(_) => None,
        })
    }
}

impl Procedure for core::Block {
    type BlockId = Id;
    type VarId = Id;

    fn cfg(&self) -> impl DepthFirstPostorder<Node = Self::BlockId> + Successors {
        SingletonGraph(Id::ROOT)
    }

    fn instructions(
        &self,
        _b: Self::BlockId,
    ) -> impl DoubleEndedIterator<Item: Instruction<VarId = Self::VarId>> {
        (0..=self.priors.len()).map(|i| BlockInstruction { block: self, index: i })
    }
}

type Liveness = analysis::Liveness<core::Block>;
type BlockLiveness = analysis::BlockLiveness<core::Block>;

struct Analysis {
    liveness: Liveness,
}

fn analyze(block: &core::Block) -> Analysis {
    let liveness = liveness(block);
    Analysis { liveness }
}
