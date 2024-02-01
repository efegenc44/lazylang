use crate::{
    parser::{BinaryOp, Expression},
    ranged::Ranged,
};

pub struct Evaluator {}

impl Evaluator {
    pub fn new() -> Self {
        Self {}
    }

    fn eval_binary(
        &mut self,
        lhs: Ranged<Expression>,
        rhs: Ranged<Expression>,
        bop: BinaryOp,
    ) -> Value {
        let (lhs, rhs) = match (self.eval(lhs), self.eval(rhs)) {
            (Value::Integer(lint), Value::Integer(rint)) => (lint, rint),
        };

        match bop {
            BinaryOp::Addition => Value::Integer(lhs + rhs),
            BinaryOp::Multiplication => Value::Integer(lhs * rhs),
        }
    }

    pub fn eval(&mut self, expr: Ranged<Expression>) -> Value {
        match expr.data {
            Expression::NaturalNumber(nat) => Value::Integer(nat.parse().unwrap()),
            Expression::Binary { lhs, rhs, bop } => self.eval_binary(*lhs, *rhs, bop),
        }
    }
}

pub enum Value {
    Integer(isize),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Integer(int) => write!(f, "{int}"),
        }
    }
}
