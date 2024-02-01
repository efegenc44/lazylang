use crate::{
    parser::{BinaryOp, Expression, Pattern},
    ranged::Ranged,
};

pub struct Evaluator {
    locals: Vec<(String, Value)>,
}

impl Evaluator {
    pub fn new() -> Self {
        Self { locals: vec![] }
    }

    fn resolve_ident(&self, expected: &str, start: usize, end: usize) -> EvaluationResult<Value> {
        self.locals
            .iter()
            .rev()
            .find(|(ident, _)| ident == expected)
            .ok_or_else(|| {
                Ranged::new(
                    EvaluationError::UnboundIdentifier(expected.to_string()),
                    start,
                    end,
                )
            })
            .map(|(_, value)| value.clone())
    }

    fn check_pattern(pattern: &Ranged<Pattern>, value: &Value) -> bool {
        match (&pattern.data, value) {
            (Pattern::NaturalNumber(nat), Value::Integer(int)) => {
                &nat.parse::<isize>().unwrap() == int
            }
            (Pattern::All(_), _) => true,
        }
    }

    fn define_pattern_locals(&mut self, pattern: &Ranged<Pattern>, value: Value) {
        match (&pattern.data, value) {
            (Pattern::All(ident), value) => {
                self.locals.push((ident.clone(), value));
            }
            _ => (),
        }
    }

    fn eval_binary(
        &mut self,
        lhs: &Ranged<Expression>,
        rhs: &Ranged<Expression>,
        bop: &BinaryOp,
    ) -> EvaluationResult<Value> {
        let (lhs, rhs) = match (self.eval(lhs)?, self.eval(rhs)?) {
            (Value::Integer(lint), Value::Integer(rint)) => (lint, rint),
        };

        Ok(match bop {
            BinaryOp::Addition => Value::Integer(lhs + rhs),
            BinaryOp::Multiplication => Value::Integer(lhs * rhs),
        })
    }

    fn eval_let(
        &mut self,
        pattern: &Ranged<Pattern>,
        vexpr: &Ranged<Expression>,
        rexpr: &Ranged<Expression>,
    ) -> EvaluationResult<Value> {
        let value = self.eval(vexpr)?;
        let true = Self::check_pattern(pattern, &value) else {
            return Err(Ranged::new(EvaluationError::UnmatchedPattern, pattern.start, pattern.end))
        };
        let local_len = self.locals.len();
        self.define_pattern_locals(pattern, value);
        let result = self.eval(rexpr);
        self.locals.truncate(local_len);
        result
    }

    pub fn eval(&mut self, expr: &Ranged<Expression>) -> EvaluationResult<Value> {
        match &expr.data {
            Expression::Identifier(ident) => Ok(self.resolve_ident(ident, expr.start, expr.end)?),
            Expression::NaturalNumber(nat) => Ok(Value::Integer(nat.parse().unwrap())),
            Expression::Binary { lhs, rhs, bop } => self.eval_binary(lhs, rhs, bop),
            Expression::Let {
                pattern,
                vexpr,
                rexpr,
            } => self.eval_let(pattern, vexpr, rexpr),
        }
    }
}

#[derive(Debug)]
pub enum EvaluationError {
    UnmatchedPattern,
    UnboundIdentifier(String),
}

type EvaluationResult<T> = Result<T, Ranged<EvaluationError>>;

#[derive(Clone)]
pub enum Value {
    Integer(isize),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(int) => write!(f, "{int}"),
        }
    }
}
