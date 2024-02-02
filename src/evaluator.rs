use std::collections::HashMap;

use crate::{
    parser::{BinaryOp, Expression, Parser, Pattern},
    ranged::Ranged,
    tokens::Tokens,
    value::{Module, Value},
};

pub struct Evaluator {
    locals: Vec<(String, Value)>,
}

impl Evaluator {
    pub fn new() -> Self {
        Self { locals: vec![] }
    }

    fn resolve_ident(
        &self,
        expected: &str,
        start: usize,
        end: usize,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let result = self
            .locals
            .iter()
            .rev()
            .find(|(ident, _)| ident == expected)
            .map(|(_, value)| value.clone());

        if let Some(value) = result {
            return Ok(value);
        }

        module.borrow().map.get(expected).map_or_else(
            || {
                Err(Ranged::new(
                    EvaluationError::UnboundIdentifier(expected.to_string()),
                    start,
                    end,
                ))
            },
            |value| Ok(value.clone()),
        )
    }

    fn check_pattern(pattern: &Ranged<Pattern>, value: &Value) -> EvaluationResult<()> {
        match (&pattern.data, value) {
            (Pattern::NaturalNumber(nat), Value::Integer(int)) => (&nat.parse::<isize>().unwrap()
                == int)
                .then_some(())
                .ok_or_else(|| {
                    Ranged::new(
                        EvaluationError::UnmatchedPattern,
                        pattern.start,
                        pattern.end,
                    )
                }),
            (Pattern::Pair { first, second }, Value::Pair(pair)) => {
                Self::check_pattern(first, &pair.first)?;
                Self::check_pattern(second, &pair.second)
            }
            (Pattern::All(_), _) => Ok(()),
            _ => Err(Ranged::new(
                EvaluationError::UnmatchedPattern,
                pattern.start,
                pattern.end,
            )),
        }
    }

    fn define_pattern_locals(&mut self, pattern: &Ranged<Pattern>, value: Value) {
        match (&pattern.data, value) {
            (Pattern::All(ident), value) => {
                self.locals.push((ident.clone(), value));
            }
            (Pattern::Pair { first, second }, Value::Pair(pair)) => {
                self.define_pattern_locals(first, *pair.first.clone());
                self.define_pattern_locals(second, *pair.second.clone());
            }
            _ => (),
        }
    }

    fn eval_binary(
        &mut self,
        lhs: &Ranged<Expression>,
        rhs: &Ranged<Expression>,
        bop: BinaryOp,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let (left_value, right_value) =
            (self.eval_expr(lhs, module)?, self.eval_expr(rhs, module)?);

        Ok(match bop {
            BinaryOp::Addition => {
                let (lhs, rhs) = match (left_value, right_value) {
                    (Value::Integer(left_int), Value::Integer(right_int)) => (left_int, right_int),
                    _ => {
                        return Err(Ranged::new(
                            EvaluationError::ExpectedNumbers,
                            lhs.start,
                            rhs.end,
                        ))
                    }
                };
                Value::Integer(lhs + rhs)
            }
            BinaryOp::Multiplication => {
                let (lhs, rhs) = match (left_value, right_value) {
                    (Value::Integer(left_int), Value::Integer(right_int)) => (left_int, right_int),
                    _ => {
                        return Err(Ranged::new(
                            EvaluationError::ExpectedNumbers,
                            lhs.start,
                            rhs.end,
                        ))
                    }
                };
                Value::Integer(lhs * rhs)
            }
            BinaryOp::Pairing => Value::new_pair_value(left_value, right_value),
        })
    }

    fn eval_let(
        &mut self,
        pattern: &Ranged<Pattern>,
        value_expr: &Ranged<Expression>,
        return_expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let value = self.eval_expr(value_expr, module)?;
        Self::check_pattern(pattern, &value)?;
        let local_len = self.locals.len();
        self.define_pattern_locals(pattern, value);
        let result = self.eval_expr(return_expr, module);
        self.locals.truncate(local_len);
        result
    }

    fn eval_application(
        &mut self,
        expr: &Ranged<Expression>,
        arguments: &[Ranged<Expression>],
        module: &Module,
    ) -> EvaluationResult<Value> {
        let Value::Lambda(lambda) = self.eval_expr(expr, module)? else {
            return Err(Ranged::new(EvaluationError::ExpectedFunction, expr.start, expr.end))
        };

        if arguments.len() != lambda.args.len() {
            return Err(Ranged::new(
                EvaluationError::ArityMismatch,
                expr.start,
                expr.end,
            ));
        }

        let local_len = self.locals.len();
        self.locals.extend(lambda.captures.clone());
        for (argument, pattern) in arguments.iter().zip(&lambda.args) {
            let value = self.eval_expr(argument, &lambda.module)?;
            Self::check_pattern(pattern, &value)?;
            self.define_pattern_locals(pattern, value);
        }
        let result = self.eval_expr(&lambda.expr, &lambda.module);
        self.locals.truncate(local_len);
        result
    }

    fn eval_import(&mut self, parts: &[String], _module: &Module) -> EvaluationResult<Value> {
        let file_path = parts.join("/") + ".txt";
        let file = match std::fs::read_to_string(&file_path) {
            Ok(value) => value,
            Err(_) => panic!(),
        };
        let tokens = Tokens::new(&file);
        let module = Parser::new(tokens).parse_module().unwrap();
        Ok(Value::Module(self.eval_module(file_path, &module)?))
    }

    fn eval_access(
        &mut self,
        from: &Ranged<Expression>,
        what: &Ranged<String>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let from = self.eval_expr(from, module)?;

        let Value::Module(module) = from else {
            panic!()
        };

        let map = &module.borrow().map;
        let Some(value) = map.get(&what.data) else {
            panic!()
        };

        Ok(value.clone())
    }

    pub fn eval_expr(
        &mut self,
        expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        match &expr.data {
            Expression::Identifier(ident) => {
                Ok(self.resolve_ident(ident, expr.start, expr.end, module)?)
            }
            Expression::NaturalNumber(nat) => Ok(Value::Integer(nat.parse().unwrap())),
            Expression::Binary { lhs, rhs, bop } => self.eval_binary(lhs, rhs, *bop, module),
            Expression::Let {
                pattern,
                value_expr,
                return_expr,
            } => self.eval_let(pattern, value_expr, return_expr, module),
            Expression::Function { args, expr } => Ok(Value::new_lambda_value(
                self.locals.clone(),
                args.clone(),
                *expr.clone(),
                module.clone(),
            )),
            Expression::Application { expr, args } => self.eval_application(expr, args, module),
            Expression::Import(parts) => self.eval_import(parts, module),
            Expression::Access { from, what } => self.eval_access(from, what, module),
        }
    }

    fn eval_module(
        &mut self,
        source: String,
        definitions: &[(String, Ranged<Expression>)],
    ) -> EvaluationResult<Module> {
        let module = Value::new_module(source, HashMap::default());

        for (name, expr) in definitions {
            let value = self.eval_expr(expr, &module)?;
            module.borrow_mut().map.insert(name.clone(), value);
        }

        Ok(module)
    }

    pub fn eval_main(
        &mut self,
        source: String,
        definitions: &[(String, Ranged<Expression>)],
    ) -> EvaluationResult<Value> {
        let module = self.eval_module(source, definitions)?;

        let main = module
            .borrow_mut()
            .map
            .remove(&String::from("main"))
            .expect("Symbol main is not provided.");
        let Value::Lambda(lambda) = main else {
            panic!("main is not function");
        };

        self.eval_expr(&lambda.expr, &lambda.module)
    }
}

#[derive(Debug)]
pub enum EvaluationError {
    UnmatchedPattern,
    UnboundIdentifier(String),
    ExpectedNumbers,
    ExpectedFunction,
    ArityMismatch,
}

type EvaluationResult<T> = Result<T, Ranged<EvaluationError>>;
