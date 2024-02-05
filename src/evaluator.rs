use core::fmt;
use std::{collections::HashMap, fs, io};

use crate::{
    error,
    parser::{BinaryOp, Expression, ParseError, Parser, Pattern},
    ranged::{Ranged, Ranges},
    tokens::Tokens,
    value::{self, Module, Type, Value},
};

pub struct Evaluator {
    locals: Vec<(String, Value)>,
}

impl Evaluator {
    pub const fn new() -> Self {
        Self { locals: vec![] }
    }

    fn resolve_ident(
        &self,
        expected: &str,
        ranges: Ranges,
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
                Err(EvaluationError::basic(
                    BaseEvaluationError::UnboundIdentifier(expected.to_string()),
                    ranges,
                ))
            },
            |value| Ok(value.clone()),
        )
    }

    fn check_pattern(&mut self, pattern: &Ranged<Pattern>, value: &Value) -> EvaluationResult<()> {
        match (&pattern.data, value) {
            (Pattern::NaturalNumber(nat), Value::Integer(int)) => (&nat.parse::<isize>().unwrap()
                == int)
                .then_some(())
                .ok_or_else(|| {
                    EvaluationError::basic(
                        BaseEvaluationError::PatternCouldntMatch,
                        pattern.ranges(),
                    )
                }),
            (Pattern::Pair { first, second }, Value::Pair(pair)) => {
                self.check_pattern(first, &pair.first)?;
                self.check_pattern(second, &pair.second)
            }
            (Pattern::All(_), _) => Ok(()),
            (_, Value::Thunk(thunk)) => {
                let value = self.eval_expr_lazy(&thunk.expr, &thunk.module)?;
                self.check_pattern(pattern, &value)
            }
            _ => Err(EvaluationError::basic(
                BaseEvaluationError::PatternCouldntMatch,
                pattern.ranges(),
            )),
        }
    }

    fn define_pattern_locals(
        &mut self,
        pattern: &Ranged<Pattern>,
        value: Value,
    ) -> EvaluationResult<()> {
        match (&pattern.data, value) {
            (Pattern::All(ident), value) => {
                self.locals.push((ident.clone(), value));
                Ok(())
            }
            (Pattern::Pair { first, second }, Value::Pair(pair)) => {
                self.define_pattern_locals(first, *pair.first.clone())?;
                self.define_pattern_locals(second, *pair.second.clone())
            }
            (_, Value::Thunk(thunk)) => {
                let value = self.eval_expr_lazy(&thunk.expr, &thunk.module)?;
                self.define_pattern_locals(pattern, value)
            }
            _ => Ok(()),
        }
    }

    fn eval_binary(
        &mut self,
        lhs: &Ranged<Expression>,
        rhs: &Ranged<Expression>,
        bop: BinaryOp,
        module: &Module,
    ) -> EvaluationResult<Value> {
        Ok(match bop {
            BinaryOp::Addition => {
                let (lhs, rhs) = match (
                    self.eval_expr_eager(lhs, module)?,
                    self.eval_expr_eager(rhs, module)?,
                ) {
                    (Value::Integer(left_int), Value::Integer(right_int)) => (left_int, right_int),
                    (left_value, right_value) => {
                        return Err(EvaluationError::basic(
                            BaseEvaluationError::ExpectedNumbers(
                                left_value.typ(),
                                right_value.typ(),
                            ),
                            (lhs.starts(), rhs.ends()),
                        ))
                    }
                };
                Value::Integer(lhs + rhs)
            }
            BinaryOp::Multiplication => {
                let (lhs, rhs) = match (
                    self.eval_expr_eager(lhs, module)?,
                    self.eval_expr_eager(rhs, module)?,
                ) {
                    (Value::Integer(left_int), Value::Integer(right_int)) => (left_int, right_int),
                    (left_value, right_value) => {
                        return Err(EvaluationError::basic(
                            BaseEvaluationError::ExpectedNumbers(
                                left_value.typ(),
                                right_value.typ(),
                            ),
                            (lhs.starts(), rhs.ends()),
                        ))
                    }
                };
                Value::Integer(lhs * rhs)
            }
            BinaryOp::Pairing => Value::pair(
                self.eval_expr_lazy(lhs, module)?,
                self.eval_expr_lazy(rhs, module)?,
            ),
        })
    }

    fn eval_let(
        &mut self,
        pattern: &Ranged<Pattern>,
        value_expr: &Ranged<Expression>,
        return_expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let value = self.eval_expr_lazy(value_expr, module)?;
        self.check_pattern(pattern, &value)?;
        let local_len = self.locals.len();
        self.define_pattern_locals(pattern, value)?;
        let result = self.eval_expr_lazy(return_expr, module);
        self.locals.truncate(local_len);
        result
    }

    fn eval_application(
        &mut self,
        expr: &Ranged<Expression>,
        args: &[Ranged<Expression>],
        ranges: Ranges,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let value = self.eval_expr_eager(expr, module)?;
        let Value::Lambda(lambda) = value else {
            return Err(EvaluationError::basic(BaseEvaluationError::ExpectedLambda(value.typ()), expr.ranges()));
        };

        if args.len() != lambda.args.len() {
            return Err(EvaluationError::basic(
                BaseEvaluationError::ArityMismatch {
                    takes: lambda.args.len(),
                    provided: args.len(),
                },
                ranges,
            ));
        }

        let local_len = self.locals.len();
        self.locals.extend(lambda.captures.clone());
        for (argument, pattern) in args.iter().zip(&lambda.args) {
            let value = self.eval_expr_lazy(argument, &lambda.module)?;
            self.check_pattern(pattern, &value)?;
            self.define_pattern_locals(pattern, value)?;
        }
        let result = self.eval_expr_lazy(&lambda.expr, &lambda.module);
        self.locals.truncate(local_len);

        result.map_err(|error| {
            EvaluationError::complex(
                BaseEvaluationError::ErrorWhileEvaluatingLambda,
                ranges,
                (Box::new(error), lambda.module.borrow().source_name.clone()),
            )
        })
    }

    fn eval_import(parts: &[String], ranges: Ranges) -> EvaluationResult<Value> {
        let file_path = parts.join("/") + ".txt";
        let file = std::fs::read_to_string(&file_path)
            .map_err(|error| EvaluationError::basic(BaseEvaluationError::IOError(error), ranges))?;
        let tokens = Tokens::new(&file);
        let definitions = Parser::new(tokens).parse_module().map_err(|error| {
            let error_ranges = error.ranges();
            EvaluationError::complex(
                BaseEvaluationError::ErrorWhileImporting,
                ranges,
                (
                    Box::new(EvaluationError::basic(
                        BaseEvaluationError::ParseError(error.data),
                        error_ranges,
                    )),
                    file_path.clone(),
                ),
            )
        })?;
        Ok(Value::Module(Self::eval_module(file_path, &definitions)))
    }

    fn eval_access(
        &mut self,
        from: &Ranged<Expression>,
        what: &Ranged<String>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let from_value = self.eval_expr_eager(from, module)?;

        let Value::Module(module) = from_value else {
            return Err(EvaluationError::basic(BaseEvaluationError::ExpectedModule(from_value.typ()), from.ranges()));
        };

        let map = &module.borrow().map;
        let Some(value) = map.get(&what.data) else {
            return Err(EvaluationError::basic(BaseEvaluationError::UnboundInModule(what.data.clone()), what.ranges()))
        };

        Ok(value.clone())
    }

    pub fn eval_expr_lazy(
        &mut self,
        expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        match &expr.data {
            Expression::Identifier(ident) => self.resolve_ident(ident, expr.ranges(), module),
            Expression::NaturalNumber(nat) => Ok(Value::Integer(nat.parse().unwrap())),
            Expression::Binary { lhs, rhs, bop } => self.eval_binary(lhs, rhs, *bop, module),
            Expression::Let {
                pattern,
                value_expr,
                return_expr,
            } => self.eval_let(pattern, value_expr, return_expr, module),
            Expression::Function { args, expr } => Ok(Value::lambda(
                self.locals.clone(),
                args.clone(),
                *expr.clone(),
                module.clone(),
            )),
            Expression::Application {
                expr: lambda_expr,
                args,
            } => self.eval_application(lambda_expr, args, expr.ranges(), module),
            Expression::Import(parts) => Self::eval_import(parts, expr.ranges()),
            Expression::Access { from, what } => self.eval_access(from, what, module),
        }
    }

    pub fn eval_expr_eager(
        &mut self,
        expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        match &expr.data {
            Expression::Identifier(ident) => {
                Ok(match self.resolve_ident(ident, expr.ranges(), module)? {
                    Value::Thunk(thunk) => {
                        let value = self.eval_expr_eager(&thunk.expr, &thunk.module)?;
                        *module.borrow_mut().map.get_mut(ident).unwrap() = value.clone();
                        value
                    }
                    value => value,
                })
            }
            Expression::Access { from, what } => {
                Ok(match self.eval_access(from, what, module)? {
                    Value::Thunk(thunk) => {
                        let value = self.eval_expr_eager(&thunk.expr, &thunk.module)?;
                        *thunk.module.borrow_mut().map.get_mut(&what.data).unwrap() = value.clone();
                        value
                    }
                    value => value,
                })
            }
            _ => self.eval_expr_lazy(expr, module),
        }
    }

    fn eval_module(source_name: String, definitions: &[(String, Ranged<Expression>)]) -> Module {
        let module = value::new_module(source_name, HashMap::default());

        for (name, expr) in definitions {
            // let value = self.eval_expr(expr, &module)?;
            let value = Value::Thunk(value::new_thunk(expr.clone(), module.clone()));
            module.borrow_mut().map.insert(name.clone(), value);
        }

        module
    }

    pub fn eval_main(
        &mut self,
        source_name: String,
        definitions: &[(String, Ranged<Expression>)],
    ) -> EvaluationResult<Value> {
        let module = Self::eval_module(source_name, definitions);

        let main = module
            .borrow_mut()
            .map
            .remove(&String::from("main"))
            .ok_or_else(|| {
                EvaluationError::basic(BaseEvaluationError::MainIsNotProvided, Default::default())
            })?;

        let Value::Thunk(thunk) = main else {
            unreachable!()
        };

        let Value::Lambda(lambda) = self.eval_expr_eager(&thunk.expr, &thunk.module)? else {
            let ranges = definitions.iter().find(|(ident, _)| ident == "main").unwrap().1.ranges();
            return Err(EvaluationError::basic(BaseEvaluationError::MainMustBeLambda, ranges))
        };

        self.eval_expr_lazy(&lambda.expr, &lambda.module)
            .map_err(|error| {
                let ranges = definitions
                    .iter()
                    .find(|(ident, _)| ident == "main")
                    .unwrap()
                    .1
                    .ranges();
                EvaluationError::complex(
                    BaseEvaluationError::ErrorWhileEvaluatingLambda,
                    ranges,
                    (Box::new(error), lambda.module.borrow().source_name.clone()),
                )
            })
    }
}

#[derive(Debug)]
pub enum BaseEvaluationError {
    PatternCouldntMatch,
    UnboundIdentifier(String),
    ExpectedNumbers(Type, Type),
    ExpectedLambda(Type),
    ExpectedModule(Type),
    ArityMismatch { takes: usize, provided: usize },
    ErrorWhileEvaluatingLambda,
    ErrorWhileImporting,
    MainMustBeLambda,
    MainIsNotProvided,
    UnboundInModule(String),
    ParseError(ParseError),
    IOError(io::Error),
}

impl fmt::Display for BaseEvaluationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PatternCouldntMatch => write!(f, "Pattern couldn't match the value."),
            Self::UnboundIdentifier(ident) => write!(f, "`{ident}` was never bound."),
            Self::ExpectedNumbers(left_type, right_type) => write!(f, "Expected numbers in numerical operation instead found `{left_type}` and `{right_type}`."),
            Self::ExpectedLambda(found) => write!(f, "Expected lambda in application instead found `{found}`."),
            Self::ArityMismatch { takes, provided } => write!(f, "Lambda value takes `{takes}` arguments instead `{provided}` provided."),
            Self::ErrorWhileEvaluatingLambda => write!(f, "An error occured while evaluating the lambda."),
            Self::ErrorWhileImporting => write!(f, "An error occured while importing the module."),
            Self::MainMustBeLambda => write!(f, "`main` must be bound to a lambda value."),
            Self::MainIsNotProvided => write!(f, "`main` is not bound."),
            Self::ExpectedModule(found) => write!(f, "Expeceted module in access instead found {found}."),
            Self::UnboundInModule(ident) => write!(f, "`{ident}` is not bound in the module value."),
            Self::ParseError(error) => write!(f, "{error}"),
            Self::IOError(error) => write!(f, "{error}"),
        }
    }
}

#[derive(Debug)]
pub struct EvaluationError {
    pub error: Ranged<BaseEvaluationError>,
    pub origin: Option<(Box<EvaluationError>, String)>,
}

impl EvaluationError {
    pub const fn complex(
        error: BaseEvaluationError,
        ranges: Ranges,
        origin: (Box<Self>, String),
    ) -> Self {
        Self {
            error: Ranged::new(error, ranges),
            origin: Some(origin),
        }
    }

    pub const fn basic(error: BaseEvaluationError, ranges: Ranges) -> Self {
        Self {
            error: Ranged::new(error, ranges),
            origin: None,
        }
    }

    pub fn report(&self, source_name: &str, source: &str) {
        if matches!(&self.error.data, BaseEvaluationError::MainIsNotProvided) {
            todo!()
        }

        error::report(&self.error, source_name, source, "evaluation");

        if let Some((error, source_name)) = &self.origin {
            eprintln!("      ! | Originates from");
            let source = match fs::read_to_string(source_name) {
                Ok(source) => source,
                Err(error) => return error::report_file_read(&error, source_name),
            };
            error.report(source_name, &source);
        }
    }
}

type EvaluationResult<T> = Result<T, EvaluationError>;
