use core::fmt;
use std::{collections::HashMap, fs, io};

use crate::{
    error,
    parser::{BinaryOp, Expression, ParseError, Parser, Pattern},
    ranged::{Ranged, Ranges},
    tokens::Tokens,
    value::{self, Lambda, Module, Type, Value},
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
            (Pattern::Or { right, left }, value) => (self.check_pattern(right, value).is_ok()
                || self.check_pattern(left, value).is_ok())
            .then_some(())
            .ok_or_else(|| {
                EvaluationError::basic(BaseEvaluationError::PatternCouldntMatch, pattern.ranges())
            }),
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
            (Pattern::Or { right, left }, value) => {
                if self.check_pattern(right, &value).is_ok() {
                    self.define_pattern_locals(right, value)
                } else {
                    self.define_pattern_locals(left, value)
                }
            }
            (_, Value::Thunk(thunk)) => {
                let value = self.eval_expr_lazy(&thunk.expr, &thunk.module)?;
                self.define_pattern_locals(pattern, value)
            }
            _ => Ok(()),
        }
    }

    fn expect_boolean(
        &mut self,
        expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<bool> {
        let value = self.eval_expr_eager(expr, module)?;
        match value {
            Value::Boolean(bool) => Ok(bool),
            _ => Err(EvaluationError::basic(
                BaseEvaluationError::TypeMismatch {
                    expected: Type::Boolean,
                    found: value.typ(),
                },
                expr.ranges(),
            )),
        }
    }

    fn expect_lambda(
        &mut self,
        expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Lambda> {
        let value = self.eval_expr_eager(expr, module)?;
        match value {
            Value::Lambda(lambda) => Ok(lambda),
            _ => Err(EvaluationError::basic(
                BaseEvaluationError::TypeMismatch {
                    expected: Type::Lambda,
                    found: value.typ(),
                },
                expr.ranges(),
            )),
        }
    }

    fn expect_module(
        &mut self,
        expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Module> {
        let value = self.eval_expr_eager(expr, module)?;
        match value {
            Value::Module(module) => Ok(module),
            _ => Err(EvaluationError::basic(
                BaseEvaluationError::TypeMismatch {
                    expected: Type::Module,
                    found: value.typ(),
                },
                expr.ranges(),
            )),
        }
    }

    fn expect_number(
        &mut self,
        expr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let value = self.eval_expr_eager(expr, module)?;
        match value {
            Value::Integer(_) => Ok(value),
            _ => Err(EvaluationError::basic(
                BaseEvaluationError::ExpectedNumber(value.typ()),
                expr.ranges(),
            )),
        }
    }

    fn value_equality(
        &mut self,
        left_value: &Value,
        right_value: &Value,
    ) -> EvaluationResult<bool> {
        match (left_value, right_value) {
            (Value::Integer(left_int), Value::Integer(right_int)) => Ok(left_int == right_int),
            (Value::Pair(left_pair), Value::Pair(right_pair)) => Ok(self
                .value_equality(&left_pair.first, &right_pair.first)?
                && self.value_equality(&left_pair.second, &right_pair.second)?),
            (Value::Boolean(left_bool), Value::Boolean(right_bool)) => Ok(left_bool == right_bool),
            (Value::Thunk(thunk), other) | (other, Value::Thunk(thunk)) => {
                let value = self.eval_expr_lazy(&thunk.expr, &thunk.module)?;
                self.value_equality(&value, other)
            }
            _ => Ok(false),
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
                match (
                    self.expect_number(lhs, module)?,
                    self.expect_number(lhs, module)?,
                ) {
                    (Value::Integer(left_int), Value::Integer(right_int)) => {
                        Value::Integer(left_int + right_int)
                    }
                    _ => unreachable!(),
                }
            }
            BinaryOp::Multiplication => {
                match (
                    self.expect_number(lhs, module)?,
                    self.expect_number(lhs, module)?,
                ) {
                    (Value::Integer(left_int), Value::Integer(right_int)) => {
                        Value::Integer(left_int * right_int)
                    }
                    _ => unreachable!(),
                }
            }
            BinaryOp::Pairing => Value::pair(
                self.eval_expr_lazy(lhs, module)?,
                self.eval_expr_lazy(rhs, module)?,
            ),
            BinaryOp::Equivalence => {
                let left_value = self.eval_expr_lazy(lhs, module)?;
                let right_value = self.eval_expr_lazy(rhs, module)?;
                Value::Boolean(self.value_equality(&left_value, &right_value)?)
            }
            BinaryOp::NonEquivalence => {
                let left_value = self.eval_expr_lazy(lhs, module)?;
                let right_value = self.eval_expr_lazy(rhs, module)?;
                Value::Boolean(!self.value_equality(&left_value, &right_value)?)
            }
            BinaryOp::BooleanOr => {
                if self.expect_boolean(lhs, module)? == true {
                    Value::Boolean(true)
                } else {
                    Value::Boolean(self.expect_boolean(rhs, module)?)
                }
            }
            BinaryOp::BooleanAnd => {
                if self.expect_boolean(lhs, module)? == false {
                    Value::Boolean(false)
                } else {
                    Value::Boolean(self.expect_boolean(rhs, module)?)
                }
            }
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
        let lambda = self.expect_lambda(expr, module)?;

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
        let module = self.expect_module(from, module)?;

        let map = &module.borrow().map;
        let Some(value) = map.get(&what.data) else {
            return Err(EvaluationError::basic(BaseEvaluationError::UnboundInModule(what.data.clone()), what.ranges()))
        };

        Ok(value.clone())
    }

    fn eval_match(
        &mut self,
        expr: &Ranged<Expression>,
        branches: &[(Ranged<Pattern>, Box<Ranged<Expression>>)],
        ranges: Ranges,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let value = self.eval_expr_lazy(expr, module)?;

        for (pattern, branch_expr) in branches {
            if self.check_pattern(pattern, &value).is_ok() {
                let locals_len = self.locals.len();
                self.define_pattern_locals(pattern, value)?;
                let result = self.eval_expr_lazy(branch_expr, module);
                self.locals.truncate(locals_len);
                return result;
            }
        }

        Err(EvaluationError::basic(
            BaseEvaluationError::NonExhaustiveMatch,
            ranges,
        ))
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
            Expression::Match {
                expr: match_expr,
                branches,
            } => self.eval_match(match_expr, branches, expr.ranges(), module),
            Expression::Boolean(bool) => Ok(Value::Boolean(*bool)),
            Expression::Unit => Ok(Value::Unit),
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
    ExpectedNumber(Type),
    ArityMismatch { takes: usize, provided: usize },
    ErrorWhileEvaluatingLambda,
    ErrorWhileImporting,
    MainMustBeLambda,
    MainIsNotProvided,
    UnboundInModule(String),
    ParseError(ParseError),
    IOError(io::Error),
    NonExhaustiveMatch,
    TypeMismatch { expected: Type, found: Type },
}

impl fmt::Display for BaseEvaluationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PatternCouldntMatch => write!(f, "Pattern couldn't match the value."),
            Self::UnboundIdentifier(ident) => write!(f, "`{ident}` was never bound."),
            Self::ExpectedNumber(found) => write!(f, "Expected number instead found `{found}`."),
            Self::ArityMismatch { takes, provided } => write!(
                f,
                "Lambda value takes `{takes}` arguments instead `{provided}` provided."
            ),
            Self::ErrorWhileEvaluatingLambda => {
                write!(f, "An error occured while evaluating the lambda.")
            }
            Self::ErrorWhileImporting => write!(f, "An error occured while importing the module."),
            Self::MainMustBeLambda => write!(f, "`main` must be bound to a lambda value."),
            Self::MainIsNotProvided => write!(f, "`main` is absent."),
            Self::UnboundInModule(ident) => {
                write!(f, "`{ident}` is not bound in the module value.")
            }
            Self::ParseError(error) => write!(f, "{error}"),
            Self::IOError(error) => write!(f, "{error}"),
            Self::NonExhaustiveMatch => write!(
                f,
                "Value couldn't match any of the patterns in the match expression."
            ),
            Self::TypeMismatch { expected, found } => {
                write!(f, "Expected `{expected}` instead found `{found}`.")
            }
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
            error::report_absent_main(&self.error.data, source_name);
        } else {
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
}

type EvaluationResult<T> = Result<T, EvaluationError>;
