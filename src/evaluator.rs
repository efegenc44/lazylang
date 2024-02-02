use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    parser::{BinaryOp, Expression, Parser, Pattern},
    ranged::Ranged,
    tokens::Tokens,
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

        match module.map.borrow().get(expected) {
            Some(value) => Ok(value.clone()),
            None => Err(Ranged::new(
                EvaluationError::UnboundIdentifier(expected.to_string()),
                start,
                end,
            )),
        }
    }

    fn check_pattern(pattern: &Ranged<Pattern>, value: &Value) -> bool {
        match (&pattern.data, value) {
            (Pattern::NaturalNumber(nat), Value::Integer(int)) => {
                &nat.parse::<isize>().unwrap() == int
            }
            (
                Pattern::Pair { first, second },
                Value::Pair {
                    first: first_value,
                    second: second_value,
                },
            ) => {
                Self::check_pattern(first, first_value) && Self::check_pattern(second, second_value)
            }
            (Pattern::All(_), _) => true,
            _ => false,
        }
    }

    fn define_pattern_locals(&mut self, pattern: &Ranged<Pattern>, value: Value) {
        match (&pattern.data, value) {
            (Pattern::All(ident), value) => {
                self.locals.push((ident.clone(), value));
            }
            (
                Pattern::Pair { first, second },
                Value::Pair {
                    first: first_value,
                    second: second_value,
                },
            ) => {
                self.define_pattern_locals(first, *first_value);
                self.define_pattern_locals(second, *second_value);
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
        let (lvalue, rvalue) = (self.eval_expr(lhs, module)?, self.eval_expr(rhs, module)?);

        Ok(match bop {
            BinaryOp::Addition => {
                let (lhs, rhs) = match (lvalue, rvalue) {
                    (Value::Integer(lint), Value::Integer(rint)) => (lint, rint),
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
                let (lhs, rhs) = match (lvalue, rvalue) {
                    (Value::Integer(lint), Value::Integer(rint)) => (lint, rint),
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
            BinaryOp::Pairing => Value::Pair {
                first: Box::new(lvalue),
                second: Box::new(rvalue),
            },
        })
    }

    fn eval_let(
        &mut self,
        pattern: &Ranged<Pattern>,
        vexpr: &Ranged<Expression>,
        rexpr: &Ranged<Expression>,
        module: &Module,
    ) -> EvaluationResult<Value> {
        let value = self.eval_expr(vexpr, module)?;
        let true = Self::check_pattern(pattern, &value) else {
            return Err(Ranged::new(EvaluationError::UnmatchedPattern, pattern.start, pattern.end))
        };
        let local_len = self.locals.len();
        self.define_pattern_locals(pattern, value);
        let result = self.eval_expr(rexpr, module);
        self.locals.truncate(local_len);
        result
    }

    fn eval_application(
        &mut self,
        expr: &Ranged<Expression>,
        arguments: &[Ranged<Expression>],
        module: &Module,
    ) -> EvaluationResult<Value> {
        let Value::Function { closure, arguments: farguments, expr: fexpr, module: func_module } = self.eval_expr(expr, module)? else {
            return Err(Ranged::new(EvaluationError::ExpectedFunction, expr.start, expr.end))
        };

        if arguments.len() != farguments.len() {
            return Err(Ranged::new(
                EvaluationError::ArityMismatch,
                expr.start,
                expr.end,
            ));
        }

        let local_len = self.locals.len();
        self.locals.extend(closure);
        for (argument, pattern) in arguments.iter().zip(farguments) {
            let value = self.eval_expr(argument, &func_module)?;
            let true = Self::check_pattern(&pattern, &value) else {
                return Err(Ranged::new(EvaluationError::UnmatchedPattern, pattern.start, pattern.end))
            };
            self.define_pattern_locals(&pattern, value);
        }
        let result = self.eval_expr(&fexpr, &func_module);
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

        let map = module.map.borrow();
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
                vexpr,
                rexpr,
            } => self.eval_let(pattern, vexpr, rexpr, module),
            Expression::Function {
                args: arguments,
                expr,
            } => Ok(Value::Function {
                closure: self.locals.clone(),
                arguments: arguments.clone(),
                expr: *expr.clone(),
                module: module.clone(),
            }),
            Expression::Application {
                expr,
                args: arguments,
            } => self.eval_application(expr, arguments, module),
            Expression::Import(parts) => self.eval_import(parts, module),
            Expression::Access { from, what } => self.eval_access(from, what, module),
        }
    }

    fn eval_module(
        &mut self,
        source: String,
        definitions: &[(String, Ranged<Expression>)],
    ) -> EvaluationResult<Module> {
        let module = Module {
            source,
            map: Default::default(),
        };

        for (name, expr) in definitions {
            let value = self.eval_expr(expr, &module)?;
            module.map.borrow_mut().insert(name.clone(), value);
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
            .map
            .borrow_mut()
            .remove(&String::from("main"))
            .expect("Symbol main is not provided.");
        let Value::Function { closure: _, arguments: _, expr, module: func_module } = main else {
            panic!("main is not function");
        };

        self.eval_expr(&expr, &func_module)
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

#[derive(Clone)]
pub struct Module {
    pub source: String,
    pub map: Rc<RefCell<HashMap<String, Value>>>,
}

#[derive(Clone)]
pub enum Value {
    Integer(isize),
    Pair {
        first: Box<Value>,
        second: Box<Value>,
    },
    Function {
        closure: Vec<(String, Value)>,
        arguments: Vec<Ranged<Pattern>>,
        expr: Ranged<Expression>,
        module: Module,
    },
    Module(Module),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(int) => write!(f, "{int}"),
            Self::Pair { first, second } => write!(f, "({first}:{second})"),
            Self::Function { .. } => write!(f, "<function>"),
            Self::Module(_) => write!(f, "<module>"),
        }
    }
}
