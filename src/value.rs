use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    parser::{Expression, Pattern},
    ranged::Ranged,
};

#[derive(Clone)]
pub enum Value {
    Integer(isize),
    Pair(Pair),
    Lambda(Lambda),
    Module(Module),
}

impl Value {
    pub fn new_pair_value(first: Self, second: Self) -> Self {
        Self::Pair(Rc::new(PairInstance {
            first: Box::new(first),
            second: Box::new(second),
        }))
    }

    pub fn new_lambda_value(
        captures: Vec<(String, Self)>,
        args: Vec<Ranged<Pattern>>,
        expr: Ranged<Expression>,
        module: Module,
    ) -> Self {
        Self::Lambda(Rc::new(LambdaInstance {
            captures,
            args,
            expr,
            module,
        }))
    }

    pub fn new_module(source: String, map: HashMap<String, Self>) -> Module {
        Rc::new(RefCell::new(ModuleInstance { source, map }))
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(int) => write!(f, "{int}"),
            Self::Pair(pair) => write!(f, "({}:{})", pair.first, pair.second),
            Self::Lambda(_) => write!(f, "<lambda>"),
            Self::Module(_) => write!(f, "<module>"),
        }
    }
}

pub struct PairInstance {
    pub first: Box<Value>,
    pub second: Box<Value>,
}
pub type Pair = Rc<PairInstance>;

pub struct LambdaInstance {
    pub captures: Vec<(String, Value)>,
    pub args: Vec<Ranged<Pattern>>,
    pub expr: Ranged<Expression>,
    pub module: Module,
}
pub type Lambda = Rc<LambdaInstance>;

#[derive(Clone)]
pub struct ModuleInstance {
    pub source: String,
    pub map: HashMap<String, Value>,
}
pub type Module = Rc<RefCell<ModuleInstance>>;
