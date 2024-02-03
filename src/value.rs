use core::fmt;
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
    pub fn pair(first: Self, second: Self) -> Self {
        Self::Pair(Rc::new(PairInstance {
            first: Box::new(first),
            second: Box::new(second),
        }))
    }

    pub fn lambda(
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

    pub const fn typ(&self) -> Type {
        match self {
            Self::Integer(_) => Type::Integer,
            Self::Pair(_) => Type::Pair,
            Self::Lambda(_) => Type::Lambda,
            Self::Module(_) => Type::Module,
        }
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
    pub source_name: String,
    pub map: HashMap<String, Value>,
}
pub type Module = Rc<RefCell<ModuleInstance>>;

pub fn new_module(source: String, map: HashMap<String, Value>) -> Module {
    Rc::new(RefCell::new(ModuleInstance {
        source_name: source,
        map,
    }))
}

#[derive(Debug)]
pub enum Type {
    Integer,
    Pair,
    Lambda,
    Module,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer => write!(f, "Integer"),
            Self::Pair => write!(f, "Pair"),
            Self::Lambda => write!(f, "Lambda"),
            Self::Module => write!(f, "Module"),
        }
    }
}
