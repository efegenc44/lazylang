use std::collections::HashMap;

use crate::{evaluator::EvaluationError, value::Value};

macro_rules! map {
    ($($name:ident -> $lambda:expr)*) => {
        HashMap::from([$((String::from(stringify!($name)), Value::Native($lambda))),*])
    };
}

pub fn get_map() -> HashMap<String, Value> {
    map! {
        println -> |evaluator, module, args| {
            for arg in args {
                println!("{}", evaluator.eval_expr_eager(arg, module)?);
            }
            Ok(Value::Unit)
        }

        panic -> |_, _, _| {
            Err(EvaluationError::native_error("Paniced!"))
        }
    }
}
