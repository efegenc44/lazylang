use std::{
    collections::HashMap,
    env::args,
    fs,
    io::{self, Write},
};

use evaluator::Evaluator;
use value::Value;

use crate::{parser::Parser, tokens::Tokens};

mod evaluator;
mod parser;
mod ranged;
mod tokens;
mod value;

fn main() -> io::Result<()> {
    match &args().collect::<Vec<_>>()[1..] {
        [] => repl(),
        [file_path, ..] => from_file(file_path),
    }
}

fn from_file(file_path: &str) -> io::Result<()> {
    let file = fs::read_to_string(file_path)?;
    let tokens = Tokens::new(&file);
    let module = Parser::new(tokens).parse_module().unwrap();
    println!(
        "{}",
        Evaluator::new()
            .eval_main(file_path.to_string(), &module)
            .unwrap()
    );
    Ok(())
}

fn repl() -> io::Result<()> {
    let mut evaluator = Evaluator::new();

    let mut stdout = io::stdout();
    let stdin = io::stdin();
    let module = Value::new_module(String::new(), HashMap::with_capacity(0));
    loop {
        print!("> ");
        stdout.flush()?;

        let mut input = String::new();
        stdin.read_line(&mut input)?;
        let input = input.trim_end();

        match input {
            ".exit" => break,
            "" => continue,
            _ => (),
        }

        let tokens = Tokens::new(input);
        let mut parser = Parser::new(tokens);

        let expr = match parser.parse_expr() {
            Ok(expr) => expr,
            Err(error) => {
                println!("{error:?}");
                continue;
            }
        };

        let value = match evaluator.eval_expr(&expr, &module) {
            Ok(value) => value,
            Err(error) => {
                println!("{error:?}");
                continue;
            }
        };

        println!("= {value}");
    }

    Ok(())
}
