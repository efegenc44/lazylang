use std::{
    collections::HashMap,
    env::args,
    fs,
    io::{self, Write},
};

use evaluator::Evaluator;

use crate::{parser::Parser, tokens::Tokens};

mod error;
mod evaluator;
mod parser;
mod ranged;
mod tokens;
mod value;

fn main() -> io::Result<()> {
    match &args().collect::<Vec<_>>()[1..] {
        [] => repl(),
        [file_path, ..] => {
            from_file(file_path);
            Ok(())
        }
    }
}

fn from_file(file_path: &str) {
    let source = match fs::read_to_string(file_path) {
        Ok(source) => source,
        Err(error) => return error::report_file_read(&error, file_path),
    };
    let tokens = Tokens::new(&source);
    let definitions = match Parser::new(tokens).parse_module() {
        Ok(definitions) => definitions,
        Err(error) => return error.report(file_path, &source),
    };
    match Evaluator::new().eval_main(file_path.to_string(), &definitions) {
        Ok(value) => println!("= {value}"),
        Err(error) => error.report(file_path, &source),
    }
}

fn repl() -> io::Result<()> {
    let mut evaluator = Evaluator::new();

    let mut stdout = io::stdout();
    let stdin = io::stdin();
    let module = value::new_module(String::new(), HashMap::with_capacity(0));
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
                error.report("REPL", input);
                continue;
            }
        };

        let value = match evaluator.eval_expr_lazy(&expr, &module) {
            Ok(value) => value,
            Err(error) => {
                error.report("REPL", input);
                continue;
            }
        };

        println!("= {value}");
    }

    Ok(())
}
