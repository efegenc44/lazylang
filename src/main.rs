use std::io::{self, Write};

use evaluator::Evaluator;

use crate::{parser::Parser, tokens::Tokens};

mod evaluator;
mod parser;
mod ranged;
mod tokens;

fn main() -> io::Result<()> {
    let mut evaluator = Evaluator::new();

    let mut stdout = io::stdout();
    let stdin = io::stdin();
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

        let expr = match parser.parse() {
            Ok(expr) => expr,
            Err(error) => {
                println!("{error:?}");
                continue;
            }
        };

        let value = match evaluator.eval(&expr) {
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
