mod evaluator;
mod parser;
mod ranged;
mod tokens;

fn main() {
    let code = "let x = 4 in x * x";
    let tokens = tokens::Tokens::new(code);
    let mut parser = parser::Parser::new(tokens);
    let mut evaluator = evaluator::Evaluator::new();

    let expr = match parser.parse() {
        Ok(expr) => expr,
        Err(error) => return println!("{error:?}"),
    };

    let value = match evaluator.eval(&expr) {
        Ok(value) => value,
        Err(error) => return println!("{error:?}"),
    };

    println!("= {value}");
}
