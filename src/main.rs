mod evaluator;
mod parser;
mod ranged;
mod tokens;

fn main() {
    let code = "(1 + 5) * 6 * 8 + 7";
    let tokens = tokens::Tokens::new(code);
    let mut parser = parser::Parser::new(tokens);
    let mut engine = evaluator::Evaluator::new();
    println!("{}", engine.eval(parser.parse().unwrap()));
}
