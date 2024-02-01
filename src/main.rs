mod parser;
mod ranged;
mod tokens;

fn main() {
    let code = "1 + 5 ^ 6 * 8 ^ 7";
    let tokens = tokens::Tokens::new(code);
    let mut parser = parser::Parser::new(tokens);

    match parser.parse() {
        Ok(expr) => expr.data.pretty_print(0),
        Err(error) => println!("{error:?}"),
    };
}
