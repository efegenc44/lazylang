mod parser;
mod tokens;
mod ranged;

fn main() {
    let code = "  2 ^ 4 ^ 5  ";
    let tokens = tokens::Tokens::new(code);
    let mut parser = parser::Parser::new(tokens);

    let result = parser.parse();

    println!("{result:?}");
}
