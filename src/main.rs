mod tokens;

fn main() {
    let code = "2 * (4 + 5)";
    let tokens = tokens::Tokens::new(code);
    for token in tokens {
        println!("{token:?}");
    }
}
