use std::path::PathBuf;

use uxnsmal::{error, lexer::Lexer, parser::Parser, reporter::Reporter, typechecker::Typechecker};

fn main() {
	let path = PathBuf::from(std::env::args().nth(1).unwrap());
	let file = std::fs::read_to_string(&path).unwrap();

	match compile(&file) {
		Ok(_) => (),
		Err(err) => {
			eprint!("{}", Reporter::new(&err, &file, &path));
			std::process::exit(1);
		}
	}
}

fn compile(source: &str) -> error::Result<()> {
	let tokens = Lexer::lex(source)?;
	let ast = Parser::parse(source, &tokens)?;
	let typed_ast = Typechecker::check(ast)?;
	dbg!(typed_ast);
	Ok(())
	// let program = Generator::generate(&typed_ast, symbols)?;
	// Compiler::compile(&program)
}
