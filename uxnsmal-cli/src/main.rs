use std::{fs::File, io::Write, path::PathBuf};

use uxnsmal::{
	compiler::Compiler, error, generator::Generator, lexer::Lexer, parser::Parser,
	reporter::Reporter, typechecker::Typechecker,
};

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
	let mut ast = Parser::parse(source, &tokens)?;
	let mut symbols = Typechecker::check(&mut ast)?;
	let program = Generator::generate(&ast, &mut symbols)?;
	let bytecode = Compiler::compile(&program)?;

	let mut file = File::options()
		.write(true)
		.create(true)
		.truncate(true)
		.open("./output.rom")
		.unwrap();
	file.write_all(&bytecode.opcodes).unwrap();

	Ok(())
}
