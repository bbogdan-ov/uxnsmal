use std::{fs::File, io::Write, path::PathBuf};

use uxnsmal::{
	compiler::Compiler,
	lexer::Lexer,
	parser::Parser,
	problem::{FatalError, Problems},
	reporter::Reporter,
	typechecker::Typechecker,
};

fn main() {
	let path = PathBuf::from(std::env::args().nth(1).unwrap());
	let file = std::fs::read_to_string(&path).unwrap();

	let mut problems = Problems::default();

	match compile(&mut problems, &file) {
		Ok(()) => {
			eprint!("{}", Reporter::new(&problems, &file, &path));
		}
		Err(_) => {
			eprint!("{}", Reporter::new(&problems, &file, &path));
			std::process::exit(1);
		}
	}
}

fn compile(problems: &mut Problems, source: &str) -> Result<(), FatalError> {
	let tokens = Lexer::lex(source, problems)?;
	let mut ast = Parser::parse(source, problems, &tokens)?;
	let program = Typechecker::check(&mut ast, problems)?;
	let bytecode = Compiler::compile(&program);

	let mut file = File::options()
		.write(true)
		.create(true)
		.truncate(true)
		.open("./output.rom")
		.unwrap();
	file.write_all(&bytecode.opcodes).unwrap();

	Ok(())
}
