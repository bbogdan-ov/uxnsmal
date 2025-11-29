use std::{fs::File, io::Write, path::PathBuf};

use uxnsmal::{
	compiler::Compiler, lexer::Lexer, parser::Parser, problems::Problems, reporter::Reporter,
	typechecker::Typechecker,
};

fn main() {
	let path = PathBuf::from(std::env::args().nth(1).unwrap());
	let file = std::fs::read_to_string(&path).unwrap();

	match compile(&file) {
		Ok(_) => (),
		Err(problems) => {
			eprint!("{}", Reporter::new(&problems, &file, &path));
			std::process::exit(1);
		}
	}
}

fn compile(source: &str) -> Result<Problems, Problems> {
	let tokens = Lexer::lex(source).map_err(Problems::one_err)?;
	let ast = Parser::parse(source, &tokens).map_err(Problems::one_err)?;
	let (program, mut problems) = Typechecker::check(&ast)?;
	let bytecode = match Compiler::compile(&program) {
		Ok(bytecode) => bytecode,
		Err(e) => {
			problems.err(e);
			return Err(problems);
		}
	};

	let mut file = File::options()
		.write(true)
		.create(true)
		.truncate(true)
		.open("./output.rom")
		.unwrap();
	file.write_all(&bytecode.opcodes).unwrap();

	Ok(problems)
}
