use std::{fs::File, io::Write, path::PathBuf};

use uxnsmal::{
	compiler::Compiler, context::Context, error::FatalError, lexer::Lexer, parser::Parser,
	reporter::Reporter, typechecker::Typechecker,
};

fn main() {
	let path = PathBuf::from(std::env::args().nth(1).unwrap());
	let file = std::fs::read_to_string(&path).unwrap();

	let mut ctx = Context::default();

	match compile(&mut ctx, &file) {
		Ok(()) => {
			eprint!("{}", Reporter::new(&ctx.problems, &file, &path));
		}
		Err(FatalError) => {
			eprint!("{}", Reporter::new(&ctx.problems, &file, &path));
			std::process::exit(1);
		}
	}
}

fn compile(ctx: &mut Context, source: &str) -> Result<(), FatalError> {
	let tokens = Lexer::lex(source).map_err(|_| todo!())?;
	let mut ast = Parser::parse(source, &tokens).map_err(|_| todo!())?;
	let program = Typechecker::check(ctx, &mut ast)?;
	let bytecode = Compiler::compile(&program).map_err(|_| todo!())?;

	let mut file = File::options()
		.write(true)
		.create(true)
		.truncate(true)
		.open("./output.rom")
		.unwrap();
	file.write_all(&bytecode.opcodes).unwrap();

	Ok(())
}
