mod ast;
mod bytecode;
mod compiler;
mod error;
mod lexer;
mod parser;
mod program;
mod reporter;
mod symbols;
mod typechecker;

use std::path::PathBuf;

use bytecode::Bytecode;
use compiler::Compiler;
use lexer::Lexer;
use parser::Parser;
use reporter::Reporter;
use symbols::SymbolsTable;
use typechecker::Typechecker;

fn main() {
	let path = PathBuf::from(std::env::args().nth(1).unwrap());
	let file = std::fs::read_to_string(&path).unwrap();

	let bytecode = match compile(&file) {
		Ok(res) => res,
		Err(err) => {
			eprint!("{}", Reporter::new(&err, &file, &path));
			std::process::exit(1);
		}
	};

	println!("{bytecode:?}");

	let mut out_file = std::fs::File::options()
		.write(true)
		.create(true)
		.truncate(true)
		.open("output.rom")
		.unwrap();

	out_file.set_len(0).unwrap();
	bytecode.write_to(&mut out_file).unwrap();
}

fn compile(source: &str) -> error::Result<Bytecode> {
	let mut symbols = SymbolsTable::default();

	let tokens = Lexer::parse(source)?;
	let ast = Parser::parse(source, &tokens)?;
	let program = Typechecker::check(ast, &mut symbols)?;
	Compiler::new(&program).compile()
}
