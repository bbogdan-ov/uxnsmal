use std::path::PathBuf;

use uxnsmal::{error, lexer::Lexer, parser::Parser};

fn main() {
	let path = PathBuf::from(std::env::args().nth(1).unwrap());
	let file = std::fs::read_to_string(&path).unwrap();

	compile(&file).expect("something isn't right...");
	// let bytecode = match compile(&file) {
	// 	Ok(res) => res,
	// 	Err(err) => {
	// 		eprint!("{}", Reporter::new(&err, &file, &path));
	// 		std::process::exit(1);
	// 	}
	// };

	// print!("{bytecode:?}");

	// let mut out_file = std::fs::File::options()
	// 	.write(true)
	// 	.create(true)
	// 	.truncate(true)
	// 	.open("output.rom")
	// 	.unwrap();

	// out_file.set_len(0).unwrap();
	// bytecode.write_to(&mut out_file).unwrap();
}

fn compile(source: &str) -> error::Result<()> {
	let tokens = Lexer::lex(source)?;
	let ast = Parser::parse(source, &tokens)?;
	dbg!(ast);
	Ok(())
	// let (typed_ast, symbols) = Typechecker::check(ast)?;
	// let program = Generator::generate(&typed_ast, symbols)?;
	// Compiler::compile(&program)
}
