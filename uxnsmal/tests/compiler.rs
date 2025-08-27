use uxnsmal::{compiler::Compiler, lexer::Lexer, parser::Parser, typechecker::Typechecker};

#[test]
fn examples_compilation() {
	macro_rules! example {
		($file:expr) => {
			(
				$file,
				include_str!(concat!("../../examples/", $file)),
				include_str!(concat!("../../examples/", $file, ".txt")),
			)
		};
	}

	#[rustfmt::skip]
	let sources = [
		example!("mouse.smal"),
		example!("hello.smal"),
	];

	for (name, src, expect) in sources {
		let tokens = Lexer::lex(src).unwrap();
		let ast = Parser::parse(src, &tokens).unwrap();
		let program = Typechecker::check(ast).unwrap();
		let bytecode = Compiler::compile(&program).unwrap();

		let found = format!("{bytecode:?}");

		assert!(found == expect, "unexpected bytecode output for {name:?}");
	}
}
