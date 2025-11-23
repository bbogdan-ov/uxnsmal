use uxnsmal::{
	compiler::Compiler, error, lexer::Lexer, opcodes::Bytecode, parser::Parser, program::Program,
	typechecker::Typechecker,
};

mod text_testing;

struct TypecheckerTextTester {
	first: bool,
}
impl text_testing::TextTester for TypecheckerTextTester {
	type Type = (Program, Bytecode);

	fn new() -> Self {
		Self { first: true }
	}

	fn test(&mut self, source: &str) -> Option<error::Result<Self::Type>> {
		if !self.first {
			return None;
		}
		self.first = false;

		let tokens = match Lexer::lex(source) {
			Ok(t) => t,
			Err(e) => return Some(Err(e)),
		};

		let ast = match Parser::parse(source, &tokens) {
			Ok(ast) if ast.nodes.is_empty() => return None,
			Ok(ast) => ast,
			Err(e) => return Some(Err(e)),
		};

		let program = match Typechecker::check(&ast) {
			Ok(program) => program,
			Err(e) => return Some(Err(e)),
		};
		let bytecode = match Compiler::compile(&program) {
			Ok(bytecode) => bytecode,
			Err(e) => return Some(Err(e)),
		};

		Some(Ok((program, bytecode)))
	}
}

#[test]
fn typechecker_text_tests() {
	text_testing::make_text_tests::<TypecheckerTextTester>("tests/typechecker");
}
