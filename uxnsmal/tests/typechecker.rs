use uxnsmal::{
	compiler::Compiler, lexer::Lexer, opcodes::Bytecode, parser::Parser, problem::Problems,
	program::Program, typechecker::Typechecker,
};

mod text_testing;

// TODO: include scopes, symbols and other typechecker states into expected outputs

struct TypecheckerTextTester {
	first: bool,
}
impl text_testing::TextTester for TypecheckerTextTester {
	type Return = (Program, Bytecode, Problems);
	type Error = Problems;

	fn new() -> Self {
		Self { first: true }
	}

	fn test(&mut self, source: &str) -> Option<Result<Self::Return, Self::Error>> {
		todo!("test typechecker")
	}
}

#[test]
fn typechecker_text_tests() {
	text_testing::make_text_tests::<TypecheckerTextTester>("tests/typechecker");
}
