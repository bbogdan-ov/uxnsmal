use uxnsmal::{
	compiler::Compiler, lexer::Lexer, opcodes::Bytecode, parser::Parser, problems::Problems,
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
		if !self.first {
			return None;
		}
		self.first = false;

		let tokens = match Lexer::lex(source) {
			Ok(t) => t,
			Err(e) => return Some(Err(Problems::one_err(e))),
		};

		let mut ast = match Parser::parse(source, &tokens) {
			Ok(ast) if ast.nodes.is_empty() => return None,
			Ok(ast) => ast,
			Err(e) => return Some(Err(Problems::one_err(e))),
		};

		let (program, mut problems) = match Typechecker::check(&mut ast) {
			Ok(ret) => ret,
			Err(e) => return Some(Err(e)),
		};
		let bytecode = match Compiler::compile(&program) {
			Ok(bytecode) => bytecode,
			Err(e) => {
				problems.err(e);
				return Some(Err(problems));
			}
		};

		Some(Ok((program, bytecode, problems)))
	}
}

#[test]
fn typechecker_text_tests() {
	text_testing::make_text_tests::<TypecheckerTextTester>("tests/typechecker");
}
