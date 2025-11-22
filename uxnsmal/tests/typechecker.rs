use uxnsmal::{error, lexer::Lexer, parser::Parser, program::Program, typechecker::Typechecker};

mod text_testing;

struct TypecheckerTextTester {
	first: bool,
}
impl text_testing::TextTester for TypecheckerTextTester {
	type Type = Program;

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

		match Typechecker::check(&ast) {
			Ok(program) => Some(Ok(program)),
			Err(e) => Some(Err(e)),
		}
	}
}

#[test]
fn typechecker_text_tests() {
	text_testing::make_text_tests::<TypecheckerTextTester>("tests/typechecker");
}
