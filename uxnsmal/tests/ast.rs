use uxnsmal::{ast::Ast, problem::Problem};

mod text_testing;

struct AstTextTester {}
impl text_testing::TextTester for AstTextTester {
	type Return = Ast;
	type Error = Problem;

	fn new() -> Self {
		Self {}
	}

	fn test(&mut self, _source: &str) -> Option<Result<Self::Return, Self::Error>> {
		todo!("test ast")
	}
}

#[test]
fn ast_text_tests() {
	text_testing::make_text_tests::<AstTextTester>("tests/ast");
}
