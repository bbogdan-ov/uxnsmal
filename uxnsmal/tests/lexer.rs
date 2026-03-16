use uxnsmal::{lexer::Token, problem::Problem};

mod text_testing;

struct LexerTextTester {}
impl text_testing::TextTester for LexerTextTester {
	type Return = Vec<Token>;
	type Error = Problem;

	fn new() -> Self {
		Self {}
	}

	fn test(&mut self, _source: &str) -> Option<Result<Self::Return, Self::Error>> {
		todo!("text lexer")
	}
}

#[test]
fn lexer_text_tests() {
	text_testing::make_text_tests::<LexerTextTester>("tests/lexer");
}
