use uxnsmal::{
	lexer::{Lexer, Token},
	problem::Problem,
};

mod text_testing;

struct LexerTextTester {
	source_skip: Option<usize>,
}
impl text_testing::TextTester for LexerTextTester {
	type Return = Vec<Token>;
	type Error = Problem;

	fn new() -> Self {
		Self {
			source_skip: Some(0),
		}
	}

	fn test(&mut self, source: &str) -> Option<Result<Self::Return, Self::Error>> {
		todo!("text lexer")
	}
}

#[test]
fn lexer_text_tests() {
	text_testing::make_text_tests::<LexerTextTester>("tests/lexer");
}
