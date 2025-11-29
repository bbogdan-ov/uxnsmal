use uxnsmal::{
	error::Error,
	lexer::{Lexer, Token},
};

mod text_testing;

struct LexerTextTester {
	source_skip: Option<usize>,
}
impl text_testing::TextTester for LexerTextTester {
	type Return = Vec<Token>;
	type Error = Error;

	fn new() -> Self {
		Self {
			source_skip: Some(0),
		}
	}

	fn test(&mut self, source: &str) -> Option<Result<Self::Return, Self::Error>> {
		let skip = self.source_skip?;

		match Lexer::lex_with_skip(source, skip) {
			// No tokens or only Eof
			Ok(t) if t.len() <= 1 => None,
			Ok(t) => Some(Ok(t)),
			Err(e) => {
				self.source_skip = e.span().map(|s| s.end);
				Some(Err(e))
			}
		}
	}
}

#[test]
fn lexer_text_tests() {
	text_testing::make_text_tests::<LexerTextTester>("tests/lexer");
}
