use uxnsmal::{
	ast::Ast,
	error::Error,
	lexer::{Lexer, Token, TokenKind},
	parser::Parser,
};

mod text_testing;

struct AstTextTester {
	tokens: Option<Vec<Token>>,
	cur_token_idx: Option<usize>,
}
impl text_testing::TextTester for AstTextTester {
	type Return = Ast;
	type Error = Error;

	fn new() -> Self {
		Self {
			tokens: None,
			cur_token_idx: Some(0),
		}
	}

	fn test(&mut self, source: &str) -> Option<Result<Self::Return, Self::Error>> {
		let Some(cur_idx) = self.cur_token_idx else {
			return None;
		};

		if self.tokens.is_none() {
			self.tokens = match Lexer::lex(source) {
				Ok(t) => Some(t),
				Err(e) => {
					self.cur_token_idx = None;
					return Some(Err(e));
				}
			};
		}

		let tokens = self.tokens.as_ref().unwrap();

		match Parser::parse(source, &tokens[cur_idx..]) {
			Ok(a) if a.nodes.is_empty() => None,
			Ok(a) => {
				self.cur_token_idx = None;
				Some(Ok(a))
			}
			Err(e) => {
				self.cur_token_idx = tokens[cur_idx..]
					.iter()
					.skip(1) // skip current comment
					.position(|t| t.kind == TokenKind::Comment)
					.map(|i| cur_idx + 1 + i);

				Some(Err(e))
			}
		}
	}
}

#[test]
fn ast_text_tests() {
	text_testing::make_text_tests::<AstTextTester>("tests/ast");
}
