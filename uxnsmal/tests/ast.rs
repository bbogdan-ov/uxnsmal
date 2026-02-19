use uxnsmal::{
	ast::Ast,
	lexer::{Lexer, Token, TokenKind},
	parser::Parser,
	problem::Problem,
};

mod text_testing;

struct AstTextTester {
	tokens: Option<Vec<Token>>,
	cur_token_idx: Option<usize>,
}
impl text_testing::TextTester for AstTextTester {
	type Return = Ast;
	type Error = Problem;

	fn new() -> Self {
		Self {
			tokens: None,
			cur_token_idx: Some(0),
		}
	}

	fn test(&mut self, source: &str) -> Option<Result<Self::Return, Self::Error>> {
		todo!("test ast")
	}
}

#[test]
fn ast_text_tests() {
	text_testing::make_text_tests::<AstTextTester>("tests/ast");
}
