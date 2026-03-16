use uxnsmal::problem::Problems;

mod text_testing;

// TODO: include scopes, symbols and other typechecker states into expected outputs

struct TypecheckerTextTester {}
impl text_testing::TextTester for TypecheckerTextTester {
	type Return = ();
	type Error = Problems;

	fn new() -> Self {
		Self {}
	}

	fn test(&mut self, _source: &str) -> Option<Result<Self::Return, Self::Error>> {
		todo!("test typechecker")
	}
}

#[test]
fn typechecker_text_tests() {
	text_testing::make_text_tests::<TypecheckerTextTester>("tests/typechecker");
}
