use uxnsmal::{
	compiler::Compiler, context::Context, error::FatalError, lexer::Lexer, opcodes::Bytecode,
	parser::Parser, problems::Problems, program::Program, typechecker::Typechecker,
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

		let mut ctx = Context::default();
		let program = match Typechecker::check(&mut ctx, &mut ast) {
			Ok(program) => program,
			Err(FatalError) => return Some(Err(ctx.problems)),
		};
		let bytecode = match Compiler::compile(&program) {
			Ok(code) => code,
			Err(e) => {
				ctx.problems.err(e);
				return Some(Err(ctx.problems));
			}
		};

		Some(Ok((program, bytecode, ctx.problems)))
	}
}

#[test]
fn typechecker_text_tests() {
	text_testing::make_text_tests::<TypecheckerTextTester>("tests/typechecker");
}
