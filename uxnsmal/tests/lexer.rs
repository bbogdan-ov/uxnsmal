use uxnsmal::lexer::{Keyword as Kw, Lexer, Radix, TokenKind::*};

macro_rules! parse {
	(
		$(
			$s:expr => [ $($expect:expr),*$(,)? ]
		);*$(;)?
	) => {$({
		const S: &str = $s;

		let expect = [$($expect,)*];

		let tokens = Lexer::parse(S).unwrap();
		assert_eq!(tokens.len(), expect.len());
		for idx in 0..expect.len() {
			let tok = &tokens[idx];
			let slice = &S[tok.span.into_range()];

			assert_eq!((slice, tok.kind), expect[idx]);
		}
	})*};
}

#[test]
#[rustfmt::skip]
fn lexer_all_tokens() {
	parse! {
		r#"
			const hey var a
			data b

			$0o77

			fun my-vec ( -> ) {}
			fun my-func ( -- ) {
				10 20*hello

				loop @label {
					jump@label jumpif @label
					0b101 0xff add pop
				}
				@block {}

				"my-string!!"
				"esc\"apes\" 'char' \\"
				'a'
				'ab\n'
				'\\'
			}
		"#

		=> [
			("const", Keyword(Kw::Const)),
			("hey", Ident),
			("var", Keyword(Kw::Var)),
			("a", Ident),
			("data", Keyword(Kw::Data)),
			("b", Ident),

			("$", Dollar),
			("0o77", Number(Radix::Octal)),

			("fun", Keyword(Kw::Func)),
			("my-vec", Ident),
			("(", OpenParen),
			("->", ArrowRight),
			(")", CloseParen),
			("{", OpenBrace),
			("}", CloseBrace),

			("fun", Keyword(Kw::Func)),
			("my-func", Ident),
			("(", OpenParen),
			("--", DoubleDash),
			(")", CloseParen),
			("{", OpenBrace),
				("10", Number(Radix::Decimal)),
				("20", Number(Radix::Decimal)),
				("*", Asterisk),
				("hello", Ident),

				("loop", Keyword(Kw::Loop)),
				("@", AtSign),
				("label", Ident),
				("{", OpenBrace),
					("jump", Keyword(Kw::Jump)),
					("@", AtSign),
					("label", Ident),
					("jumpif", Keyword(Kw::JumpIf)),
					("@", AtSign),
					("label", Ident),
					("0b101", Number(Radix::Binary)),
					("0xff", Number(Radix::Hexadecimal)),
					("add", Ident),
					("pop", Ident),
				("}", CloseBrace),
				("@", AtSign),
				("block", Ident),
				("{", OpenBrace),
				("}", CloseBrace),

				(r#""my-string!!""#, String),
				(r#""esc\"apes\" 'char' \\""#, String),
				(r#"'a'"#, Char),
				(r#"'ab\n'"#, Char),
				(r#"'\\'"#, Char),
			("}", CloseBrace),
			("", Eof),
		]
	}
}
