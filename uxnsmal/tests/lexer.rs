use uxnsmal::{
	error::ErrorKind,
	lexer::{Keyword as Kw, Lexer, Radix, TokenKind::*},
};

macro_rules! parse {
	(
		$($s:expr => $($expect:expr),*$(,)?);*$(;)?
	) => {$({
		const S: &str = $s;

		let expect = [$($expect,)* ("", Eof)];

		let tokens = Lexer::parse(S).unwrap();
		assert_eq!(tokens.len(), expect.len(), "while testing {:?}", expect);
		for idx in 0..expect.len() {
			let tok = &tokens[idx];
			let slice = &S[tok.span.into_range()];

			assert_eq!((slice, tok.kind), expect[idx]);
		}
	})*};
}

macro_rules! parse_error {
	(
		$($s:expr => $expect:expr);*$(;)?
	) => {$({
		const S: &str = $s;
		match Lexer::parse(S) {
			Ok(_) => panic!("found `Ok`, expected `Err()` in {S:?}"),
			Err(e) => assert_eq!(e.kind, $expect),
		}
	})*};
}

#[test]
fn lexer_puncts() {
	parse! {
		"(" => ("(", OpenParen);
		")" => (")", CloseParen);
		"{" => ("{", OpenBrace);
		"}" => ("}", CloseBrace);
		"&" => ("&", Ampersand);
		"*" => ("*", Asterisk);
		"$" => ("$", Dollar);
		"@" => ("@", AtSign);
		"--" => ("--", DoubleDash);
		"->" => ("->", ArrowRight);

		"(){}&*$@--->" =>
			("(", OpenParen), (")", CloseParen),
			("{", OpenBrace), ("}", CloseBrace),
			("&", Ampersand), ("*", Asterisk), ("$", Dollar), ("@", AtSign),
			("--", DoubleDash),
			("->", ArrowRight),
	}
}

#[test]
fn lexer_literals() {
	parse! {
		"0" => ("0", Number(Radix::Decimal));
		"1" => ("1", Number(Radix::Decimal));
		"10" => ("10", Number(Radix::Decimal));
		"255" => ("255", Number(Radix::Decimal));
		"999" => ("999", Number(Radix::Decimal));
		"0xff" => ("0xff", Number(Radix::Hexadecimal));
		"0b1010" => ("0b1010", Number(Radix::Binary));
		"0o1234567" => ("0o1234567", Number(Radix::Octal));
		"0x0123456789ABCDEF" => ("0x0123456789ABCDEF", Number(Radix::Hexadecimal));

		r#"'char!'"# => (r#"'char!'"#, Char);
		r#"'\\'"# => (r#"'\\'"#, Char);
		r#"'\n'"# => (r#"'\n'"#, Char);
		r#""string!""# => (r#""string!""#, String);
		r#"" escape \" ' \\ ""# => (r#"" escape \" ' \\ ""#, String);

		// TODO: should be an error
		"0x" => ("0x", Number(Radix::Hexadecimal));
		"0b" => ("0b", Number(Radix::Binary));
		"0o" => ("0o", Number(Radix::Octal));
	}

	parse_error! {
		"1hey2" => ErrorKind::BadNumber(Radix::Decimal);
		"12hey" => ErrorKind::BadNumber(Radix::Decimal);
		"0xffz" => ErrorKind::BadNumber(Radix::Hexadecimal);
		"0b123" => ErrorKind::BadNumber(Radix::Binary);
		"0o888" => ErrorKind::BadNumber(Radix::Octal);
	}
}

#[test]
fn lexer_symbols() {
	parse! {
		"hello" => ("hello", Ident);
		"hey123" => ("hey123", Ident);
		"h1ey" => ("h1ey", Ident);
		"-" => ("-", Ident);
		"." => (".", Ident);
		"_" => ("_", Ident);
		"-...--.-" => ("-...--.-", Ident);
		"n--ame" => ("n--ame", Ident);
		"name--" => ("name--", Ident);
		"-name-" => ("-name-", Ident);
		"--name" => ("--", DoubleDash), ("name", Ident);
		"-----" => ("--", DoubleDash), ("--", DoubleDash), ("-", Ident);
		"_____" => ("_____", Ident);
		"_name_" => ("_name_", Ident);
		"my.abs.olutely-normal_name.123" => ("my.abs.olutely-normal_name.123", Ident);

		"fun" => ("fun", Keyword(Kw::Func));
		"var" => ("var", Keyword(Kw::Var));
		"const" => ("const", Keyword(Kw::Const));
		"data" => ("data", Keyword(Kw::Data));
		"loop" => ("loop", Keyword(Kw::Loop));
		"jump" => ("jump", Keyword(Kw::Jump));
		"jumpif" => ("jumpif", Keyword(Kw::JumpIf));

		"fun name" => ("fun", Keyword(Kw::Func)), ("name", Ident);
	}
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
		"# =>

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
	}
}
