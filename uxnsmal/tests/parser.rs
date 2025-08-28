use uxnsmal::{
	ast::{Definition, Expr, FuncArgs, FuncDef, Name, Node},
	error::ErrorKind,
	lexer::{Lexer, Span, Spanned, TokenKind},
	parser::Parser,
	program::AddrKind,
	symbols::FuncSignature,
	typechecker::Type::{self, *},
};

#[test]
fn ast_vec_funcs() {
	const S: &str = r#"
		fun on-reset ( -> ) {}
		fun my-vector(->){}
		fun
		v(->){}
	"#;

	let expect = ["on-reset", "my-vector", "v"];

	let tokens = Lexer::lex(S).unwrap();
	let ast = Parser::parse(S, &tokens).unwrap();
	for idx in 0..ast.nodes.len() {
		let Node::Def(Definition::Func(def)) = &ast.nodes[idx].x else {
			panic!("not a function definition while testing {:?}", &expect[idx]);
		};
		assert!(matches!(def.args, FuncArgs::Vector));
		assert_eq!(def.name.as_ref(), expect[idx]);
	}
}

#[test]
fn ast_proc_funcs() {
	const S: &str = r#"
		fun my-proc ( -- ) {}
		fun proc ( byte short -- ) {}
		fun p(byte ptr2 byte --byte){  }
		fun r (--ptr ptr2 ptr short){  }

		fun p(byte --){}
		fun p(short --){}
		fun p(ptr byte --){}
		fun p(ptr2 byte --){}
		fun p(ptr ptr ptr short --){}
		fun p(ptr2 ptr ptr2 byte --){}

		fun p(funptr(byte -- byte) --){}
		fun p(ptr2 funptr(ptr byte --) --){}
		fun p(funptr(->) --){}
		fun p(ptr funptr(->) --){}
	"#;

	#[rustfmt::skip]
	let expect: &[(&str, &[Type], &[Type])] = &[
		("my-proc", &[], &[]),
		("proc", &[Byte, Short], &[]),
		("p", &[Byte, ShortPtr(Byte.into())], &[Byte]),
		("r", &[], &[BytePtr(ShortPtr(BytePtr(Short.into()).into()).into())]),

		("p", &[Byte], &[]),
		("p", &[Short], &[]),
		("p", &[BytePtr(Byte.into())], &[]),
		("p", &[ShortPtr(Byte.into())], &[]),
		("p", &[BytePtr(BytePtr(BytePtr(Short.into()).into()).into())], &[]),
		("p", &[ShortPtr(BytePtr(ShortPtr(Byte.into()).into()).into())], &[]),

		("p", &[FuncPtr(FuncSignature::Proc {
			inputs: [Byte].into(),
			outputs: [Byte].into(),
		})], &[]),
		("p", &[ShortPtr(FuncPtr(FuncSignature::Proc {
			inputs: [BytePtr(Byte.into())].into(),
			outputs: [].into(),
		}).into())], &[]),
		("p", &[FuncPtr(FuncSignature::Vector)], &[]),
		("p", &[BytePtr(FuncPtr(FuncSignature::Vector).into())], &[]),
	];

	let tokens = Lexer::lex(S).unwrap();
	let ast = Parser::parse(S, &tokens).unwrap();
	for idx in 0..ast.nodes.len() {
		let Node::Def(Definition::Func(def)) = &ast.nodes[idx].x else {
			panic!(
				"not a function definition, while testing {:?}",
				&expect[idx]
			);
		};
		let FuncArgs::Proc { inputs, outputs } = &def.args else {
			panic!("not a proc function, while testing {:?}", &expect[idx]);
		};

		assert_eq!(def.name.as_ref(), expect[idx].0);
		for typ_idx in 0..inputs.len() {
			assert_eq!(inputs[typ_idx].x, expect[idx].1[typ_idx]);
		}
		for typ_idx in 0..outputs.len() {
			assert_eq!(outputs[typ_idx].x, expect[idx].2[typ_idx]);
		}
	}
}

#[test]
fn ast_nodes() {
	use uxnsmal::program::{Intrinsic as I, IntrinsicMode as Im};

	fn s<T>(inner: T) -> Spanned<T> {
		Spanned::new(inner, Span::default())
	}
	fn n(s: &str) -> Name {
		Name::new(s)
	}
	fn sn(string: &str) -> Spanned<Name> {
		s(n(string))
	}
	fn e(expr: Expr) -> Node {
		Node::Expr(expr)
	}
	fn se(expr: Expr) -> Spanned<Node> {
		s(e(expr))
	}

	const S: &str = r#"
		add
		10 0xff

		fun on-reset ( -> ) { /( empty )/ }

		fun a ( -> ) {
			1 0xff 0b101
			1* 0xffff* 0o77*
			"string!" "escape \" ' \\ \0 "
			'a' 'b'

			// Escapes
			'\0' '\a' '\b' '\t' '\n' '\v' '\f' '\r' '\\' '\'' '\"'

			// Paddings should not be allowed inside functions
			$100 $0xff $0b10

			symbol hey.hello
			&ptr-to-me &  ptr-to-this

			// Intrinsics
			add
			sub
			mul
			div
			inc
			shift

			and
			or
			xor

			eq
			neq
			gth
			lth

			pop
			swap
			nip
			rot
			dup
			over

			load
			store

			input
			input2
			output

			add-r add-k add-rk add-kr

			// Blocks
			@block {}
			loop @ break {}
			@ exit {
				20 30 hey
				jump @exit
				jumpif@ exit
			}

			if { 2 pop }
			else { 3 pop }

			if { 100 200 }

			while 0 1 eq { 20 pop }

			-> (a b c)->(hello hi)
			-> (
			wrap
			omg)
			->()
		}
	"#;

	#[rustfmt::skip]
	let expect: &[Node ] = &[
		e(Expr::Intrinsic(I::Add, Im::NONE)),
		e(Expr::Byte(10)), e(Expr::Byte(255)),

		Node::Def(Definition::Func(FuncDef { name: n("on-reset"), args: FuncArgs::Vector, body: Box::default() })),

		Node::Def(Definition::Func(FuncDef { name: n("a"), args: FuncArgs::Vector, body: Box::new([
			se(Expr::Byte(1)), se(Expr::Byte(0xff)), se(Expr::Byte(0b101)),
			se(Expr::Short(1)), se(Expr::Short(0xffff)), se(Expr::Short(0o77)),
			se(Expr::String("string!".into())),
			se(Expr::String("escape \" ' \\ \0 ".into())),
			se(Expr::Byte(b'a')), se(Expr::Byte(b'b')),
			se(Expr::Byte(b'\0')),
			se(Expr::Byte(b'\x07')),
			se(Expr::Byte(b'\x08')),
			se(Expr::Byte(b'\t')),
			se(Expr::Byte(b'\n')),
			se(Expr::Byte(b'\x0B')),
			se(Expr::Byte(b'\x0C')),
			se(Expr::Byte(b'\r')),
			se(Expr::Byte(b'\\')),
			se(Expr::Byte(b'\'')),
			se(Expr::Byte(b'"')),
			se(Expr::Padding(100)),
			se(Expr::Padding(255)),
			se(Expr::Padding(2)),
			se(Expr::Symbol(n("symbol"))), se(Expr::Symbol(n("hey.hello"))),
			se(Expr::PtrTo(n("ptr-to-me"))),
			se(Expr::PtrTo(n("ptr-to-this"))),

			se(Expr::Intrinsic(I::Add, Im::NONE)),
			se(Expr::Intrinsic(I::Sub, Im::NONE)),
			se(Expr::Intrinsic(I::Mul, Im::NONE)),
			se(Expr::Intrinsic(I::Div, Im::NONE)),
			se(Expr::Intrinsic(I::Inc, Im::NONE)),
			se(Expr::Intrinsic(I::Shift, Im::NONE)),

			se(Expr::Intrinsic(I::And, Im::NONE)),
			se(Expr::Intrinsic(I::Or, Im::NONE)),
			se(Expr::Intrinsic(I::Xor, Im::NONE)),

			se(Expr::Intrinsic(I::Eq, Im::NONE)),
			se(Expr::Intrinsic(I::Neq, Im::NONE)),
			se(Expr::Intrinsic(I::Gth, Im::NONE)),
			se(Expr::Intrinsic(I::Lth, Im::NONE)),

			se(Expr::Intrinsic(I::Pop, Im::NONE)),
			se(Expr::Intrinsic(I::Swap, Im::NONE)),
			se(Expr::Intrinsic(I::Nip, Im::NONE)),
			se(Expr::Intrinsic(I::Rot, Im::NONE)),
			se(Expr::Intrinsic(I::Dup, Im::NONE)),
			se(Expr::Intrinsic(I::Over, Im::NONE)),

			se(Expr::Intrinsic(I::Load(AddrKind::Unknown), Im::NONE)),
			se(Expr::Intrinsic(I::Store(AddrKind::Unknown), Im::NONE)),

			se(Expr::Intrinsic(I::Input, Im::NONE)),
			se(Expr::Intrinsic(I::Input2, Im::NONE)),
			se(Expr::Intrinsic(I::Output, Im::NONE)),

			se(Expr::Intrinsic(I::Add, Im::RETURN)),
			se(Expr::Intrinsic(I::Add, Im::KEEP)),
			se(Expr::Intrinsic(I::Add, Im::KEEP | Im::RETURN)),
			se(Expr::Intrinsic(I::Add, Im::KEEP | Im::RETURN)),

			se(Expr::Block { looping: false, label: sn("block"), body: Box::default() }),
			se(Expr::Block { looping: true, label: sn("break"), body: Box::default() }),
			se(Expr::Block { looping: false, label: sn("exit"), body: Box::new([
				se(Expr::Byte(20)), se(Expr::Byte(30)), se(Expr::Symbol(n("hey"))),
				se(Expr::Jump { label: sn("exit"), conditional: false }),
				se(Expr::Jump { label: sn("exit"), conditional: true }),
			]) }),

			se(Expr::If {
				if_body: Box::new([se(Expr::Byte(2)), se(Expr::Intrinsic(I::Pop, Im::NONE))]),
				else_body: Some(Box::new([se(Expr::Byte(3)), se(Expr::Intrinsic(I::Pop, Im::NONE))])),
			}),
			se(Expr::If {
				if_body: Box::new([se(Expr::Byte(100)), se(Expr::Byte(200))]),
				else_body: None,
			}),

			se(Expr::While {
				condition: Box::new([
					se(Expr::Byte(0)), se(Expr::Byte(1)),
					se(Expr::Intrinsic(I::Eq, Im::NONE)),
				]),
				body: Box::new([
					se(Expr::Byte(20)),
					se(Expr::Intrinsic(I::Pop, Im::NONE)),
				]),
			}),

			se(Expr::Bind(Box::new([sn("a"), sn("b"), sn("c")]))),
			se(Expr::Bind(Box::new([sn("hello"), sn("hi")]))),
			se(Expr::Bind(Box::new([sn("wrap"), sn("omg")]))),
			se(Expr::Bind(Box::new([]))),
		]) })),
	];

	let tokens = Lexer::lex(S).unwrap();
	let ast = Parser::parse(S, &tokens).unwrap();
	for idx in 0..ast.nodes.len() {
		let node = &ast.nodes[idx].x;
		assert_eq!(node, &expect[idx]);
	}
}

#[test]
fn ast_error_parsing() {
	use ErrorKind as Ek;
	use TokenKind as Tk;

	#[rustfmt::skip]
	let expects: &[(&str, (&str, ErrorKind))] = &[
		("", ("", Ek::EmptyFile)),
		("      ", ("", Ek::EmptyFile)),

		("fun", ("", Ek::Expected { expected: Tk::Ident, found: Tk::Eof })),
		("fun hello {}", ("{", Ek::Expected { expected: Tk::OpenParen, found: Tk::OpenBrace })),
		("fun hello (byte byte) {}", (")", Ek::Expected { expected: Tk::DoubleDash, found: Tk::CloseParen })),
		("fun (byte) {}", ("(", Ek::Expected { expected: Tk::Ident, found: Tk::OpenParen })),
		("fun name (byte ->) {}", ("->", Ek::Expected { expected: Tk::DoubleDash, found: Tk::ArrowRight })),

		("var", ("", Ek::Expected { expected: Tk::Ident, found: Tk::Eof })),
		("var byte", ("", Ek::Expected { expected: Tk::Ident, found: Tk::Eof })),
		("var byte hello {}", ("{", Ek::UnexpectedToken)),

		("const", ("", Ek::Expected { expected: Tk::Ident, found: Tk::Eof })),
		("const byte", ("", Ek::Expected { expected: Tk::Ident, found: Tk::Eof })),
		("const byte hey", ("", Ek::Expected { expected: Tk::OpenBrace, found: Tk::Eof })),
		("const byte hey {", ("", Ek::Expected { expected: Tk::CloseBrace, found: Tk::Eof })),

		("data", ("", Ek::Expected { expected: Tk::Ident, found: Tk::Eof })),
		("data hey", ("", Ek::Expected { expected: Tk::OpenBrace, found: Tk::Eof })),
		("data hey {", ("", Ek::Expected { expected: Tk::CloseBrace, found: Tk::Eof })),

		("fun a(--) { @block { }", ("", Ek::Expected { expected: Tk::CloseBrace, found: Tk::Eof })),
		("fun a(--) { @ {} }", ("{", Ek::Expected { expected: Tk::Ident, found: Tk::OpenBrace })),
		("fun a(--) { ->(a b }", ("}", Ek::Expected { expected: Tk::CloseParen, found: Tk::CloseBrace })),
		("fun a(--) { -> a b }", ("a", Ek::Expected { expected: Tk::OpenParen, found: Tk::Ident })),

		("fun a(t --) {}", ("t", Ek::NoCustomTypesYet)),
		("fun a(ptr ptr2 t --) {}", ("t", Ek::NoCustomTypesYet)),

		(r#"data a { "\o" }"#, (r#""\o""#, Ek::UnknownCharEscape('o'))),
		("data a { 256 }", ("256", Ek::ByteIsTooLarge)),
		("data a { 0x1ffff }", ("0x1ffff", Ek::NumberIsTooLarge)),
		("data a { '' }", ("''", Ek::InvalidCharLiteral)),
		("data a { 'ab' }", ("'ab'", Ek::InvalidCharLiteral)),
		("data a { $hey }", ("hey", Ek::ExpectedNumber { found: Tk::Ident })),
		("data a { $ }", ("}", Ek::ExpectedNumber { found: Tk::CloseBrace })),

		("while", ("", Ek::ExpectedCondition { found: TokenKind::Eof })),
		("while 1 0 eq", ("", Ek::UnexpectedToken )),
		("while {}", ("{", Ek::ExpectedCondition { found: TokenKind::OpenBrace })),
	];

	for expect in expects {
		let result = Lexer::lex(expect.0).and_then(|t| Parser::parse(expect.0, &t));
		match result {
			Ok(_) => panic!("found `Ok`, expected `Err()` in {:?}", expect.0),
			Err(e) => {
				let span = e.span.unwrap_or_default();
				let slice = &expect.0[span.into_range()];
				assert_eq!((slice, e.kind), expect.1)
			}
		}
	}
}
