use uxnsmal::{
	ast::{Definition, FuncArgs, NodeOp},
	lexer::{Lexer, Span, Spanned},
	parser::Parser,
	program::{
		AddrKind,
		Type::{self, *},
	},
	symbols::Name,
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

	let tokens = Lexer::parse(S).unwrap();
	let ast = Parser::parse(S, &tokens).unwrap();
	for idx in 0..ast.definitions.len() {
		let Definition::Function(def) = &ast.definitions[idx].0 else {
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
	"#;

	#[rustfmt::skip]
	let expect: &[(&str, &[Type], &[Type])] = &[
		("my-proc", &[], &[]),
		("proc", &[Byte, Short], &[]),
		("p", &[Byte, ShortPtr(Byte.into())], &[Byte]),
		("r", &[], &[BytePtr(ShortPtr(BytePtr(Short.into()).into()).into())]),
	];

	let tokens = Lexer::parse(S).unwrap();
	let ast = Parser::parse(S, &tokens).unwrap();
	for idx in 0..ast.definitions.len() {
		let Definition::Function(def) = &ast.definitions[idx].0 else {
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
			assert_eq!(inputs[typ_idx].0, expect[idx].1[typ_idx]);
		}
		for typ_idx in 0..outputs.len() {
			assert_eq!(outputs[typ_idx].0, expect[idx].2[typ_idx]);
		}
	}
}

#[test]
fn ast_ops() {
	use NodeOp as Op;
	use uxnsmal::program::{Intrinsic as I, IntrinsicMode as Im};

	fn s<T>(inner: T) -> Spanned<T> {
		Spanned(inner, Span::default())
	}
	fn n(s: &str) -> Name {
		Name::new(s)
	}
	fn sn(string: &str) -> Spanned<Name> {
		s(n(string))
	}

	const S: &str = r#"
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

			-> (a b c)->(hello hi)
			-> (
			wrap
			omg)
		}
	"#;

	#[rustfmt::skip]
	let expect: &[NodeOp] = &[
		Op::Byte(1), Op::Byte(0xff), Op::Byte(0b101),
		Op::Short(1), Op::Short(0xffff), Op::Short(0o77),
		Op::String("string!".into()),
		Op::String("escape \" ' \\ \0 ".into()),
		Op::Byte(b'a'), Op::Byte(b'b'),
		Op::Byte(b'\0'),
		Op::Byte(b'\x07'),
		Op::Byte(b'\x08'),
		Op::Byte(b'\t'),
		Op::Byte(b'\n'),
		Op::Byte(b'\x0B'),
		Op::Byte(b'\x0C'),
		Op::Byte(b'\r'),
		Op::Byte(b'\\'),
		Op::Byte(b'\''),
		Op::Byte(b'"'),
		Op::Padding(100),
		Op::Padding(255),
		Op::Padding(2),
		Op::Symbol(n("symbol")), Op::Symbol(n("hey.hello")),
		Op::PtrTo(n("ptr-to-me")),
		Op::PtrTo(n("ptr-to-this")),

		Op::Intrinsic(I::Add, Im::NONE),
		Op::Intrinsic(I::Sub, Im::NONE),
		Op::Intrinsic(I::Mul, Im::NONE),
		Op::Intrinsic(I::Div, Im::NONE),
		Op::Intrinsic(I::Inc, Im::NONE),
		Op::Intrinsic(I::Shift, Im::NONE),

		Op::Intrinsic(I::And, Im::NONE),
		Op::Intrinsic(I::Or, Im::NONE),
		Op::Intrinsic(I::Xor, Im::NONE),

		Op::Intrinsic(I::Eq, Im::NONE),
		Op::Intrinsic(I::Neq, Im::NONE),
		Op::Intrinsic(I::Gth, Im::NONE),
		Op::Intrinsic(I::Lth, Im::NONE),

		Op::Intrinsic(I::Pop, Im::NONE),
		Op::Intrinsic(I::Swap, Im::NONE),
		Op::Intrinsic(I::Nip, Im::NONE),
		Op::Intrinsic(I::Rot, Im::NONE),
		Op::Intrinsic(I::Dup, Im::NONE),
		Op::Intrinsic(I::Over, Im::NONE),

		Op::Intrinsic(I::Load(AddrKind::Unknown), Im::NONE),
		Op::Intrinsic(I::Store(AddrKind::Unknown), Im::NONE),

		Op::Intrinsic(I::Input, Im::NONE),
		Op::Intrinsic(I::Input2, Im::NONE),
		Op::Intrinsic(I::Output, Im::NONE),

		Op::Intrinsic(I::Add, Im::RETURN),
		Op::Intrinsic(I::Add, Im::KEEP),
		Op::Intrinsic(I::Add, Im::KEEP | Im::RETURN),
		Op::Intrinsic(I::Add, Im::KEEP | Im::RETURN),

		Op::Block { looping: false, label: sn("block"), body: Box::default() },
		Op::Block { looping: true, label: sn("break"), body: Box::default() },
		Op::Block { looping: false, label: sn("exit"), body: Box::new([
			s(Op::Byte(20)), s(Op::Byte(30)), s(Op::Symbol(n("hey"))),
			s(Op::Jump { label: sn("exit"), conditional: false }),
			s(Op::Jump { label: sn("exit"), conditional: true }),
		]) },
		Op::Bind(Box::new([sn("a"), sn("b"), sn("c")])),
		Op::Bind(Box::new([sn("hello"), sn("hi")])),
		Op::Bind(Box::new([sn("wrap"), sn("omg")])),
	];

	let tokens = Lexer::parse(S).unwrap();
	let ast = Parser::parse(S, &tokens).unwrap();
	for idx in 0..ast.definitions.len() {
		let Definition::Function(def) = &ast.definitions[idx].0 else {
			panic!(
				"not a function definition, while testing {:?}",
				&expect[idx]
			);
		};

		for op_idx in 0..def.body.len() {
			let op = &def.body[op_idx].0;
			assert_eq!(op, &expect[op_idx]);
		}
	}
}
