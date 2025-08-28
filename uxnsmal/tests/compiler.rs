use uxnsmal::{
	bytecode::Bytecode, compiler::Compiler, error, lexer::Lexer, parser::Parser,
	typechecker::Typechecker,
};

fn compile(src: &str) -> error::Result<Bytecode> {
	let tokens = Lexer::lex(src).unwrap();
	let ast = Parser::parse(src, &tokens).unwrap();
	let program = Typechecker::check(ast).unwrap();
	Compiler::compile(&program)
}

#[test]
fn compile_intrinsics() {
	use Byte as B;
	use uxnsmal::bytecode::Opcode::{self, *};

	macro_rules! s {
		($outer:expr, $inner:expr) => {
			// Compiler requires 'on-reset' vector function to be defined
			concat!($outer, " fun on-reset(->){ ", $inner, " }")
		};
	}

	// TODO: need to add more tests
	#[rustfmt::skip]
	let expects: &[(&str, &[Opcode])] = &[
		(s!("", "1 2 add pop"),             &[LIT,  B(1),       LIT, B(2),      ADD, POP,                BRK]),
		(s!("", "1* 2* add pop"),           &[LIT2, B(0),B(1), LIT2, B(0),B(2), ADD2, POP2,              BRK]),
		(s!("", "1 2 add-k pop pop pop"),   &[LIT,  B(1),       LIT, B(2),      ADDk, POP, POP, POP,     BRK]),
		(s!("", "1* 2* add-k pop pop pop"), &[LIT2, B(0),B(1), LIT2, B(0),B(2), ADD2k, POP2, POP2, POP2, BRK]),

		(s!("", "255* pop"),    &[LIT2, B(0),B(255), POP2,     BRK]),
		(s!("", "256* pop"),    &[LIT2, B(1),B(0), POP2,       BRK]),
		(s!("", "257* pop"),    &[LIT2, B(1),B(1), POP2,       BRK]),
		(s!("", "0xab pop"),    &[LIT,  B(0xab), POP,          BRK]),
		(s!("", "0xffff* pop"), &[LIT2, B(0xff),B(0xff), POP2, BRK]),
		(s!("", "0xabcd* pop"), &[LIT2, B(0xab),B(0xcd), POP2, BRK]),

		(s!("", "'a' 0x18 output"),  &[LIT,  B(0x61),   LIT, B(0x18), DEO,  BRK]),
		(s!("", "257* 0x18 output"), &[LIT2, B(1),B(1), LIT, B(0x18), DEO2, BRK]),

		(s!("", "69 input pop"),  &[LIT, B(69), DEI,  POP,  BRK]),
		(s!("", "69 input2 pop"), &[LIT, B(69), DEI2, POP2, BRK]),

		// TODO: add tests for return-stack ops when they will be implemented
		(s!("", "1 pop"),        &[LIT,  B(1), POP,              BRK]),
		(s!("", "1* pop"),       &[LIT2, B(0),B(1), POP2,        BRK]),
		(s!("", "1 pop-k pop"),  &[LIT,  B(1), POPk, POP,        BRK]),
		(s!("", "1* pop-k pop"), &[LIT2, B(0),B(1), POP2k, POP2, BRK]),

		(s!("var byte v", "v pop"),              &[LIT, B(0), LDZ, POP,       BRK]),
		(s!("var byte v", "&v pop"),             &[LIT, B(0), POP,            BRK]),
		(s!("var short v", "v pop"),             &[LIT, B(0), LDZ2, POP2,     BRK]),
		(s!("var short _ var byte a", "a pop"),  &[LIT, B(2), LDZ, POP,       BRK]),
		(s!("data a{0xab 0x66 0xcd}", "&a pop"), &[LIT2, B(1),B(5), POP2,     BRK, B(0xab), B(0x66), B(0xcd)]),
		(s!("data a{0xab 0x66 0xcd}", "a pop"),  &[LIT2, B(1),B(6), LDA, POP, BRK, B(0xab), B(0x66), B(0xcd)]),

		(s!("fun a(--){1 pop}", "a"),      &[JSI, B(0),B(1),        BRK, LIT, B(1), POP, JMP2r]),
		(s!("fun a(--){1 pop}", "&a pop"), &[LIT2, B(1),B(5), POP2, BRK, LIT, B(1), POP, JMP2r]),

		(s!("", "@exit { jump @exit 10 20 add pop }"), &[JMI, B(0),B(6), LIT, B(10), LIT, B(20), ADD, POP, BRK]),
		(s!("", "@exit { 2 3 eq jumpif @exit 10 pop }"), &[LIT, B(2), LIT, B(3), EQU, JCI, B(0),B(3), LIT, B(10), POP, BRK]),
	];

	for expect in expects {
		let bytecode = compile(expect.0).unwrap();
		assert_eq!(bytecode.opcodes, expect.1);
	}
}

#[test]
fn examples_compilation() {
	macro_rules! example {
		($file:expr) => {
			(
				$file,
				include_str!(concat!("../../examples/", $file)),
				include_str!(concat!("../../examples/", $file, ".txt")),
			)
		};
	}

	#[rustfmt::skip]
	let sources = [
		example!("mouse.smal"),
		example!("hello.smal"),
		example!("logo.smal"),
		example!("print.smal"),
		example!("sprite.smal"),
	];

	for (name, src, expect) in sources {
		let bytecode = compile(src).unwrap();
		let found = format!("{bytecode:?}");
		assert!(found == expect, "unexpected bytecode output for {name:?}");
	}
}
