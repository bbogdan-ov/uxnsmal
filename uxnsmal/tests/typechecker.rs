use uxnsmal::{
	ast::{ConstDef, DataDef, Expr, FuncArgs, FuncDef, Stmt, Typed, VarDef},
	lexer::{Span, Spanned},
	program::{AddrKind, Intrinsic, IntrinsicMode},
	symbols::{FuncSignature, Name, Type},
	typechecker::{StackMatch, Typechecker},
};

macro_rules! nodes {
	($($node:expr),*$(,)?) => {
		Box::new([
			$(Spanned::new($node.into(), Default::default()), )*
		])
	};
}
macro_rules! args {
	(
		$($input:expr),*$(,)? =>
		$($output:expr),*$(,)?
	) => {
		FuncArgs::Proc {
			inputs: Box::new([
				$(Spanned::new($input.into(), Default::default()), )*
			]),
			outputs: Box::new([
				$(Spanned::new($output.into(), Default::default()), )*
			]),
		}
	};
}

fn s<T>(x: T) -> Spanned<T> {
	Spanned::new(x, Default::default())
}
fn intr(intr: Intrinsic) -> Expr {
	Expr::Intrinsic(intr, IntrinsicMode::NONE)
}

/// Tests intrinsic output types with all possible modes
#[test]
fn typecheck_intrinsics() {
	use FuncSignature::Vector as FuncV;
	use Intrinsic::*;
	use Type::*;
	use Typed::{Typed as Td, Untyped as Ud};

	let proc = FuncSignature::Proc {
		inputs: Box::new([Type::Byte, Type::Short, Type::BytePtr(Type::Short.into())]),
		outputs: Box::new([Type::ShortPtr(Type::Byte.into()), Type::FuncPtr(FuncV)]),
	};

	macro_rules! list {
		($(
			$($typ:expr),*$(,)? =>
			$($intr:expr),*$(,)? =>
			$mode:ident, $expected:expr =>
			$($output:expr),*$(,)?;
		)*) => {
			&mut [
				$((
					&mut [$($typ,)*],
					&mut [$($intr,)*],
					IntrinsicMode::NONE,
					$expected,
					&[$($output,)*],
				),)*
			]
		};
	}

	// inputs... => intrinsics... => expected mode, expected intrinsic => outputs...
	#[rustfmt::skip]
	let expects: &mut [(&mut [_], &mut [_], _, _, &[_])] = list! {
		// Arithmetic
		Byte, Byte,   => Add, Sub, Mul, Div => NONE,None  => Byte;
		Short, Short, => Add, Sub, Mul, Div => SHORT,None => Short;

		Byte, BytePtr(Byte.into())   => Add, Sub, Mul, Div => NONE,None  => BytePtr(Byte.into());
		Short, ShortPtr(Byte.into()) => Add, Sub, Mul, Div => SHORT,None => ShortPtr(Byte.into());
		Short, FuncPtr(FuncV)        => Add, Sub, Mul, Div => SHORT,None => FuncPtr(FuncV);
		BytePtr(Byte.into()), Byte   => Add, Sub, Mul, Div => NONE,None  => BytePtr(Byte.into());
		ShortPtr(Byte.into()), Short => Add, Sub, Mul, Div => SHORT,None => ShortPtr(Byte.into());
		FuncPtr(FuncV), Short        => Add, Sub, Mul, Div => SHORT,None => FuncPtr(FuncV);

		BytePtr(Byte.into()), BytePtr(Byte.into())   => Add, Sub, Mul, Div => NONE,None => BytePtr(Byte.into());
		ShortPtr(Byte.into()), ShortPtr(Byte.into()) => Add, Sub, Mul, Div => SHORT,None => ShortPtr(Byte.into());
		FuncPtr(FuncV), FuncPtr(FuncV)               => Add, Sub, Mul, Div => SHORT,None => FuncPtr(FuncV);

		Byte, BytePtr(ShortPtr(Byte.into()).into())   => Add, Sub, Mul, Div => NONE,None => BytePtr(ShortPtr(Byte.into()).into());
		Short, ShortPtr(FuncPtr(proc.clone()).into()) => Add, Sub, Mul, Div => SHORT,None => ShortPtr(FuncPtr(proc.clone()).into());

		// Increment
		Byte                  => Inc => NONE,None  => Byte;
		Short                 => Inc => SHORT,None => Short;
		BytePtr(Short.into()) => Inc => NONE,None  => BytePtr(Short.into());
		ShortPtr(Byte.into()) => Inc => SHORT,None => ShortPtr(Byte.into());
		FuncPtr(FuncV)        => Inc => SHORT,None => FuncPtr(FuncV);
		FuncPtr(proc.clone()) => Inc => SHORT,None => FuncPtr(proc.clone());

		// Bitwise ops
		Byte, Byte  => Shift => NONE,None  => Byte;
		Short, Byte => Shift => SHORT,None => Short;

		Byte, Byte   => And, Or, Xor => NONE,None  => Byte;
		Short, Short => And, Or, Xor => SHORT,None => Short;

		// Comparison
		Byte, Byte                                                    => Eq, Neq, Gth, Lth => NONE,None  => Byte;
		Short, Short                                                  => Eq, Neq, Gth, Lth => SHORT,None => Byte;
		BytePtr(Byte.into()), BytePtr(Byte.into())                    => Eq, Neq, Gth, Lth => NONE,None  => Byte;
		BytePtr(FuncPtr(FuncV).into()), BytePtr(Short.into())         => Eq, Neq, Gth, Lth => NONE,None  => Byte;
		ShortPtr(Byte.into()), ShortPtr(Short.into())                 => Eq, Neq, Gth, Lth => SHORT,None => Byte;
		ShortPtr(Byte.into()), ShortPtr(FuncPtr(proc.clone()).into()) => Eq, Neq, Gth, Lth => SHORT,None => Byte;
		FuncPtr(FuncV), FuncPtr(proc.clone())                         => Eq, Neq, Gth, Lth => SHORT,None => Byte;

		// Stack manipulation
		Byte, BytePtr(Byte.into())            => Pop => NONE,None  => Byte;
		Short, ShortPtr(Byte.into())          => Pop => SHORT,None => Short;
		FuncPtr(FuncV), ShortPtr(Byte.into()) => Pop => SHORT,None => FuncPtr(FuncV);
		ShortPtr(Byte.into()), Short          => Pop => SHORT,None => ShortPtr(Byte.into());

		Byte, Byte                            => Swap => NONE,None  => Byte, Byte;
		Byte, BytePtr(Byte.into())            => Swap => NONE,None  => BytePtr(Byte.into()), Byte;
		Short, Short                          => Swap => SHORT,None => Short, Short;
		ShortPtr(Byte.into()), Short          => Swap => SHORT,None => Short, ShortPtr(Byte.into());
		Short, FuncPtr(FuncV)                 => Swap => SHORT,None => FuncPtr(FuncV), Short;
		ShortPtr(Byte.into()), FuncPtr(FuncV) => Swap => SHORT,None => FuncPtr(FuncV), ShortPtr(Byte.into());

		Byte, Byte                            => Nip => NONE,None  => Byte;
		BytePtr(Short.into()), Byte           => Nip => NONE,None  => Byte;
		Short, Short                          => Nip => SHORT,None => Short;
		Short, ShortPtr(Byte.into())          => Nip => SHORT,None => ShortPtr(Byte.into());
		FuncPtr(FuncV), Short                 => Nip => SHORT,None => Short;
		ShortPtr(Byte.into()), FuncPtr(FuncV) => Nip => SHORT,None => FuncPtr(FuncV);

		Byte, Byte, Byte                                  => Rot => NONE,None  => Byte, Byte, Byte;
		BytePtr(Short.into()), BytePtr(Byte.into()), Byte => Rot => NONE,None  => BytePtr(Byte.into()), Byte, BytePtr(Short.into());
		Short, Short, Short                               => Rot => SHORT,None => Short, Short, Short;
		Short, ShortPtr(Byte.into()), FuncPtr(FuncV)      => Rot => SHORT,None => ShortPtr(Byte.into()), FuncPtr(FuncV), Short;

		Byte                     => Dup => NONE,None  => Byte, Byte;
		BytePtr(Byte.into())     => Dup => NONE,None  => BytePtr(Byte.into()), BytePtr(Byte.into());
		Short                    => Dup => SHORT,None => Short, Short;
		ShortPtr(Short.into())   => Dup => SHORT,None => ShortPtr(Short.into()), ShortPtr(Short.into());
		FuncPtr(FuncV)           => Dup => SHORT,None => FuncPtr(FuncV), FuncPtr(FuncV);
		FuncPtr(proc.clone())    => Dup => SHORT,None => FuncPtr(proc.clone()), FuncPtr(proc.clone());

		Byte, Byte                   => Over => NONE,None  => Byte, Byte, Byte;
		BytePtr(Byte.into()), Byte   => Over => NONE,None  => BytePtr(Byte.into()), Byte, BytePtr(Byte.into());
		Short, Short                 => Over => SHORT,None => Short, Short, Short;
		Short, ShortPtr(Byte.into()) => Over => SHORT,None => Short, ShortPtr(Byte.into()), Short;
		FuncPtr(proc.clone()), Short => Over => SHORT,None => FuncPtr(proc.clone()), Short, FuncPtr(proc.clone());

		// Load/store
		BytePtr(Byte.into())                  => Load(Ud) => NONE,Some(Load(Td(AddrKind::AbsByte)))   => Byte;
		BytePtr(Short.into())                 => Load(Ud) => SHORT,Some(Load(Td(AddrKind::AbsByte)))  => Short;
		ShortPtr(Byte.into())                 => Load(Ud) => NONE,Some(Load(Td(AddrKind::AbsShort)))  => Byte;
		ShortPtr(Short.into())                => Load(Ud) => SHORT,Some(Load(Td(AddrKind::AbsShort))) => Short;
		ShortPtr(BytePtr(Byte.into()).into()) => Load(Ud) => NONE,Some(Load(Td(AddrKind::AbsShort))) => BytePtr(Byte.into());
		BytePtr(FuncPtr(FuncV).into())        => Load(Ud) => SHORT,Some(Load(Td(AddrKind::AbsByte))) => FuncPtr(FuncV);

		Byte, BytePtr(Byte.into())                      => Store(Ud) => NONE,Some(Store(Td(AddrKind::AbsByte))) =>;
		Short, BytePtr(Short.into())                    => Store(Ud) => SHORT,Some(Store(Td(AddrKind::AbsByte))) =>;
		FuncPtr(FuncV), BytePtr(FuncPtr(FuncV).into())  => Store(Ud) => SHORT,Some(Store(Td(AddrKind::AbsByte))) =>;
		Byte, ShortPtr(Byte.into())                     => Store(Ud) => NONE,Some(Store(Td(AddrKind::AbsShort))) =>;
		Short, ShortPtr(Short.into())                   => Store(Ud) => SHORT,Some(Store(Td(AddrKind::AbsShort))) =>;
		FuncPtr(FuncV), ShortPtr(FuncPtr(FuncV).into()) => Store(Ud) => SHORT,Some(Store(Td(AddrKind::AbsShort))) =>;

		// Input/output
		Byte, Byte                   => Output => NONE,None =>;
		Short, Byte                  => Output => NONE,None =>;
		BytePtr(Byte.into()), Byte   => Output => NONE,None =>;
		ShortPtr(Byte.into()), Byte  => Output => NONE,None =>;
		ShortPtr(Short.into()), Byte => Output => NONE,None =>;
		FuncPtr(FuncV), Byte         => Output => NONE,None =>;
		FuncPtr(proc.clone()), Byte  => Output => NONE,None =>;
		BytePtr(ShortPtr(Byte.into()).into()), Byte => Output => NONE,None =>;

		Byte => Input  => NONE,None  => Byte;
		Byte => Input2 => SHORT,None => Short;
	};

	for expect in expects.iter_mut() {
		for intr in expect.1.iter_mut() {
			// TODO: add tests for 'return' mode too
			const MODES: &[IntrinsicMode] = &[IntrinsicMode::NONE, IntrinsicMode::KEEP];

			for m in MODES {
				let span = Span::default();
				let mut checker = Typechecker::default();
				let mut expect_ws = Vec::<Type>::default();
				let mut mode = *m;
				let keep = mode.contains(IntrinsicMode::KEEP);
				let init_intr = intr.clone();

				for typ in expect.0.iter() {
					if keep {
						expect_ws.push(typ.clone());
					}

					checker.ws.push((typ.clone(), span));
				}

				let res = checker.check_intrinsic(intr, &mut mode, span);
				assert_eq!(res, Ok(()), "at {expect:?} (mode = {mode:?})");

				assert_eq!(mode | expect.2, mode, "at {expect:?} (mode = {mode:?})");
				if let Some(expect_intr) = expect.3 {
					assert_eq!(expect_intr, *intr);
				}

				expect_ws.extend(expect.4.iter().cloned());

				if !(*intr == Intrinsic::Pop && keep) {
					let res = checker
						.ws
						.compare(expect_ws.iter(), StackMatch::Exact, false, span);
					assert_eq!(res, Ok(()), "at {expect:?} (mode = {mode:?})");
				}

				*intr = init_intr;
			}
		}
	}
}

#[test]
fn typecheck_blocks() {
	use Intrinsic::*;
	use Type::*;

	macro_rules! list {
		($(
			$($input:expr),*$(,)? =>
			$stmt:expr =>
			$($output:expr),*$(,)?;
		)*) => {
			&mut [$((
				&[$($input,)*],
				$stmt,
				&[$($output,)*],
			),)*]
		};
	}

	fn name(name: &str) -> Spanned<Name> {
		Spanned::new(Name::new(name), Default::default())
	}

	#[rustfmt::skip]
	let expects: &mut [(&[_], _, &[_])] = list! {
		// Labeled block
		Byte => Stmt::Block { looping: false, label: name("hey"), body: nodes![] } => Byte;
		Byte => Stmt::Block { looping: true, label: name("hey"), body: nodes![] } => Byte;

		Byte, Short => Stmt::Block {
			looping: false,
			label: name("hey"),
			body: nodes![
				Expr::Short(2), intr(Add),
				Stmt::Jump { label: name("hey"), conditional: false },
			]
		} => Byte, Short;
		Byte, Short => Stmt::Block {
			looping: true,
			label: name("hey"),
			body: nodes![
				intr(Dup), Expr::Short(2), intr(Lth),
				Stmt::Jump { label: name("hey"), conditional: true },
				Expr::Byte(1), Expr::Byte(2), intr(Add), intr(Pop),
			]
		} => Byte, Short;

		Byte => Stmt::Block {
			looping: true,
			label: name("hey"),
			body: nodes![
				intr(Dup), intr(Dup), intr(Dup),
				intr(Pop), intr(Pop), intr(Pop),
				intr(Inc),
			]
		} => Byte;

		// If block
		Short, Byte => Stmt::If { if_body: nodes![], else_body: None } => Short;
		Short, Byte => Stmt::If { if_body: nodes![], else_body: Some(nodes![]) } => Short;

		Short, Byte => Stmt::If {
			if_body: nodes![intr(Inc)],
			else_body: None
		} => Short;
		Short, Byte => Stmt::If {
			if_body: nodes![intr(Pop), Expr::Short(69)],
			else_body: None
		} => Short;
		Short, Byte => Stmt::If {
			if_body:        nodes![intr(Inc)],
			else_body: Some(nodes![Expr::Short(2), intr(Mul)])
		} => Short;
		Byte => Stmt::If {
			if_body:        nodes![Expr::Short(69), Expr::Short(420)],
			else_body: Some(nodes![Expr::Short(1), Expr::Short(2)])
		} => Short, Short;
		Short, Short, Byte => Stmt::If {
			if_body:        nodes![intr(Pop), intr(Pop)],
			else_body: Some(nodes![intr(Mul), Expr::Byte(10), intr(Output)])
		} =>;

		// While block
		Byte => Stmt::While {
			condition: nodes![intr(Dup), intr(Lth), Expr::Byte(10)],
			body: nodes![intr(Inc)]
		} => Byte;
		Byte, Short => Stmt::While {
			condition: nodes![Expr::Byte(1)],
			body: nodes![]
		} => Byte, Short;
	};

	for expect in expects.iter_mut() {
		let mut checker = Typechecker::default();
		let span = Span::default();

		for typ in expect.0.iter() {
			checker.ws.push((typ.clone(), span));
		}

		let res = checker.check_stmt(&mut expect.1, span);
		assert_eq!(res, Ok(()), "at {expect:?}");

		let res = checker.ws.compare(expect.2, StackMatch::Exact, false, span);
		assert_eq!(res, Ok(()), "at {expect:?}");
	}
}

#[test]
fn typecheck_definitions() {
	use FuncArgs::Vector as ArgsV;
	use Intrinsic::*;
	use Type::*;

	macro_rules! func {
		($args:expr, [$($node:expr),*$(,)?]) => {
			Stmt::FuncDef(FuncDef {
				name: Name::new("hey"),
				args: $args,
				body: nodes![$($node, )*],
			})
		};
	}
	macro_rules! cnst {
		($typ:expr, [$($node:expr),*$(,)?]) => {
			Stmt::ConstDef(ConstDef {
				name: Name::new("hey"),
				typ: $typ,
				body: nodes![$($node, )*],
			})
		};
	}
	macro_rules! data {
		([$($node:expr),*$(,)?]) => {
			Stmt::DataDef(DataDef {
				name: Name::new("hey"),
				body: nodes![$($node, )*],
			})
		};
	}

	#[rustfmt::skip]
	let expects: &mut [Stmt] = &mut [
		// Function
		func! { args![=>],                            [] },
		func! { args![=>],                            [Expr::Byte(10), intr(Inc), intr(Pop)] },
		func! { args![Byte =>],                       [intr(Inc), intr(Pop)] },
		func! { args![Byte => Byte],                  [Expr::Byte(2), intr(Mul)] },
		func! { args![Byte => Byte, Short],           [Expr::Byte(2), intr(Mul), Expr::Short(20)] },
		func! { args![Byte => Short],                 [intr(Pop), Expr::Short(69)] },
		func! { args![ShortPtr(Byte.into()) => Byte], [intr(Load(Typed::Untyped))] },

		func! { ArgsV, [] },
		func! { ArgsV, [Expr::Byte(10), intr(Inc), intr(Pop)] },
		func! { ArgsV, [Expr::Short(10), intr(Pop)] },

		// Variable
		Stmt::VarDef(VarDef { name: Name::new("hey"), typ: s(Byte) }),
		Stmt::VarDef(VarDef { name: Name::new("hey"), typ: s(Short) }),
		Stmt::VarDef(VarDef { name: Name::new("hey"), typ: s(BytePtr(Short.into())) }),
		Stmt::VarDef(VarDef { name: Name::new("hey"), typ: s(ShortPtr(Byte.into())) }),
		Stmt::VarDef(VarDef { name: Name::new("hey"), typ: s(FuncPtr(FuncSignature::Vector)) }),

		// Constant
		cnst! { s(Byte),  [Expr::Byte(10)] },
		cnst! { s(Short), [Expr::Short(10)] },

		// Data
		data! { [] },
		data! { [Expr::Byte(10)] },
		data! { [Expr::Short(420)] },
		data! { [Expr::String("hey".into())] },
		data! { [Expr::Padding(1024)] },
	];

	for expect in expects.iter_mut() {
		let mut checker = Typechecker::default();
		let span = Span::default();

		let res = checker.check_stmt(expect, span);
		assert_eq!(res, Ok(()), "at {expect:?}");
	}
}
