use uxnsmal::{
	ast::{ConstDef, DataDef, Def, Expr, FuncArgs, FuncDef, VarDef},
	lexer::{Span, Spanned},
	program::{IntrMode, Intrinsic},
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
	Expr::Intrinsic(intr, IntrMode::NONE)
}

/// Tests intrinsic output types with all possible modes
#[test]
fn typecheck_intrinsics() {
	use FuncSignature::Vector as FuncV;
	use Intrinsic::*;
	use Type::*;

	let proc = FuncSignature::Proc {
		inputs: Box::new([Type::Byte, Type::Short, Type::BytePtr(Type::Short.into())]),
		outputs: Box::new([Type::ShortPtr(Type::Byte.into()), Type::FuncPtr(FuncV)]),
	};

	macro_rules! list {
		($(
			$($typ:expr),*$(,)? =>
			$($intr:expr),*$(,)? =>
			$($output:expr),*$(,)?;
		)*) => {
			&[
				$((
					&[$($typ,)*],
					&[$($intr,)*],
					&[$($output,)*],
				),)*
			]
		};
	}

	// inputs... => intrinsics... => outputs...
	#[rustfmt::skip]
	let expects: &[(&[_], &[_], &[_])] = list! {
		// Arithmetic
		Byte, Byte,   => Add, Sub, Mul, Div => Byte;
		Short, Short, => Add, Sub, Mul, Div => Short;

		Byte, BytePtr(Byte.into())   => Add, Sub, Mul, Div => BytePtr(Byte.into());
		Short, ShortPtr(Byte.into()) => Add, Sub, Mul, Div => ShortPtr(Byte.into());
		Short, FuncPtr(FuncV)        => Add, Sub, Mul, Div => FuncPtr(FuncV);
		BytePtr(Byte.into()), Byte   => Add, Sub, Mul, Div => BytePtr(Byte.into());
		ShortPtr(Byte.into()), Short => Add, Sub, Mul, Div => ShortPtr(Byte.into());
		FuncPtr(FuncV), Short        => Add, Sub, Mul, Div => FuncPtr(FuncV);

		BytePtr(Byte.into()), BytePtr(Byte.into())   => Add, Sub, Mul, Div => BytePtr(Byte.into());
		ShortPtr(Byte.into()), ShortPtr(Byte.into()) => Add, Sub, Mul, Div => ShortPtr(Byte.into());
		FuncPtr(FuncV), FuncPtr(FuncV)               => Add, Sub, Mul, Div => FuncPtr(FuncV);

		Byte, BytePtr(ShortPtr(Byte.into()).into())   => Add, Sub, Mul, Div => BytePtr(ShortPtr(Byte.into()).into());
		Short, ShortPtr(FuncPtr(proc.clone()).into()) => Add, Sub, Mul, Div => ShortPtr(FuncPtr(proc.clone()).into());

		// Increment
		Byte                  => Inc => Byte;
		Short                 => Inc => Short;
		BytePtr(Short.into()) => Inc => BytePtr(Short.into());
		ShortPtr(Byte.into()) => Inc => ShortPtr(Byte.into());
		FuncPtr(FuncV)        => Inc => FuncPtr(FuncV);
		FuncPtr(proc.clone()) => Inc => FuncPtr(proc.clone());

		// Bitwise ops
		Byte, Byte  => Shift => Byte;
		Short, Byte => Shift => Short;

		Byte, Byte   => And, Or, Xor => Byte;
		Short, Short => And, Or, Xor => Short;

		// Comparison
		Byte, Byte                                                    => Eq, Neq, Gth, Lth => Byte;
		Short, Short                                                  => Eq, Neq, Gth, Lth => Byte;
		BytePtr(Byte.into()), BytePtr(Byte.into())                    => Eq, Neq, Gth, Lth => Byte;
		BytePtr(FuncPtr(FuncV).into()), BytePtr(Short.into())         => Eq, Neq, Gth, Lth => Byte;
		ShortPtr(Byte.into()), ShortPtr(Short.into())                 => Eq, Neq, Gth, Lth => Byte;
		ShortPtr(Byte.into()), ShortPtr(FuncPtr(proc.clone()).into()) => Eq, Neq, Gth, Lth => Byte;
		FuncPtr(FuncV), FuncPtr(proc.clone())                         => Eq, Neq, Gth, Lth => Byte;

		// Stack manipulation
		Byte, BytePtr(Byte.into())            => Pop => Byte;
		Short, ShortPtr(Byte.into())          => Pop => Short;
		FuncPtr(FuncV), ShortPtr(Byte.into()) => Pop => FuncPtr(FuncV);
		ShortPtr(Byte.into()), Short          => Pop => ShortPtr(Byte.into());

		Byte, Byte                            => Swap => Byte, Byte;
		Byte, BytePtr(Byte.into())            => Swap => BytePtr(Byte.into()), Byte;
		Short, Short                          => Swap => Short, Short;
		ShortPtr(Byte.into()), Short          => Swap => Short, ShortPtr(Byte.into());
		Short, FuncPtr(FuncV)                 => Swap => FuncPtr(FuncV), Short;
		ShortPtr(Byte.into()), FuncPtr(FuncV) => Swap => FuncPtr(FuncV), ShortPtr(Byte.into());

		Byte, Byte                            => Nip => Byte;
		BytePtr(Short.into()), Byte           => Nip => Byte;
		Short, Short                          => Nip => Short;
		Short, ShortPtr(Byte.into())          => Nip => ShortPtr(Byte.into());
		FuncPtr(FuncV), Short                 => Nip => Short;
		ShortPtr(Byte.into()), FuncPtr(FuncV) => Nip => FuncPtr(FuncV);

		Byte, Byte, Byte                                  => Rot => Byte, Byte, Byte;
		BytePtr(Short.into()), BytePtr(Byte.into()), Byte => Rot => BytePtr(Byte.into()), Byte, BytePtr(Short.into());
		Short, Short, Short                               => Rot => Short, Short, Short;
		Short, ShortPtr(Byte.into()), FuncPtr(FuncV)      => Rot => ShortPtr(Byte.into()), FuncPtr(FuncV), Short;

		Byte                     => Dup => Byte, Byte;
		BytePtr(Byte.into())     => Dup => BytePtr(Byte.into()), BytePtr(Byte.into());
		Short                    => Dup => Short, Short;
		ShortPtr(Short.into())   => Dup => ShortPtr(Short.into()), ShortPtr(Short.into());
		FuncPtr(FuncV)           => Dup => FuncPtr(FuncV), FuncPtr(FuncV);
		FuncPtr(proc.clone())    => Dup => FuncPtr(proc.clone()), FuncPtr(proc.clone());

		Byte, Byte                   => Over => Byte, Byte, Byte;
		BytePtr(Byte.into()), Byte   => Over => BytePtr(Byte.into()), Byte, BytePtr(Byte.into());
		Short, Short                 => Over => Short, Short, Short;
		Short, ShortPtr(Byte.into()) => Over => Short, ShortPtr(Byte.into()), Short;
		FuncPtr(proc.clone()), Short => Over => FuncPtr(proc.clone()), Short, FuncPtr(proc.clone());

		// Load/store
		BytePtr(Byte.into())                  => Load => Byte;
		BytePtr(Short.into())                 => Load => Short;
		ShortPtr(Byte.into())                 => Load => Byte;
		ShortPtr(Short.into())                => Load => Short;
		ShortPtr(BytePtr(Byte.into()).into()) => Load => BytePtr(Byte.into());
		BytePtr(FuncPtr(FuncV).into())        => Load => FuncPtr(FuncV);

		Byte, BytePtr(Byte.into())                      => Store => ;
		Short, BytePtr(Short.into())                    => Store => ;
		FuncPtr(FuncV), BytePtr(FuncPtr(FuncV).into())  => Store => ;
		Byte, ShortPtr(Byte.into())                     => Store => ;
		Short, ShortPtr(Short.into())                   => Store => ;
		FuncPtr(FuncV), ShortPtr(FuncPtr(FuncV).into()) => Store => ;

		// Input/output
		Byte, Byte                   => Output => ;
		Short, Byte                  => Output => ;
		BytePtr(Byte.into()), Byte   => Output => ;
		ShortPtr(Byte.into()), Byte  => Output => ;
		ShortPtr(Short.into()), Byte => Output => ;
		FuncPtr(FuncV), Byte         => Output => ;
		FuncPtr(proc.clone()), Byte  => Output => ;
		BytePtr(ShortPtr(Byte.into()).into()), Byte => Output => ;

		Byte => Input  => Byte;
		Byte => Input2 => Short;
	};

	for expect in expects {
		for intr in expect.1 {
			const MODES: &[IntrMode] = &[IntrMode::NONE, IntrMode::KEEP];

			for m in MODES {
				let span = Span::default();
				let mut checker = Typechecker::default();
				let mut expect_ws = Vec::<Type>::default();
				let keep = m.contains(IntrMode::KEEP);

				for typ in expect.0.iter() {
					if keep {
						expect_ws.push(typ.clone());
					}

					checker.ws.push((typ.clone(), span));
				}

				let mut ops = vec![];
				let res = checker.check_intrinsic(*intr, *m, span, &mut ops);
				assert_eq!(
					res,
					Ok(()),
					"unexpected result at {expect:?} (mode = {m:?})"
				);

				expect_ws.extend(expect.2.iter().cloned());

				if !(*intr == Intrinsic::Pop && keep) {
					let res = checker
						.ws
						.compare(expect_ws.iter(), StackMatch::Exact, false, span);
					assert_eq!(
						res,
						Ok(()),
						"unexpected result at {expect:?} (mode = {m:?})"
					);
				}
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
			$def:expr =>
			$($output:expr),*$(,)?;
		)*) => {
			&mut [$((
				&[$($input,)*],
				$def,
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
		Byte => Expr::Block { looping: false, label: name("hey"), body: nodes![] } => Byte;
		Byte => Expr::Block { looping: true, label: name("hey"), body: nodes![] } => Byte;

		Byte, Short => Expr::Block {
			looping: false,
			label: name("hey"),
			body: nodes![
				Expr::Short(2), intr(Add),
				Expr::Jump { label: name("hey"), conditional: false },
			]
		} => Byte, Short;
		Byte, Short => Expr::Block {
			looping: true,
			label: name("hey"),
			body: nodes![
				intr(Dup), Expr::Short(2), intr(Lth),
				Expr::Jump { label: name("hey"), conditional: true },
				Expr::Byte(1), Expr::Byte(2), intr(Add), intr(Pop),
			]
		} => Byte, Short;

		Byte => Expr::Block {
			looping: true,
			label: name("hey"),
			body: nodes![
				intr(Dup), intr(Dup), intr(Dup),
				intr(Pop), intr(Pop), intr(Pop),
				intr(Inc),
			]
		} => Byte;

		// If block
		Short, Byte => Expr::If { if_body: nodes![], else_body: None } => Short;
		Short, Byte => Expr::If { if_body: nodes![], else_body: Some(nodes![]) } => Short;

		Short, Byte => Expr::If {
			if_body: nodes![intr(Inc)],
			else_body: None
		} => Short;
		Short, Byte => Expr::If {
			if_body: nodes![intr(Pop), Expr::Short(69)],
			else_body: None
		} => Short;
		Short, Byte => Expr::If {
			if_body:        nodes![intr(Inc)],
			else_body: Some(nodes![Expr::Short(2), intr(Mul)])
		} => Short;
		Byte => Expr::If {
			if_body:        nodes![Expr::Short(69), Expr::Short(420)],
			else_body: Some(nodes![Expr::Short(1), Expr::Short(2)])
		} => Short, Short;
		Short, Short, Byte => Expr::If {
			if_body:        nodes![intr(Pop), intr(Pop)],
			else_body: Some(nodes![intr(Mul), Expr::Byte(10), intr(Output)])
		} =>;

		// While block
		Byte => Expr::While {
			condition: nodes![intr(Dup), intr(Lth), Expr::Byte(10)],
			body: nodes![intr(Inc)]
		} => Byte;
		Byte, Short => Expr::While {
			condition: nodes![Expr::Byte(1)],
			body: nodes![]
		} => Byte, Short;
	};

	for expect in expects {
		let mut checker = Typechecker::default();
		let span = Span::default();

		for typ in expect.0.iter() {
			checker.ws.push((typ.clone(), span));
		}

		let res = checker.check_expr(expect.1.clone(), span, &mut vec![]);
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
			Def::Func(FuncDef {
				name: Name::new("hey"),
				args: $args,
				body: nodes![$($node, )*],
			})
		};
	}
	macro_rules! cnst {
		($typ:expr, [$($node:expr),*$(,)?]) => {
			Def::Const(ConstDef {
				name: Name::new("hey"),
				typ: $typ,
				body: nodes![$($node, )*],
			})
		};
	}
	macro_rules! data {
		([$($node:expr),*$(,)?]) => {
			Def::Data(DataDef {
				name: Name::new("hey"),
				body: nodes![$($node, )*],
			})
		};
	}

	#[rustfmt::skip]
	let expects: &[Def] = &[
		// Function
		func! { args![=>],                            [] },
		func! { args![=>],                            [Expr::Byte(10), intr(Inc), intr(Pop)] },
		func! { args![Byte =>],                       [intr(Inc), intr(Pop)] },
		func! { args![Byte => Byte],                  [Expr::Byte(2), intr(Mul)] },
		func! { args![Byte => Byte, Short],           [Expr::Byte(2), intr(Mul), Expr::Short(20)] },
		func! { args![Byte => Short],                 [intr(Pop), Expr::Short(69)] },
		func! { args![ShortPtr(Byte.into()) => Byte], [intr(Load)] },

		func! { ArgsV, [] },
		func! { ArgsV, [Expr::Byte(10), intr(Inc), intr(Pop)] },
		func! { ArgsV, [Expr::Short(10), intr(Pop)] },

		// Variable
		Def::Var(VarDef { name: Name::new("hey"), typ: s(Byte) }),
		Def::Var(VarDef { name: Name::new("hey"), typ: s(Short) }),
		Def::Var(VarDef { name: Name::new("hey"), typ: s(BytePtr(Short.into())) }),
		Def::Var(VarDef { name: Name::new("hey"), typ: s(ShortPtr(Byte.into())) }),
		Def::Var(VarDef { name: Name::new("hey"), typ: s(FuncPtr(FuncSignature::Vector)) }),

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

	for expect in expects {
		let mut checker = Typechecker::default();
		let span = Span::default();

		let res = checker.check_def(expect.clone(), span);
		assert_eq!(res, Ok(()), "at {expect:?}");
	}
}
