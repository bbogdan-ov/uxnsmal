use uxnsmal::{
	lexer::Span,
	program::{Intrinsic, IntrinsicMode},
	symbols::{FuncSignature, Type},
	typechecker::{StackMatch, Typechecker},
};

/// Tests intrinsic output types with all possible modes
#[test]
fn typecheck_intrinsics() {
	use FuncSignature::Vector as FuncV;
	use Type::*;

	let proc = FuncSignature::Proc {
		inputs: Box::new([Type::Byte, Type::Short, Type::BytePtr(Type::Short.into())]),
		outputs: Box::new([Type::ShortPtr(Type::Byte.into()), Type::FuncPtr(FuncV)]),
	};

	macro_rules! list {
		($(
			$($typ:expr),*$(,)? =>
			$($intr:ident),*$(,)? =>
			$($mode:ident),*$(,)? =>
			$($output:expr),*$(,)?;
		)*) => {
			&mut [
				$((
					&mut [$($typ,)*],
					&[$(Intrinsic::$intr,)*],
					IntrinsicMode::NONE $( | IntrinsicMode::$mode)*,
					&[$($output,)*]
				),)*
			]
		};
	}

	// inputs... => intrinsics... => result mode... => outputs...
	#[rustfmt::skip]
	let expects: &mut [(&mut [Type], &[Intrinsic], IntrinsicMode, &[Type])] = list! {
		// Arithmetic
		Byte, Byte,   => Add, Sub, Mul, Div => NONE  => Byte;
		Short, Short, => Add, Sub, Mul, Div => SHORT => Short;

		Byte, BytePtr(Byte.into())   => Add, Sub, Mul, Div => NONE  => BytePtr(Byte.into());
		Short, ShortPtr(Byte.into()) => Add, Sub, Mul, Div => SHORT => ShortPtr(Byte.into());
		Short, FuncPtr(FuncV)        => Add, Sub, Mul, Div => SHORT => FuncPtr(FuncV);
		BytePtr(Byte.into()), Byte   => Add, Sub, Mul, Div => NONE  => BytePtr(Byte.into());
		ShortPtr(Byte.into()), Short => Add, Sub, Mul, Div => SHORT => ShortPtr(Byte.into());
		FuncPtr(FuncV), Short        => Add, Sub, Mul, Div => SHORT => FuncPtr(FuncV);

		BytePtr(Byte.into()), BytePtr(Byte.into())   => Add, Sub, Mul, Div => NONE => BytePtr(Byte.into());
		ShortPtr(Byte.into()), ShortPtr(Byte.into()) => Add, Sub, Mul, Div => SHORT => ShortPtr(Byte.into());
		FuncPtr(FuncV), FuncPtr(FuncV)               => Add, Sub, Mul, Div => SHORT => FuncPtr(FuncV);

		Byte, BytePtr(ShortPtr(Byte.into()).into())   => Add, Sub, Mul, Div => NONE => BytePtr(ShortPtr(Byte.into()).into());
		Short, ShortPtr(FuncPtr(proc.clone()).into()) => Add, Sub, Mul, Div => SHORT => ShortPtr(FuncPtr(proc.clone()).into());

		// Increment
		Byte                  => Inc => NONE  => Byte;
		Short                 => Inc => SHORT => Short;
		BytePtr(Short.into()) => Inc => NONE  => BytePtr(Short.into());
		ShortPtr(Byte.into()) => Inc => SHORT => ShortPtr(Byte.into());
		FuncPtr(FuncV)        => Inc => SHORT => FuncPtr(FuncV);
		FuncPtr(proc.clone()) => Inc => SHORT => FuncPtr(proc.clone());

		// Bitwise ops
		Byte, Byte  => Shift => NONE  => Byte;
		Short, Byte => Shift => SHORT => Short;

		Byte, Byte   => And, Or, Xor => NONE  => Byte;
		Short, Short => And, Or, Xor => SHORT => Short;

		// Comparison
		Byte, Byte                                                    => Eq, Neq, Gth, Lth => NONE  => Byte;
		Short, Short                                                  => Eq, Neq, Gth, Lth => SHORT => Byte;
		BytePtr(Byte.into()), BytePtr(Byte.into())                    => Eq, Neq, Gth, Lth => NONE  => Byte;
		BytePtr(FuncPtr(FuncV).into()), BytePtr(Short.into())         => Eq, Neq, Gth, Lth => NONE  => Byte;
		ShortPtr(Byte.into()), ShortPtr(Short.into())                 => Eq, Neq, Gth, Lth => SHORT => Byte;
		ShortPtr(Byte.into()), ShortPtr(FuncPtr(proc.clone()).into()) => Eq, Neq, Gth, Lth => SHORT => Byte;
		FuncPtr(FuncV), FuncPtr(proc.clone())                         => Eq, Neq, Gth, Lth => SHORT => Byte;

		// Input/output
		Byte, Byte                   => Output => NONE => ;
		Short, Byte                  => Output => NONE => ;
		BytePtr(Byte.into()), Byte   => Output => NONE => ;
		ShortPtr(Byte.into()), Byte  => Output => NONE => ;
		ShortPtr(Short.into()), Byte => Output => NONE => ;
		FuncPtr(FuncV), Byte         => Output => NONE => ;
		FuncPtr(proc.clone()), Byte  => Output => NONE => ;
		BytePtr(ShortPtr(Byte.into()).into()), Byte => Output => NONE => ;

		Byte => Input  => NONE  => Byte;
		Byte => Input2 => SHORT => Short;
	};

	for expect in expects.iter_mut() {
		for intr in expect.1.iter() {
			// TODO: add tests for 'return' mode too
			const MODES: &[IntrinsicMode] = &[IntrinsicMode::NONE, IntrinsicMode::KEEP];

			for m in MODES {
				let span = Span::default();
				let mut checker = Typechecker::default();
				let mut expect_ws = Vec::<Type>::default();
				let mut mode = *m;

				for typ in expect.0.iter() {
					if mode.contains(IntrinsicMode::KEEP) {
						expect_ws.push(typ.clone());
					}

					checker.ws.push((typ.clone(), span));
				}

				checker.check_intrinsic(*intr, &mut mode, span).unwrap();
				assert_eq!(mode, mode | expect.2, "at {expect:?} (mode = {mode:?})");

				expect_ws.extend(expect.3.iter().cloned());

				let res = checker
					.ws
					.compare(expect_ws.iter(), StackMatch::Exact, span);
				assert_eq!(res, Ok(()), "at {expect:?} (mode = {mode:?})");
			}
		}
	}
}
