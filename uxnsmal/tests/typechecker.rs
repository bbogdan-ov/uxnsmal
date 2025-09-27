use uxnsmal::{
	ast::Typed,
	lexer::Span,
	program::{AddrKind, Intrinsic, IntrinsicMode},
	symbols::{FuncSignature, Type},
	typechecker::{StackMatch, Typechecker},
};

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
	let expects: &mut [(
		&mut [Type],
		&mut [Intrinsic],
		IntrinsicMode,
		Option<Intrinsic>,
		&[Type]
	)] = list! {
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

				checker.check_intrinsic(intr, &mut mode, span).unwrap();

				assert_eq!(mode | expect.2, mode, "at {expect:?} (mode = {mode:?})");
				if let Some(expect_intr) = expect.3 {
					assert_eq!(expect_intr, *intr);
				}

				expect_ws.extend(expect.4.iter().cloned());

				if !(*intr == Intrinsic::Pop && keep) {
					let res = checker
						.ws
						.compare(expect_ws.iter(), StackMatch::Exact, span);
					assert_eq!(res, Ok(()), "at {expect:?} (mode = {mode:?})");
				}

				*intr = init_intr;
			}
		}
	}
}
