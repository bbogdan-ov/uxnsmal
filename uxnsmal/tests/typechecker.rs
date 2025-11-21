use uxnsmal::{
	ast::{ConstDef, DataDef, Def, Expr, FuncArgs, FuncDef, VarDef},
	lexer::{Span, Spanned},
	program::{IntrMode, Intrinsic},
	symbols::{FuncSignature, Name, Type},
	typechecker::{Scope, StackMatch, Typechecker},
};

// I NEED MORE TESTS BUT I HATE WRITING THEM SOOO MUCH
// WHY THE HELL THIS IS SO BORING

// TODO: add error tests

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

	let proc = &FuncSignature::Proc {
		inputs: Box::new([Type::Byte, Type::Short, Type::BytePtr(Type::Short.into())]),
		outputs: Box::new([Type::ShortPtr(Type::Byte.into()), Type::FuncPtr(FuncV)]),
	};

	fn ptr(typ: Type) -> Type {
		Type::BytePtr(Box::new(typ))
	}
	fn ptr2(typ: Type) -> Type {
		Type::ShortPtr(Box::new(typ))
	}
	fn vecptr() -> Type {
		Type::FuncPtr(FuncV)
	}
	fn procptr(sig: &FuncSignature) -> Type {
		Type::FuncPtr(sig.clone())
	}

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

		Byte, ptr(Byte)   => Add, Sub, Mul, Div => ptr(Byte);
		Short, ptr2(Byte) => Add, Sub, Mul, Div => ptr2(Byte);
		Short, vecptr()   => Add, Sub, Mul, Div => vecptr();
		ptr(Byte), Byte   => Add, Sub, Mul, Div => ptr(Byte);
		ptr2(Byte), Short => Add, Sub, Mul, Div => ptr2(Byte);
		vecptr(), Short   => Add, Sub, Mul, Div => vecptr();

		ptr(Byte), ptr(Byte)   => Add, Sub, Mul, Div => ptr(Byte);
		ptr2(Byte), ptr2(Byte) => Add, Sub, Mul, Div => ptr2(Byte);
		vecptr(), vecptr()     => Add, Sub, Mul, Div => vecptr();

		Byte, ptr(ptr2(Byte))      => Add, Sub, Mul, Div => ptr(ptr2(Byte));
		Short, ptr2(procptr(proc)) => Add, Sub, Mul, Div => ptr2(procptr(proc));

		// Increment
		Byte          => Inc => Byte;
		Short         => Inc => Short;
		ptr(Short)    => Inc => ptr(Short);
		ptr2(Byte)    => Inc => ptr2(Byte);
		vecptr()      => Inc => vecptr();
		procptr(proc) => Inc => procptr(proc);

		// Bitwise ops
		Byte, Byte  => Shift => Byte;
		Short, Byte => Shift => Short;

		Byte, Byte   => And, Or, Xor => Byte;
		Short, Short => And, Or, Xor => Short;

		// Comparison
		Byte, Byte                      => Eq, Neq, Gth, Lth => Byte;
		Short, Short                    => Eq, Neq, Gth, Lth => Byte;
		ptr(Byte), ptr(Byte)            => Eq, Neq, Gth, Lth => Byte;
		ptr(vecptr()), ptr(Short)       => Eq, Neq, Gth, Lth => Byte;
		ptr2(Byte), ptr2(Short)         => Eq, Neq, Gth, Lth => Byte;
		ptr2(Byte), ptr2(procptr(proc)) => Eq, Neq, Gth, Lth => Byte;
		vecptr(), procptr(proc)         => Eq, Neq, Gth, Lth => Byte;

		// Stack manipulation
		Byte, ptr(Byte)      => Pop => Byte;
		Short, ptr2(Byte)    => Pop => Short;
		vecptr(), ptr2(Byte) => Pop => vecptr();
		ptr2(Byte), Short    => Pop => ptr2(Byte);

		Byte, Byte           => Swap => Byte, Byte;
		Byte, ptr(Byte)      => Swap => ptr(Byte), Byte;
		Short, Short         => Swap => Short, Short;
		ptr2(Byte), Short    => Swap => Short, ptr2(Byte);
		Short, vecptr()      => Swap => vecptr(), Short;
		ptr2(Byte), vecptr() => Swap => vecptr(), ptr2(Byte);

		Byte, Byte           => Nip => Byte;
		ptr(Short), Byte     => Nip => Byte;
		Short, Short         => Nip => Short;
		Short, ptr2(Byte)    => Nip => ptr2(Byte);
		vecptr(), Short      => Nip => Short;
		ptr2(Byte), vecptr() => Nip => vecptr();

		Byte, Byte, Byte            => Rot => Byte, Byte, Byte;
		ptr(Short), ptr(Byte), Byte => Rot => ptr(Byte), Byte, ptr(Short);
		Short, Short, Short         => Rot => Short, Short, Short;
		Short, ptr2(Byte), vecptr() => Rot => ptr2(Byte), vecptr(), Short;

		Byte          => Dup => Byte, Byte;
		ptr(Byte)     => Dup => ptr(Byte), ptr(Byte);
		Short         => Dup => Short, Short;
		ptr2(Short)   => Dup => ptr2(Short), ptr2(Short);
		vecptr()      => Dup => vecptr(), vecptr();
		procptr(proc) => Dup => procptr(proc), procptr(proc);

		Byte, Byte           => Over => Byte, Byte, Byte;
		ptr(Byte), Byte      => Over => ptr(Byte), Byte, ptr(Byte);
		Short, Short         => Over => Short, Short, Short;
		Short, ptr2(Byte)    => Over => Short, ptr2(Byte), Short;
		procptr(proc), Short => Over => procptr(proc), Short, procptr(proc);

		// Load/store
		ptr(Byte)       => Load => Byte;
		ptr(Short)      => Load => Short;
		ptr2(Byte)      => Load => Byte;
		ptr2(Short)     => Load => Short;
		ptr2(ptr(Byte)) => Load => ptr(Byte);
		ptr(vecptr())   => Load => vecptr();

		Byte, ptr(Byte)          => Store => ;
		Short, ptr(Short)        => Store => ;
		vecptr(), ptr(vecptr())  => Store => ;
		Byte, ptr2(Byte)         => Store => ;
		Short, ptr2(Short)       => Store => ;
		vecptr(), ptr2(vecptr()) => Store => ;

		// Input/output
		Byte, Byte            => Output => ;
		Short, Byte           => Output => ;
		ptr(Byte), Byte       => Output => ;
		ptr2(Byte), Byte      => Output => ;
		ptr2(Short), Byte     => Output => ;
		vecptr(), Byte        => Output => ;
		procptr(proc), Byte   => Output => ;
		ptr(ptr2(Byte)), Byte => Output => ;

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

				let res = checker.check_intrinsic(*intr, *m, span);
				assert!(
					res.is_ok(),
					"unexpected result at {expect:?} (mode = {m:?})"
				);

				expect_ws.extend(expect.2.iter().cloned());

				if !(*intr == Intrinsic::Pop && keep) {
					let res = checker
						.ws
						.consumer(span)
						.compare(&expect_ws, StackMatch::Exact);
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

	macro_rules! block {
		($name:expr, [ $($node:expr),*$(,)? ]) => {
			Expr::Block { looping: false, label: name($name), body: nodes![$($node, )*] }
		};
	}
	macro_rules! ifb {
		([ $($node:expr),*$(,)? ]) => {
			Expr::If {
				if_body: nodes![$($node, )*],
				else_body: None,
			}
		};
		([ $($if_node:expr),*$(,)? ], [ $($else_node:expr),*$(,)? ]) => {
			Expr::If {
				if_body: nodes![$($if_node, )*],
				else_body: Some(nodes![$($else_node, )*]),
			}
		};
	}
	macro_rules! whileb {
		([ $($cond_node:expr),*$(,)? ], [ $($node:expr),*$(,)? ]) => {
			Expr::While {
				condition: nodes![$($cond_node, )*],
				body: nodes![$($node, )*]
			}
		};
	}

	fn name(name: &str) -> Spanned<Name> {
		Spanned::new(Name::new(name), Default::default())
	}
	fn byte(b: u8) -> Expr {
		Expr::Byte(b)
	}
	fn short(s: u16) -> Expr {
		Expr::Short(s)
	}
	fn jump(n: &str) -> Expr {
		Expr::Jump {
			label: name(n),
			conditional: false,
		}
	}
	fn jumpif(n: &str) -> Expr {
		Expr::Jump {
			label: name(n),
			conditional: true,
		}
	}

	#[rustfmt::skip]
	let expects: &mut [(&[_], _, &[_])] = list! {
		// Labeled block
		Byte => block!("hey", []) => Byte;

		Byte, Short => block!("hey", [
			short(2), intr(Add),
			jump("hey"),
		]) => Byte, Short;
		Byte, Short => block!("hey", [
			intr(Dup), short(2), intr(Lth),
			jumpif("hey"),
			byte(1), byte(2), intr(Add), intr(Pop),
		]) => Byte, Short;

		Byte => block!("hey", [
			short(10),
			block!("a", [
				intr(Pop),
				jump("hey"), // expected stack ( byte ), because we jump out of "hey" block
				short(1),    // expected stack ( byte short )
			]),
			intr(Pop),
		]) => Byte;
		Byte => block!("hey", [
			short(10),
			block!("a", [
				intr(Pop),
				jump("hey"), // ( byte )
				short(1),
				byte(69), jumpif("a"), // ( byte short )
				intr(Inc),
			]), // ( byte short )
			intr(Pop),
		]) => Byte;

		Byte => block!("hey", [
			intr(Dup), intr(Dup), intr(Dup),
			intr(Pop), intr(Pop), intr(Pop),
			intr(Inc),
		]) => Byte;

		// If block
		Short, Byte => ifb! { [] } => Short;
		Short, Byte => ifb! { [], [] } => Short;

		Short, Byte => ifb! { [intr(Inc)] } => Short;
		Short, Byte => ifb! { [intr(Pop), short(69)] } => Short;
		Short, Byte => ifb! { [intr(Inc)], [short(2), intr(Mul)] } => Short;
		Byte => ifb! {
			[short(69), short(420)],
			[short(1), short(2)]
		} => Short, Short;
		Short, Short, Byte => ifb! {
			[intr(Pop), intr(Pop)],
			[intr(Mul), byte(10), intr(Output)]
		} =>;

		// While block
		Byte, Short => whileb! { [byte(1)], [] } => Byte, Short;
		Byte => whileb! {
			[intr(Dup), intr(Lth), byte(10)],
			[intr(Inc)]
		} => Byte;
	};

	for expect in expects {
		let mut checker = Typechecker::default();
		let span = Span::default();

		for typ in expect.0.iter() {
			checker.ws.push((typ.clone(), span));
		}

		let res = checker.check_expr(&mut expect.1, span, &mut Scope::new(), &mut vec![]);
		assert_eq!(res, Ok(()), "at {expect:?}");

		let res = checker
			.ws
			.consumer(span)
			.compare(expect.2, StackMatch::Exact);
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
	let expects: &mut [Def] = &mut [
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

	for expect in expects.iter_mut() {
		let mut checker = Typechecker::default();
		let span = Span::default();

		let res = checker.check_def(expect, span, Scope::top_level());
		assert_eq!(res, Ok(()), "at {expect:?}");
	}
}
