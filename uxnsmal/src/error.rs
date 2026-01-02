use std::{fmt::Display, io};

use crate::{
	lexer::{Radix, Span, Spanned, TokenKind},
	symbols::{FuncSignature, Name, SymbolKind, Type},
	typechecker::StackItem,
};

pub type Result<T> = std::result::Result<T, Error>;

pub fn err_io(error: io::Error, span: Span) -> Error {
	Error::Io {
		error: error.kind(),
		span,
	}
}

/// Expected stack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedStack {
	Types(Vec<Type>),
	/// Inputs for manipulation intrinsics (`pop`, `swap`, etc).
	Manipulation(u16),
	/// Inputs for arithmetic intrinsics (`add`, `sub`, etc).
	Arithmetic,
	/// Inputs for logic intrinsics (`and`, `or`, `xor`).
	Logic,
	/// Inputs for comparison intrinsics (`eq`, `gth`, etc).
	Comparison,
	/// A single byte input.
	Condition,
	/// A single index input.
	Index(Type),

	/// Input for "store" operator.
	Store(Type),
	/// Input for `inc` intrinsic.
	IntrInc,
	/// Inputs for `shift` intrinsic.
	IntrShift,
	/// Inputs for `load` intrinsic.
	IntrLoad,
	/// `store` got empty stack.
	IntrStoreEmpty,
	/// `store` unmatched pointer and a value was found.
	IntrStore(Type),
	/// Input for `input` and `input2` intrinsics.
	IntrInput,
	/// Input for `output` intrinsic.
	IntrOutput,
	/// Input for `call` intrinsic.
	IntrCall,
}
impl Display for ExpectedStack {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			ExpectedStack::Types(types) => {
				write!(f, "( ")?;
				for typ in types {
					write!(f, "{typ} ")?;
				}
				write!(f, ")")?;
			}
			ExpectedStack::Manipulation(n) => {
				write!(f, "( ")?;
				for _ in 0..*n {
					write!(f, "<any> ")?;
				}
				write!(f, ")")?;
			}
			ExpectedStack::Arithmetic => write!(f, "( <any> <any> )")?,
			ExpectedStack::Logic => write!(f, "( byte byte ) or ( short short )")?,
			ExpectedStack::Comparison => write!(f, "2 items of the same type")?,
			ExpectedStack::Condition => write!(f, "( byte )")?,
			ExpectedStack::Index(t) => write!(f, "( {t} )")?,

			ExpectedStack::Store(typ) => write!(f, "( {typ} )")?,
			ExpectedStack::IntrInc => write!(f, "( <any> )")?,
			ExpectedStack::IntrShift => write!(f, "( <any> byte )")?,
			ExpectedStack::IntrLoad => write!(f, "( <any pointer> )")?,
			ExpectedStack::IntrStoreEmpty => write!(f, "( <any> <any pointer> )")?,
			ExpectedStack::IntrStore(ptr) => match ptr {
				Type::BytePtr(t) | Type::ShortPtr(t) => write!(f, "( {t} {ptr} )")?,
				// NOTE: this arm should never execute, but handle it anyway.
				_ => write!(f, "( <any> {ptr} )")?,
			},
			ExpectedStack::IntrInput => write!(f, "( byte )")?,
			ExpectedStack::IntrOutput => write!(f, "( <any> byte )")?,
			ExpectedStack::IntrCall => write!(f, "( [func inputs...] <func pointer> )")?,
		}
		Ok(())
	}
}

/// Found stack.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoundStack(pub Vec<StackItem>);
impl Display for FoundStack {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "( ")?;
		for item in self.0.iter() {
			write!(f, "{item} ")?;
		}
		write!(f, ")")
	}
}

/// Expected names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedNames(pub Vec<Option<Name>>);
impl Display for ExpectedNames {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "( ")?;
		for name in self.0.iter() {
			match name {
				Some(name) => write!(f, "{name} ")?,
				None => write!(f, "_ ")?,
			}
		}
		write!(f, ")")
	}
}

/// Found names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoundNames(pub Vec<Spanned<Option<Name>>>);
impl FoundNames {
	pub fn from_items(items: &[StackItem]) -> Self {
		let names = items
			.iter()
			.map(|i| Spanned::new(i.name.clone(), i.pushed_at))
			.collect();

		Self(names)
	}
}
impl Display for FoundNames {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "( ")?;
		for name in self.0.iter() {
			match &name.x {
				Some(name) => write!(f, "{name} ")?,
				None => write!(f, "_ ")?,
			}
		}
		write!(f, ")")
	}
}

/// Stack error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackError {
	Invalid,
	TooFew { consumed_by: Vec<Span> },
	TooMany { caused_by: Vec<Span> },
}

/// Cast error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CastError {
	Underflow,
	UnhandledBytes { size: u16, left: u16, at: Span },
}

/// Symbol error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolError {
	Redefinition { redefined: SymbolKind },
	LabelRedefinition,
	IllegalUse { found: SymbolKind },
	IllegalPtr { found: SymbolKind },
	IllegalStore { found: SymbolKind },
	IllegalVectorCall,
	Expected { expected: SymbolKind },

	SymbolsNotStructs { kind: SymbolKind },
	SymbolsNotArrays { kind: SymbolKind },
	NotStruct,
	NotArray,
	UnknownField,
	UnknownVariant,
	SpecifyEnumVariant,
	NoNestedVariants,
}

/// Type error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
	IllegalStruct { defined_at: Span },
	IllegalArray,
	UnknownArraySize,
}

/// Error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
	// ==============================
	// Temporary errors because UXNSMAL is still WIP.
	// ==============================
	NoLocalDefsYet(Span),
	NoCodeInDataYet(Span),
	NoMutltipleArraysAccessYet(Span),

	// ==============================
	// Syntax errors.
	// ==============================
	UnknownToken(Span),

	Expected {
		expected: TokenKind,
		found: TokenKind,
		span: Span,
	},
	ExpectedNumber {
		found: TokenKind,
		span: Span,
	},
	ExpectedCondition {
		found: TokenKind,
		span: Span,
	},
	ExpectedType {
		found: TokenKind,
		span: Span,
	},
	UnexpectedToken(Span),

	UnclosedComment(Span),
	UnclosedString(Span),

	InvalidCharLiteral(Span),
	UnknownCharEscape(char, Span),
	InvalidNumber(Radix, Span),
	ByteIsTooBig(Span),
	NumberIsTooBig(Span),

	// ==============================
	// Type errors.
	// ==============================
	InvalidStack {
		error: StackError,
		expected: ExpectedStack,
		found: FoundStack,
		span: Span,
	},
	InvalidSymbol {
		error: SymbolError,
		defined_at: Span,
		span: Span,
	},
	InvalidType {
		error: TypeError,
		span: Span,
	},
	InvalidNames {
		error: StackError,
		expected: ExpectedNames,
		found: FoundNames,
		span: Span,
	},
	InvalidCasting {
		error: CastError,
		expected: u16,
		found: u16,
		span: Span,
	},

	UnmatchedInputsSizes {
		found: Vec<Spanned<u16>>,
		span: Span,
	},
	UnmatchedInputsTypes {
		found: FoundStack,
		span: Span,
	},

	TooManyBindings(Span),

	IllegalVectorPtrCall {
		found: Span,
		span: Span,
	},
	IllegalTopLevelExpr(Span),
	IllegalPadding(Span),
	IllegalInclude(Span),
	InvalidEnumType(Span),

	UnknownSymbol(Span),
	UnknownLabel(Span),

	// ==============================
	// Other errors.
	// ==============================
	Io {
		error: io::ErrorKind,
		span: Span,
	},
}
impl std::error::Error for Error {}
impl Display for Error {
	#[rustfmt::skip]
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		macro_rules! w {
			($($msg:tt)+) => {
				write!(f, $($msg)+)
			};
		}

		match self {
			Self::NoLocalDefsYet(_)             => w!("there is no local definitions yet..."),
			Self::NoCodeInDataYet(_)            => w!("there is no code evaluation inside data blocks yet..."),
			Self::NoMutltipleArraysAccessYet(_) => w!("there is no mutltiple arrays access yet..."),

			Self::UnknownToken(_) => w!("unknown token"),

			Self::Expected { expected, found, .. } => w!("expected {expected}, but got {found}"),
			Self::ExpectedNumber { found, .. }     => w!("expected number, but got {found}"),
			Self::ExpectedCondition { found, .. }  => w!("expected condition, but got {found}"),
			Self::ExpectedType { found, .. }       => w!("expected type, but got {found}"),
			Self::UnexpectedToken(_)               => w!("unexpected token"),

			Self::UnclosedComment(_) => w!("unclosed multiline comment"),
			Self::UnclosedString(_)  => w!("unclosed string literal"),

			Self::InvalidCharLiteral(_)    => w!("invalid character literal"),
			Self::UnknownCharEscape(ch, _) => w!("unknown character escape '\\{ch}'"),
			Self::InvalidNumber(radix, _)  => w!("invalid {radix} number literal"),
			Self::ByteIsTooBig(_)          => w!("byte literal is too big, max is {}", u8::MAX),
			Self::NumberIsTooBig(_)        => w!("number literal is too big, max is {}", u16::MAX),

			Self::InvalidStack { error, .. } => match error {
				StackError::Invalid        => w!("invalid stack signature"),
				StackError::TooMany { .. } => w!("too many items on the stack"),
				StackError::TooFew { .. }  => w!("not enough items on the stack"),
			},
			Self::InvalidSymbol { error,.. } => match error {
				SymbolError::Redefinition { redefined }    => w!("{redefined} with this name already defined"),
				SymbolError::LabelRedefinition             => w!("label with this name already defined in this scope"),
				SymbolError::IllegalUse { found }          => w!("you cannot use {} here", found.plural()),
				SymbolError::IllegalPtr { found }          => w!("you cannot take a pointer to a {found}"),
				SymbolError::IllegalStore { found, .. }    => w!("you cannot store into a {found}"),
				SymbolError::IllegalVectorCall             => w!("you cannot call vector functions"),
				SymbolError::Expected { expected }         => w!("not a {expected}"),
				SymbolError::SymbolsNotArrays { kind, .. } => w!("{} cannot be arrays", kind.plural()),
				SymbolError::NotStruct                     => w!("this type is not a struct"),
				SymbolError::NotArray                      => w!("this type is not an array"),
				SymbolError::UnknownField                  => w!("unknown field"),
				SymbolError::UnknownVariant                => w!("unknown enum variant"),
				SymbolError::SpecifyEnumVariant            => w!("specify an enum variant"),
				SymbolError::NoNestedVariants              => w!("there is no nested enum variants"),
				SymbolError::SymbolsNotStructs { kind, .. } => match kind {
					SymbolKind::Struct => w!("you cannot access fields of struct types"),
					kind               => w!("{} are not structs", kind.plural())
				}
			}
			Self::InvalidType { error, .. } => match error {
				TypeError::IllegalStruct { .. }           => w!("you cannot use struct types here"),
				TypeError::IllegalArray                   => w!("you cannot use array types here"),
				TypeError::UnknownArraySize               => w!("you can only take pointers to unsized arrays"),
			},
			Self::InvalidNames { error, .. } => match error {
				StackError::Invalid         => w!("unmatched items names"),
				StackError::TooMany  { .. } => w!("too many names on the stack"),
				StackError::TooFew { .. }   => w!("not enough names on the stack"),
			},

			Self::UnmatchedInputsSizes { .. } => w!("unmatched inputs size"),
			Self::UnmatchedInputsTypes { .. } => w!("unmatched inputs type"),

			Self::InvalidCasting { error, .. } => match error {
				CastError::Underflow => w!("casting underflows the stack"),
				CastError::UnhandledBytes { left, .. } => match left {
					1 => w!("{left} unhandled byte while casting"),
					_ => w!("{left} unhandled bytes while casting"),
				}
			},

			Self::TooManyBindings(_) => w!("too many bindings"),

			Self::IllegalVectorPtrCall { .. } => w!("you cannot call pointers to vector functions"),
			Self::IllegalTopLevelExpr(_)      => w!("you cannot use expressions outside definitions"),
			Self::IllegalPadding(_)           => w!("paddings are only allowed inside data blocks"),
			Self::IllegalInclude(_)           => w!("includes are only allowed inside data blocks"),
			Self::InvalidEnumType(_)          => w!("enums can only inherit from `byte` or `short`"),

			Self::UnknownSymbol(_) => w!("unknown symbol"),
			Self::UnknownLabel(_)  => w!("no such label in this scope"),

			Self::Io { error, .. } => w!("unable to read this file: {error}"),
		}
	}
}
impl Error {
	pub fn span(&self) -> Option<Span> {
		// Uuh i mean, at least it is ✨typesafe✨.
		match self {
			Self::NoLocalDefsYet(span)
			| Self::NoCodeInDataYet(span)
			| Self::UnknownToken(span)
			| Self::Expected { span, .. }
			| Self::ExpectedNumber { span, .. }
			| Self::ExpectedCondition { span, .. }
			| Self::ExpectedType { span, .. }
			| Self::UnexpectedToken(span)
			| Self::InvalidCharLiteral(span)
			| Self::UnknownCharEscape(_, span)
			| Self::UnclosedComment(span)
			| Self::UnclosedString(span)
			| Self::InvalidNumber(_, span)
			| Self::ByteIsTooBig(span)
			| Self::NumberIsTooBig(span)
			| Self::InvalidStack { span, .. }
			| Self::InvalidSymbol { span, .. }
			| Self::IllegalTopLevelExpr(span)
			| Self::UnknownSymbol(span)
			| Self::UnknownLabel(span)
			| Self::UnmatchedInputsSizes { span, .. }
			| Self::UnmatchedInputsTypes { span, .. }
			| Self::InvalidCasting { span, .. }
			| Self::TooManyBindings(span)
			| Self::InvalidNames { span, .. }
			| Self::InvalidEnumType(span)
			| Self::InvalidType { span, .. }
			| Self::NoMutltipleArraysAccessYet(span)
			| Self::IllegalVectorPtrCall { span, .. }
			| Self::IllegalPadding(span)
			| Self::IllegalInclude(span)
			| Self::Io { span, .. } => Some(*span),
		}
	}

	pub fn hints<'a>(&'a self) -> Vec<Hint<'a>> {
		fn caused_by_hints(spans: &[Span]) -> Vec<Hint<'_>> {
			spans
				.iter()
				.map(|s| HintKind::CausedByThis.hint(*s))
				.collect()
		}
		fn consumed_here_hints(spans: &[Span]) -> Vec<Hint<'_>> {
			spans
				.iter()
				.map(|s| HintKind::ConsumedHere.hint(*s))
				.collect()
		}

		match self {
			Self::InvalidStack { found, error, .. } => match error {
				StackError::Invalid => found
					.0
					.iter()
					.map(|t| HintKind::TypeIs(&t.typ).hint(t.pushed_at))
					.collect(),
				StackError::TooMany { caused_by } => caused_by_hints(caused_by),
				StackError::TooFew { consumed_by } => consumed_here_hints(consumed_by),
			},
			Self::InvalidNames { found, error, .. } => match error {
				// TODO: also highlight where items were renamed.
				StackError::Invalid => found
					.0
					.iter()
					.map(|n| HintKind::NameIs(&n.x).hint(n.span))
					.collect(),
				StackError::TooMany { caused_by } => caused_by_hints(caused_by),
				StackError::TooFew { consumed_by } => consumed_here_hints(consumed_by),
			},
			Self::InvalidCasting { error, .. } => match error {
				CastError::UnhandledBytes { size, left, at } => {
					vec![HintKind::UnhandledBytes(*left, *size).hint(*at)]
				}
				CastError::Underflow => vec![],
			},

			Self::UnmatchedInputsSizes { found, .. } => found
				.iter()
				.map(|t| HintKind::SizeIs(t.x).hint(t.span))
				.collect(),
			Self::UnmatchedInputsTypes { found, .. } => found
				.0
				.iter()
				.map(|t| HintKind::TypeIs(&t.typ).hint(t.pushed_at))
				.collect(),

			Self::InvalidSymbol { defined_at, .. } => {
				vec![HintKind::DefinedHere.hint(*defined_at)]
			}
			Self::InvalidType {
				error: TypeError::IllegalStruct { defined_at },
				..
			} => {
				vec![HintKind::DefinedHere.hint(*defined_at)]
			}

			Self::IllegalVectorPtrCall { found, .. } => {
				vec![HintKind::TypeIs(&Type::FuncPtr(FuncSignature::Vector)).hint(*found)]
			}

			_ => vec![],
		}
	}
}

/// Error hint kind.
#[derive(Debug, Clone)]
pub enum HintKind<'a> {
	DefinedHere,
	ConsumedHere,
	CausedByThis,
	SizeIs(u16),
	TypeIs(&'a Type),
	NameIs(&'a Option<Name>),
	// <n> of <of> bytes are unhandled.
	UnhandledBytes(u16, u16),
}
impl<'a> HintKind<'a> {
	pub fn hint(self, span: Span) -> Hint<'a> {
		Hint { kind: self, span }
	}
}
impl Display for HintKind<'_> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::DefinedHere => write!(f, "defined here"),
			Self::ConsumedHere => write!(f, "consumed here"),
			Self::CausedByThis => write!(f, "caused by this"),
			Self::SizeIs(s) => write!(f, "size is {s}"),
			Self::TypeIs(t) => write!(f, "this is `{t}`"),
			Self::NameIs(Some(n)) => write!(f, "name is \"{n}\""),
			Self::NameIs(None) => write!(f, "no name"),
			Self::UnhandledBytes(n, of) => write!(f, "{n} of {of} bytes are unhandled"),
		}
	}
}

/// Error hint.
#[derive(Debug, Clone)]
pub struct Hint<'a> {
	pub kind: HintKind<'a>,
	pub span: Span,
}
