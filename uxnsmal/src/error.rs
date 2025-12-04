use std::fmt::Display;

use crate::{
	lexer::{Radix, Span, Spanned, TokenKind},
	symbols::{Name, SymbolKind, Type},
	typechecker::StackItem,
};

pub type Result<T> = std::result::Result<T, Error>;

/// Expected stack
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedStack {
	Types(Vec<Type>),
	/// Inputs for manipulation intrinsics (`pop`, `swap`, etc)
	Manipulation(u16),
	/// Inputs for arithmetic intrinsics (`add`, `sub`, etc)
	Arithmetic,
	/// Inputs for logic intrinsics (`and`, `or`, `xor`)
	Logic,
	/// Inputs for comparison intrinsics (`eq`, `gth`, etc)
	Comparison,
	/// A single byte input
	Condition,

	/// Input for "store" operator
	Store(Type),
	/// Input for `inc` intrinsic
	IntrInc,
	/// Inputs for `shift` intrinsic
	IntrShift,
	/// Inputs for `load` intrinsic
	IntrLoad,
	// Inputs for `store` intrinsic
	/// `store` got empty stack
	IntrStoreEmpty,
	/// `store` unmatched pointer and a value was found
	IntrStore(Type),
	/// Input for `input` and `input2` intrinsics
	IntrInput,
	/// Input for `output intrinsic
	IntrOutput,
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
			ExpectedStack::Store(typ) => write!(f, "( {typ} )")?,
			ExpectedStack::IntrInc => write!(f, "( <any> )")?,
			ExpectedStack::IntrShift => write!(f, "( <any> byte )")?,
			ExpectedStack::IntrLoad => write!(f, "( <any pointer> )")?,
			ExpectedStack::IntrStoreEmpty => write!(f, "( <any> <any pointer> )")?,
			ExpectedStack::IntrStore(ptr) => match ptr {
				Type::BytePtr(t) | Type::ShortPtr(t) => write!(f, "( {t} {ptr} )")?,
				// NOTE: this arm should never execute, but handle it anyway
				_ => write!(f, "( <any> {ptr} )")?,
			},
			ExpectedStack::IntrInput => write!(f, "( byte )")?,
			ExpectedStack::IntrOutput => write!(f, "( <any> byte )")?,
		}
		Ok(())
	}
}

/// Found stack
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

// TODO: refactor `ExpectedNames` and `FoundNames` into a single structure

/// Expected names
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

/// Stack error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackError {
	Invalid,
	TooFew { consumed_by: Vec<Span> },
	TooMany { caused_by: Vec<Span> },
}

/// Symbol error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolError {
	Redefinition { redefined: SymbolKind },
	LabelRedefinition,
	IllegalUse { found: SymbolKind },
	IllegalPtr { found: SymbolKind },
	IllegalStore { found: SymbolKind },
	IllegalVectorCall,
	Expected { expected: SymbolKind },
}

/// Error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
	// ==============================
	// Temporary errors because UXNSMAL is still WIP
	// ==============================
	NoLocalDefsYet(Span),
	NoCodeInDataYet(Span),

	// ==============================
	// Syntax errors
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
	// Type errors
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
	InvalidNames {
		error: StackError,
		expected: ExpectedNames,
		found: FoundStack,
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

	CastingUnderflowsStack(Span),
	UnhandledCastingData {
		found: Span,
		span: Span,
	},
	TooManyBindings(Span),

	IllegalTopLevelExpr(Span),
	UnknownSymbol(Span),
	UnknownLabel(Span),
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
			Self::NoLocalDefsYet(_)  => w!("there is no local definitions yet..."),
			Self::NoCodeInDataYet(_) => w!("there is no code evaluation inside data blocks yet..."),

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
				StackError::Invalid { .. } => w!("invalid stack signature"),
				StackError::TooMany { .. } => w!("too many items on the stack"),
				StackError::TooFew { .. }  => w!("not enough items on the stack"),
			},
			Self::InvalidSymbol { error,.. } => match error {
				SymbolError::Redefinition { redefined } => w!("{redefined} with this name already defined"),
				SymbolError::LabelRedefinition          => w!("label with this name already defined in this scope"),
				SymbolError::IllegalUse { found }       => w!("you cannot use {} here", found.plural()),
				SymbolError::IllegalPtr { found }       => w!("you cannot take a pointer to a {found}"),
				SymbolError::IllegalStore { found, .. } => w!("you cannot store into a {found}"),
				SymbolError::IllegalVectorCall          => w!("you cannot call vector functions"),
				SymbolError::Expected { expected }      => w!("not a {expected}"),
			}
			Self::InvalidNames { error, .. }       => match error {
				StackError::Invalid        => w!("unmatched items names"),
				StackError::TooMany  { ..} => w!("too many names on the stack"),
				StackError::TooFew { ..}   => w!("not enough names on the stack"),
			},

			Self::UnmatchedInputsSizes { .. } => w!("unmatched inputs size"),
			Self::UnmatchedInputsTypes { .. } => w!("unmatched inputs type"),

			Self::CastingUnderflowsStack(_)   => w!("casting underflows the stack"),
			Self::UnhandledCastingData { .. } => w!("unhandled data while casting"),
			Self::TooManyBindings(_)          => w!("too many bindings"),

			Self::IllegalTopLevelExpr(_) => w!("you cannot use expressions outside definitions"),
			Self::UnknownSymbol(_)       => w!("unknown symbol"),
			Self::UnknownLabel(_)        => w!("no such label in this scope"),
		}
	}
}
impl Error {
	pub fn span(&self) -> Option<Span> {
		// Uuh i mean, at least it is ✨typesafe✨
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
			| Self::CastingUnderflowsStack(span)
			| Self::UnhandledCastingData { span, .. }
			| Self::TooManyBindings(span)
			| Self::InvalidNames { span, .. } => Some(*span),
		}
	}

	pub fn hints<'a>(&'a self) -> Vec<Hint<'a>> {
		fn caused_by_hints(spans: &[Span]) -> Vec<Hint> {
			spans
				.iter()
				.map(|s| HintKind::CausedByThis.hint(*s))
				.collect()
		}
		fn consumed_here_hints(spans: &[Span]) -> Vec<Hint> {
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
				StackError::Invalid => {
					let mut hints: Vec<Hint> = found
						.0
						.iter()
						.map(|t| HintKind::NameIs(&t.name).hint(t.pushed_at))
						.collect();
					let renamed_here: Vec<Hint> = found
						.0
						.iter()
						.filter_map(|t| t.renamed_at)
						.map(|span| HintKind::RenamedHere.hint(span))
						.collect();
					hints.extend(renamed_here);
					hints
				}
				StackError::TooMany { caused_by } => caused_by_hints(caused_by),
				StackError::TooFew { consumed_by } => consumed_here_hints(consumed_by),
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

			Error::InvalidSymbol { defined_at, .. } => {
				vec![HintKind::DefinedHere.hint(*defined_at)]
			}

			_ => vec![],
		}
	}
}

/// Error hint kind
#[derive(Debug, Clone)]
pub enum HintKind<'a> {
	DefinedHere,
	ConsumedHere,
	CausedByThis,
	SizeIs(u16),
	TypeIs(&'a Type),
	NameIs(&'a Option<Name>),
	RenamedHere,
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
			Self::RenamedHere => write!(f, "renamed here"),
		}
	}
}

/// Error hint
#[derive(Debug, Clone)]
pub struct Hint<'a> {
	pub kind: HintKind<'a>,
	pub span: Span,
}
