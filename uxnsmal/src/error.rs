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
	BindedTypes(Vec<(Type, Option<Name>)>),
	Types(Vec<Type>),
	/// Inputs for manipulation intrinsics (pop, swap, etc)
	Manipulation(u16),
	/// Inputs for arithmetic intrinsics (add, sub, etc)
	Arithmetic,
	/// Inputs for logic intrinsics (and, or, xor)
	Logic,
	/// Inputs for comparison intrinsics (eq, gth, etc)
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
	/// Inputs for `store` intrinsic
	IntrStore,
	/// Input for `input` and `input2` intrinsics
	IntrInput,
	/// Input for `output intrinsic
	IntrOutput,
}

/// Stack error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackError {
	Invalid,
	TooFew { consumed_by: Vec<Span> },
	TooMany { caused_by: Vec<Span> },
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

	InvalidCharLiteral(Span),
	UnknownCharEscape(char, Span),

	UnclosedComment(Span),
	UnclosedString(Span),

	BadNumber(Radix, Span),
	ByteIsTooBig(Span),
	NumberIsTooBig(Span),

	// ==============================
	// Type errors
	// ==============================
	InvalidStack {
		expected: ExpectedStack,
		found: Vec<StackItem>,
		stack: StackError,
		span: Span,
	},

	UnmatchedInputsSizes {
		found: Vec<Spanned<u16>>,
		span: Span,
	},
	UnmatchedInputsTypes {
		found: Vec<StackItem>,
		span: Span,
	},

	InvalidStoreSymbol {
		found: SymbolKind,
		defined_at: Span,
		span: Span,
	},
	CastingUnderflowsStack(Span),
	UnhandledCastingData {
		found: Span,
		span: Span,
	},
	TooManyBindings(Span),
	UnmatchedNames {
		found: Vec<Spanned<Option<Name>>>,
		expected: Vec<Name>,
		span: Span,
	},

	IllegalVectorCall {
		defined_at: Span,
		span: Span,
	},
	IllegalTopLevelExpr(Span),
	IllegalSymbolUse {
		found: SymbolKind,
		defined_at: Span,
		span: Span,
	},
	IllegalPtrSymbol {
		found: SymbolKind,
		defined_at: Span,
		span: Span,
	},

	SymbolRedefinition {
		was_redefined: SymbolKind,
		defined_at: Span,
		span: Span,
	},
	LabelRedefinition {
		defined_at: Span,
		span: Span,
	},
	UnknownSymbol(Span),
	UnknownLabel(Span),
	InvalidSymbol {
		expected: SymbolKind,
		defined_at: Span,
		span: Span,
	},
}
impl std::error::Error for Error {}
impl Display for Error {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		macro_rules! w {
			($($msg:tt)+) => {
				write!(f, $($msg)+)
			};
		}

		match self {
			Self::NoLocalDefsYet(_) => w!("there is no local definitions yet..."),
			Self::NoCodeInDataYet(_) => {
				w!("there is no code evaluation inside data blocks yet...")
			}

			Self::UnknownToken(_) => w!("unknown token"),

			Self::Expected {
				expected, found, ..
			} => w!("expected {expected}, but found {found}"),
			Self::ExpectedNumber { found, .. } => w!("expected number, but found {found}"),
			Self::ExpectedCondition { found, .. } => {
				w!("expected condition, but found {found}")
			}
			Self::ExpectedType { found, .. } => w!("expected type, but found {found}"),
			Self::UnexpectedToken(_) => w!("unexpected token"),

			Self::InvalidCharLiteral(_) => w!("invalid character literal"),
			Self::UnknownCharEscape(ch, _) => w!("unknown character escape '\\{ch}'"),

			Self::UnclosedComment(_) => w!("unclosed comment"),
			Self::UnclosedString(_) => w!("unclosed string"),

			Self::BadNumber(radix, _) => w!("bad {radix} number literal"),
			Self::ByteIsTooBig(_) => w!("byte literal is too big, max is 255"),
			Self::NumberIsTooBig(_) => w!("number literal is too big, max is 65535"),

			Self::InvalidStack { .. } => w!("invalid stack signature"),

			Self::UnmatchedInputsSizes { .. } => w!("unmatched inputs size"),
			Self::UnmatchedInputsTypes { .. } => w!("unmatched inputs type"),

			Self::InvalidStoreSymbol { found, .. } => w!("you cannot store into a {found}"),
			Self::CastingUnderflowsStack(_) => w!("casting underflows the stack"),
			Self::UnhandledCastingData { .. } => w!("unhandled data while casting"),
			Self::TooManyBindings(_) => w!("too many bindings"),
			Self::UnmatchedNames { .. } => w!("unmatched items names"),

			Self::IllegalVectorCall { .. } => w!("illegal vector function call"),
			Self::IllegalTopLevelExpr(_) => w!("illegal top-level expression"),
			Self::IllegalSymbolUse { found, .. } => w!("you cannot use {found} here"),
			Self::IllegalPtrSymbol { found, .. } => {
				w!("you cannot take a pointer to a {found}")
			}

			Self::SymbolRedefinition { was_redefined, .. } => {
				w!("{was_redefined} redefinition")
			}
			Self::LabelRedefinition { .. } => w!("label redefinition"),
			Self::UnknownSymbol(_) => w!("unknown symbol"),
			Self::UnknownLabel(_) => w!("no such label in this scope"),
			Self::InvalidSymbol { expected, .. } => w!("not a {expected}"),
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
			| Self::BadNumber(_, span)
			| Self::ByteIsTooBig(span)
			| Self::NumberIsTooBig(span)
			| Self::InvalidStack { span, .. }
			| Self::IllegalVectorCall { span, .. }
			| Self::IllegalTopLevelExpr(span)
			| Self::SymbolRedefinition { span, .. }
			| Self::LabelRedefinition { span, .. }
			| Self::UnknownSymbol(span)
			| Self::UnknownLabel(span)
			| Self::UnmatchedInputsSizes { span, .. }
			| Self::UnmatchedInputsTypes { span, .. }
			| Self::InvalidStoreSymbol { span, .. }
			| Self::CastingUnderflowsStack(span)
			| Self::UnhandledCastingData { span, .. }
			| Self::TooManyBindings(span)
			| Self::UnmatchedNames { span, .. }
			| Self::InvalidSymbol { span, .. }
			| Self::IllegalSymbolUse { span, .. }
			| Self::IllegalPtrSymbol { span, .. } => Some(*span),
		}
	}

	pub fn hints<'a>(&'a self) -> Vec<Hint<'a>> {
		match self {
			Self::InvalidStack { found, stack, .. } => match stack {
				StackError::Invalid => found
					.iter()
					.map(|t| HintKind::TypeIs(&t.typ).hint(t.pushed_at))
					.collect(),
				StackError::TooMany { caused_by } => caused_by
					.iter()
					.map(|s| HintKind::CausedByThis.hint(*s))
					.collect(),
				StackError::TooFew { consumed_by } => consumed_by
					.iter()
					.map(|s| HintKind::ConsumedHere.hint(*s))
					.collect(),
			},

			Self::UnmatchedInputsSizes { found, .. } => found
				.iter()
				.map(|t| HintKind::SizeIs(t.x).hint(t.span))
				.collect(),
			Self::UnmatchedInputsTypes { found, .. } => found
				.iter()
				.map(|t| HintKind::TypeIs(&t.typ).hint(t.pushed_at))
				.collect(),

			Error::IllegalVectorCall { defined_at, .. }
			| Error::SymbolRedefinition { defined_at, .. }
			| Error::LabelRedefinition { defined_at, .. }
			| Error::InvalidStoreSymbol { defined_at, .. }
			| Error::InvalidSymbol { defined_at, .. }
			| Error::IllegalSymbolUse { defined_at, .. } => {
				vec![HintKind::DefinedHere.hint(*defined_at)]
			}

			Error::UnmatchedNames { found, .. } => found
				.iter()
				.map(|n| HintKind::NameIs(&n.x).hint(n.span))
				.collect(),

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
		}
	}
}

/// Error hint
#[derive(Debug, Clone)]
pub struct Hint<'a> {
	pub kind: HintKind<'a>,
	pub span: Span,
}
