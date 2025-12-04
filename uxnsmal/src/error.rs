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
#[derive(thiserror::Error, Debug, Clone, PartialEq, Eq)]
pub enum Error {
	// ==============================
	// Temporary errors because UXNSMAL is still WIP
	// ==============================
	#[error("there is no local definitions yet...")]
	NoLocalDefsYet(Span),
	#[error("there is no code evaluation inside data blocks yet...")]
	NoCodeInDataYet(Span),

	// ==============================
	// Syntax errors
	// ==============================
	#[error("unknown token")]
	UnknownToken(Span),

	#[error("expected {expected}, but found {found}")]
	Expected {
		expected: TokenKind,
		found: TokenKind,
		span: Span,
	},
	#[error("expected number, but found {found}")]
	ExpectedNumber { found: TokenKind, span: Span },
	#[error("expected condition, but found {found}")]
	ExpectedCondition { found: TokenKind, span: Span },
	#[error("expected type, but found {found}")]
	ExpectedType { found: TokenKind, span: Span },
	#[error("unexpected token")]
	UnexpectedToken(Span),

	#[error("invalid character literal")]
	InvalidCharLiteral(Span),
	#[error("unknown character escape '\\{0}'")]
	UnknownCharEscape(char, Span),

	#[error("unclosed comment")]
	UnclosedComment(Span),
	#[error("unclosed string")]
	UnclosedString(Span),

	#[error("bad {0} number literal")]
	BadNumber(Radix, Span),
	#[error("byte literal is too big, max is 255")]
	ByteIsTooBig(Span),
	#[error("number literal is too big, max is 65535")]
	NumberIsTooBig(Span),

	// ==============================
	// Type errors
	// ==============================
	#[error("invalid stack signature")]
	InvalidStack {
		expected: ExpectedStack,
		found: Vec<StackItem>,
		stack: StackError,
		span: Span,
	},

	#[error("unmatched inputs size")]
	UnmatchedInputsSizes {
		found: Vec<Spanned<u16>>,
		span: Span,
	},
	#[error("unmatched inputs type")]
	UnmatchedInputsTypes { found: Vec<StackItem>, span: Span },

	#[error("you cannot store into a {found}")]
	InvalidStoreSymbol {
		found: SymbolKind,
		defined_at: Span,
		span: Span,
	},
	#[error("casting underflows the stack")]
	CastingUnderflowsStack(Span),
	#[error("unhandled data while casting")]
	UnhandledCastingData { found: Span, span: Span },
	#[error("too many bindings")]
	TooManyBindings(Span),
	#[error("unmatched items names")]
	UnmatchedNames {
		found: Vec<Spanned<Option<Name>>>,
		expected: Vec<Name>,
		span: Span,
	},

	#[error("illegal vector function call")]
	IllegalVectorCall { defined_at: Span, span: Span },
	#[error("illegal top-level expression")]
	IllegalTopLevelExpr(Span),
	#[error("you cannot use {found} here")]
	IllegalSymbolUse {
		found: SymbolKind,
		defined_at: Span,
		span: Span,
	},
	#[error("you cannot take a pointer to a {found}")]
	IllegalPtrSymbol {
		found: SymbolKind,
		defined_at: Span,
		span: Span,
	},

	#[error("{was_redefined} redefinition")]
	SymbolRedefinition {
		was_redefined: SymbolKind,
		defined_at: Span,
		span: Span,
	},
	#[error("label redefinition")]
	LabelRedefinition { defined_at: Span, span: Span },
	#[error("unknown symbol")]
	UnknownSymbol(Span),
	#[error("no such label in this scope")]
	UnknownLabel(Span),
	#[error("not a {expected}")]
	InvalidSymbol {
		expected: SymbolKind,
		defined_at: Span,
		span: Span,
	},
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
