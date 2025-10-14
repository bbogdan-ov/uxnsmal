use crate::lexer::{Radix, Span, TokenKind};

pub type Result<T> = std::result::Result<T, Error>;

/// Error
#[derive(thiserror::Error, Debug, Clone, PartialEq, Eq)]
pub enum Error {
	// ==============================
	// Temporary errors because UXNSMAL is still WIP
	// ==============================
	#[error("unknown type, and there is no way to define custom types yet...")]
	NoCustomTypesYet(Span),
	#[error("there is no local definitions yet...")]
	NoLocalDefsYet(Span),
	#[error("there is no code evaluation inside data blocks yet...")]
	NoDataCodeEvaluationYet(Span),

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
	InvalidStackSignature { span: Span },
	#[error("not enough inputs")]
	NotEnoughInputs { span: Span },
	#[error("non-empty stack at the end of vector function")]
	VectorNonEmptyStack { span: Span },
	#[error("invalid condition output type")]
	InvalidConditionOutput { span: Span },
	#[error("unmatched inputs type")]
	UnmatchedInputs { span: Span },
	#[error("unmatched inputs size")]
	UnmatchedInputsSize { span: Span },

	#[error("illegal vector function call")]
	IllegalVectorCall { span: Span },
	#[error("illegal pointer to constant")]
	IllegalPtrToConst { span: Span },
	#[error("illegal top-level expression")]
	IllegalTopLevelExpr(Span),

	#[error("'on-reset' vector function is not defined")]
	NoResetVector,

	#[error("symbol redefinition")]
	SymbolRedefinition { span: Span },
	#[error("label redefinition")]
	LabelRedefinition { span: Span },
	#[error("unknown symbol")]
	UnknownSymbol(Span),
	#[error("no such label in this scope")]
	UnknownLabel(Span),
}
impl Error {
	pub fn span(&self) -> Option<Span> {
		// Uuh i mean, at least it is ✨typesafe✨
		match self {
			Self::NoCustomTypesYet(span)
			| Self::NoLocalDefsYet(span)
			| Self::NoDataCodeEvaluationYet(span)
			| Self::UnknownToken(span)
			| Self::Expected { span, .. }
			| Self::ExpectedNumber { span, .. }
			| Self::ExpectedCondition { span, .. }
			| Self::UnexpectedToken(span)
			| Self::InvalidCharLiteral(span)
			| Self::UnknownCharEscape(_, span)
			| Self::UnclosedComment(span)
			| Self::UnclosedString(span)
			| Self::BadNumber(_, span)
			| Self::ByteIsTooBig(span)
			| Self::NumberIsTooBig(span)
			| Self::InvalidStackSignature { span }
			| Self::NotEnoughInputs { span }
			| Self::VectorNonEmptyStack { span }
			| Self::InvalidConditionOutput { span }
			| Self::UnmatchedInputs { span }
			| Self::UnmatchedInputsSize { span }
			| Self::IllegalVectorCall { span }
			| Self::IllegalPtrToConst { span }
			| Self::IllegalTopLevelExpr(span)
			| Self::SymbolRedefinition { span }
			| Self::LabelRedefinition { span }
			| Self::UnknownSymbol(span)
			| Self::UnknownLabel(span) => Some(*span),

			Self::NoResetVector => None,
		}
	}
}

/// Hint kind
#[derive(Debug)]
pub enum HintKind {}

/// Problem hint
#[derive(Debug)]
pub struct Hint {
	pub kind: HintKind,
	pub span: Span,
}
impl Hint {
	pub fn new(kind: HintKind, span: Span) -> Self {
		Self { kind, span }
	}
}
