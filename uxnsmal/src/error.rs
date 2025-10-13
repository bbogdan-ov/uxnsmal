use crate::lexer::{Radix, Span, TokenKind};

pub type Result<T> = std::result::Result<T, Error>;

/// Error kind
#[derive(thiserror::Error, Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
	// ==============================
	// Temporary errors because UXNSMAL is still WIP
	// ==============================
	#[error("unknown type, and there is no way to define custom types yet...")]
	NoCustomTypesYet,
	#[error("there is no local definitions yet...")]
	NoLocalDefsYet,
	#[error("there is no code evaluation inside data blocks yet...")]
	NoDataCodeEvaluationYet,

	// ==============================
	// Syntax errors
	// ==============================
	#[error("unknown token")]
	UnknownToken,

	#[error("expected {expected}, but found {found}")]
	Expected {
		expected: TokenKind,
		found: TokenKind,
	},
	#[error("expected number, but found {found}")]
	ExpectedNumber { found: TokenKind },
	#[error("expected condition, but found {found}")]
	ExpectedCondition { found: TokenKind },
	#[error("unexpected token")]
	UnexpectedToken,

	#[error("invalid character literal")]
	InvalidCharLiteral,
	#[error("unknown character escape '\\{0}'")]
	UnknownCharEscape(char),

	#[error("unclosed comment")]
	UnclosedComment,
	#[error("unclosed string")]
	UnclosedString,

	#[error("bad {0} number literal")]
	BadNumber(Radix),
	#[error("byte literal is too big, max is 255")]
	ByteIsTooBig,
	#[error("number literal is too big, max is 65535")]
	NumberIsTooBig,

	#[error("empty file? ok")]
	EmptyFile,

	// ==============================
	// Type errors
	// ==============================
	#[error("invalid stack signature")]
	InvalidStackSignature,
	#[error("not enough inputs")]
	NotEnoughInputs,
	#[error("non-empty stack at the end of vector function")]
	VectorNonEmptyStack,
	#[error("invalid condition output type")]
	InvalidConditionOutput,
	#[error("unmatched inputs type")]
	UnmatchedInputs,
	#[error("unmatched inputs size")]
	UnmatchedInputsSize,

	#[error("illegal vector function call")]
	IllegalVectorCall,
	#[error("illegal pointer to constant")]
	IllegalPtrToConst,
	#[error("illegal top-level expression")]
	IllegalTopLevelExpr,

	#[error("'on-reset' vector function is not defined")]
	NoResetVector,

	#[error("symbol redefinition")]
	SymbolRedefinition,
	#[error("label redefinition")]
	LabelRedefinition,
	#[error("unknown symbol")]
	UnknownSymbol,
	#[error("no such label in this scope")]
	UnknownLabel,
}
impl ErrorKind {
	/// Build a error from error kind and span
	pub fn err(self, span: Span) -> Error {
		Error::new(self, span)
	}
}

/// Error
#[derive(Debug, PartialEq, Eq)]
pub struct Error {
	pub kind: ErrorKind,
	pub span: Option<Span>,
}
impl Error {
	pub fn new(kind: ErrorKind, span: Span) -> Self {
		Self {
			kind,
			span: Some(span),
		}
	}
	// Is this a good name?..
	/// Creates [`Error`] without span
	pub fn everywhere(kind: ErrorKind) -> Self {
		Self { kind, span: None }
	}
}
