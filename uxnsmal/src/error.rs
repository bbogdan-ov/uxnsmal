use crate::lexer::{Radix, Span, TokenKind};

pub type Result<T> = std::result::Result<T, Error>;

/// Error kind
#[derive(thiserror::Error, Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
	// ==============================
	// Temporary errors because UXNSMAL is still WIP
	// ==============================
	#[error("unknown type, no there is no way to define custom types yet...")]
	NoCustomTypesYet,
	#[error("you cannot define local symbols yet...")]
	NoLocalDefsYet,

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
	#[error("number is too large to be stored even in 2 bytes (16 bits)")]
	NumberIsTooLarge,

	#[error("empty file? ok")]
	EmptyFile,

	// ==============================
	// Type errors
	// ==============================
	#[error("invalid stack signature")]
	InvalidStackSignature,

	#[error("symbol redefinition")]
	SymbolRedefinition,
	#[error("'jump' operation only allowed in blocks")]
	JumpNotInBlock,

	#[error("'on-reset' vector function is not defined")]
	NoResetVector,
	#[error("'on-reset' must be a vector function")]
	ResetFuncIsNotVector,
	#[error("calling vector functions is illegal")]
	IllegalVectorCall,
	#[error("pointer to a constant is illegal")]
	IllegalConstantPtr,
	#[error("illegal use of expression")]
	IllegalExpr,

	#[error("unknown symbol")]
	UnknownSymbol,
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
