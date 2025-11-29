use crate::{
	lexer::{Radix, Span, Spanned, TokenKind},
	symbols::{Name, Type},
	typechecker::StackItem,
};

pub type Result<T> = std::result::Result<T, Error>;

/// Type match
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeMatch {
	/// Any basic type (byte, short, pointers, etc)
	AnyOperand,
	/// Any number (byte, short, etc)
	AnyNumber,
	/// Any variable pointer (byte ptr, short ptr)
	AnyVarPtr,
	Exact(Type),
}

/// Stack error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackError {
	Invalid {
		found: Vec<StackItem>,
	},
	TooFew {
		found: Vec<StackItem>,
		consumed_by: Vec<Span>,
	},
	TooMany {
		found: Vec<StackItem>,
		caused_by: Vec<Span>,
	},
}

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
		// TODO: this field should accept `Vec<StackItem>`, because we are also comparing names of
		// the stack items
		expected: Vec<Type>,
		stack: StackError,
		span: Span,
	},
	#[error("invalid stack signature")]
	InvalidIntrStack {
		expected: Vec<TypeMatch>,
		stack: StackError,
		span: Span,
	},
	#[error("invalid arithmetic input types")]
	InvalidArithmeticStack { stack: StackError, span: Span },
	#[error("invalid condition type")]
	InvalidConditionType { stack: StackError, span: Span },

	#[error("unmatched inputs size")]
	UnmatchedInputsSizes {
		found: Vec<Spanned<u16>>,
		span: Span,
	},
	#[error("unmatched inputs type")]
	UnmatchedInputsTypes { found: Vec<StackItem>, span: Span },

	#[error("invalid store symbol")]
	InvalidStoreSymbol(Span),
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
	#[error("illegal pointer to constant")]
	IllegalPtrToConst { defined_at: Span, span: Span },
	#[error("illegal top-level expression")]
	IllegalTopLevelExpr(Span),

	#[error("'on-reset' vector function is not defined")]
	NoResetVector,

	#[error("symbol redefinition")]
	SymbolRedefinition { defined_at: Span, span: Span },
	#[error("label redefinition")]
	LabelRedefinition { defined_at: Span, span: Span },
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
			| Self::InvalidArithmeticStack { span, .. }
			| Self::InvalidConditionType { span, .. }
			| Self::IllegalVectorCall { span, .. }
			| Self::IllegalPtrToConst { span, .. }
			| Self::IllegalTopLevelExpr(span)
			| Self::SymbolRedefinition { span, .. }
			| Self::LabelRedefinition { span, .. }
			| Self::UnknownSymbol(span)
			| Self::UnknownLabel(span)
			| Self::InvalidIntrStack { span, .. }
			| Self::UnmatchedInputsSizes { span, .. }
			| Self::UnmatchedInputsTypes { span, .. }
			| Self::InvalidStoreSymbol(span)
			| Self::CastingUnderflowsStack(span)
			| Self::UnhandledCastingData { span, .. }
			| Self::TooManyBindings(span)
			| Self::UnmatchedNames { span, .. } => Some(*span),

			Self::NoResetVector => None,
		}
	}
}
