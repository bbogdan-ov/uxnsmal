use std::fmt::Display;

use smallvec::SmallVec;

use crate::{
	lexer::{Radix, Span, TokenKind},
	symbols::FuncSignature,
	typechecker::{StackMatch, Type},
};

pub type Result<T> = std::result::Result<T, Error>;

/// Error kind
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
	// ==============================
	// Temporary errors because UXNSMAL is still WIP
	// ==============================
	NoCustomTypesYet,

	// ==============================
	// Syntax errors
	// ==============================
	UnknownToken,

	Expected {
		expected: TokenKind,
		found: TokenKind,
	},
	ExpectedNumber {
		found: TokenKind,
	},
	UnexpectedToken,

	InvalidCharLiteral,
	UnknownCharEscape(char),

	UnclosedComment,
	UnclosedString,

	BadNumber(Radix),
	NumberIsTooLarge,
	ByteIsTooLarge,

	EmptyFile,

	// ==============================
	// Type errors
	// ==============================
	InvalidStackSignature,
	MismatchedBlockStack,

	SymbolRedefinition,
	NameTakedByIntrinsic,
	LabelRedefinition,
	JumpNotInBlock,

	IntrinsicInvalidStackSignature,
	IntrinsicInvalidStackHeight {
		expected: usize,
		found: usize,
	},

	NoResetVector,
	ResetFuncIsNotVector,
	IllegalVectorCall,
	IllegalConstantPtr,
	IllegalOpsInData,

	UnknownSymbol,
	UnknownLabel,
}
impl ErrorKind {
	/// Build a error from error kind and span
	pub fn err(self, span: Span) -> Error {
		Error::new(self, span)
	}
}
impl Display for ErrorKind {
	#[rustfmt::skip]
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		macro_rules! w {
			($($arg:tt)*) => {
				write!(f, $($arg,)*)
			};
		}

		match self {
			// ==============================
			// Temporary errors because UXNSMAL is still WIP
			// ==============================
			Self::NoCustomTypesYet => w!("unknown type, no there is no way to define custom types yet..."),

			// ==============================
			// Syntax errors
			// ==============================
			Self::UnknownToken => w!("unknown token"),

			Self::Expected { expected, found } => w!("expected {expected}, but found {found}"),
			Self::ExpectedNumber { found } => w!("expected number, but found {found}"),
			Self::UnexpectedToken => w!("unexpected token"),

			Self::InvalidCharLiteral => w!("invalid character literal"),
			Self::UnknownCharEscape(ch) => w!("unknown character escape '\\{ch}'"),

			Self::UnclosedComment => w!("unclosed comment"),
			Self::UnclosedString => w!("unclosed string"),

			Self::BadNumber(r) => w!("bad {r} number literal"),
			Self::NumberIsTooLarge => w!("number is too large to be stored even in 2 bytes (16 bits)"),
			Self::ByteIsTooLarge => w!("byte number is too large"),

			Self::EmptyFile => w!("empty file? ok"),

			// ==============================
			// Type errors
			// ==============================
			Self::InvalidStackSignature => w!("invalid stack signature"),
			Self::MismatchedBlockStack => w!("mismatched stack signature at the end of block"),

			Self::SymbolRedefinition => w!("symbol redefinition"),
			Self::NameTakedByIntrinsic => w!("this name is taken by an intrinsic"),
			Self::LabelRedefinition => w!("label redefinition"),
			Self::JumpNotInBlock => w!("'jump' operation only allowed in blocks"),

			Self::IntrinsicInvalidStackSignature => w!("invalid stack signature for intrinsic"),
			Self::IntrinsicInvalidStackHeight { .. } => w!("invalid stack height for intrinsic"),

			Self::NoResetVector => w!("'on-reset' vector function was not defined"),
			Self::ResetFuncIsNotVector => w!("'on-reset' must be a vector function"),
			Self::IllegalVectorCall => w!("calling vector functions is illegal"),
			Self::IllegalConstantPtr => w!("pointer to a constant is illegal"),
			Self::IllegalOpsInData => w!("data block cannot evaluate code inside"),

			Self::UnknownSymbol => w!("unknown symbol"),
			Self::UnknownLabel => w!("no such label in this scope"),
		}
	}
}
impl std::error::Error for ErrorKind {}

/// Error hint kind
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HintKind {
	CausedBy,
	ConsumedHere,
	DefinedHere,
	BecauseOf { typ: Type },
	SizeIs { size: u8 },
	ExpectedType { expected: Type, found: Type },
	ExpectedAnyByte { found: Type },
	ExpectedAnyShort { found: Type },
	ExpectedAnyBytePtr { inner: Type, found: Type },
	ExpectedAnyShortPtr { inner: Type, found: Type },
	ExpectedAnyShortFuncPtr { inner: FuncSignature, found: Type },
	ExpectedAnyPtr { found: Type },
}
impl Display for HintKind {
	#[rustfmt::skip]
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		macro_rules! w {
			($($arg:tt)*) => {
				write!(f, $($arg,)*)
			};
		}

		match self {
			Self::CausedBy => w!("caused by this"),
			Self::ConsumedHere => w!("consumed here"),
			Self::DefinedHere => w!("defined here"),
			Self::BecauseOf { typ } => w!("because of '{typ}'"),
			Self::SizeIs { size } => {
				w!("size is {size} ")?;
				if *size == 1 { w!("byte") } else { w!("bytes") }
			}
			Self::ExpectedType { expected, found } => w!("expected '{expected}', found '{found}'"),
			Self::ExpectedAnyByte { found } => w!("expected 'byte' or 'ptr <any>', found '{found}'"),
			Self::ExpectedAnyShort { found } => w!("expected 'short', 'ptr2 <any>' or 'funptr <any>', found '{found}'"),
			Self::ExpectedAnyBytePtr { inner, found } => w!("expected 'byte' or 'ptr {inner}', found '{found}'"),
			Self::ExpectedAnyShortPtr { inner, found } => w!("expected 'short' or 'ptr2 {inner}', found '{found}'"),
			Self::ExpectedAnyShortFuncPtr { inner, found } => w!("expected 'short' or 'funptr {inner}', found '{found}'"),
			Self::ExpectedAnyPtr { found } => w!("expected 'ptr <any>' or 'ptr2 <any>', found '{found}'"),
		}
	}
}

/// Error hint
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hint {
	pub kind: HintKind,
	pub span: Span,
}

/// Error hints list
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Hints(SmallVec<[Hint; Self::MAX_HINTS]>);
impl Hints {
	pub const MAX_HINTS: usize = 8;

	pub fn push(&mut self, kind: HintKind, span: Span) {
		if self.0.len() < Self::MAX_HINTS && !self.0.iter().any(|h| h.span == span) {
			self.0.push(Hint { kind, span });
		}
	}

	pub fn list(&self) -> &SmallVec<[Hint; Self::MAX_HINTS]> {
		&self.0
	}
}

/// Expected and found stacks
#[derive(Debug, PartialEq, Eq)]
pub struct ErrorStacks {
	pub expected: Vec<Type>,
	pub found: Vec<Type>,
	pub mtch: StackMatch,
}

// FIXME: the size of the error struct is too big (aroung 1KB) and this type returns almost from
// everywhere, i should already implement problems/diagnostics collection so these big ass structs
// will live only inside these collections
/// UXNSMAL error
#[derive(Debug, PartialEq, Eq)]
pub struct Error {
	pub kind: ErrorKind,
	pub span: Option<Span>,
	pub stacks: Option<ErrorStacks>,
	pub hints: Hints,
}
impl Error {
	pub fn new(kind: ErrorKind, span: Span) -> Self {
		Self {
			kind,
			span: Some(span),
			stacks: None,
			hints: Hints::default(),
		}
	}
	// Is this a good name?..
	/// Creates [`Error`] without span
	pub fn everywhere(kind: ErrorKind) -> Self {
		Self {
			kind,
			span: None,
			stacks: None,
			hints: Hints::default(),
		}
	}

	pub fn symbol_redefinition(span: Span, defined_span: Span) -> Self {
		let mut err = ErrorKind::SymbolRedefinition.err(span);
		err.hints.push(HintKind::DefinedHere, defined_span);
		err
	}
}
