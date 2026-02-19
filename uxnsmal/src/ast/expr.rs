use std::{fmt::Debug, path::PathBuf};

use crate::{
	ast::{Body, Node, UnknownType},
	lexer::{Span, Spanned},
	program::{IntrMode, Intrinsic},
	symbols::{Name, NamedType, SymbolAccess},
};

/// `if` or `else` block.
#[derive(Debug, Clone)]
pub struct IfBlock {
	pub body: Body,
	/// Span of the `if` or `else` keyword.
	pub span: Span,
}

/// `elif` block.
#[derive(Debug, Clone)]
pub struct ElifBlock {
	pub condition: Spanned<Vec<Node>>,
	pub body: Body,
	/// Span of the `elif` keyword.
	pub span: Span,
}

/// Expression.
#[derive(Debug, Clone)]
pub enum Expr {
	/// A number from 0 to 255.
	/// `255`, `0xff`
	Byte { value: u8, span: Span },
	/// A number from 0 to 65535.
	/// `65535*`, `0xffff*`
	Short { value: u16, span: Span },
	/// `"<string...>"`
	String { string: Box<str>, span: Span },
	/// `$<value>`
	Padding { value: u16, span: Span },

	/// `-> <access>`
	Store {
		access: Spanned<SymbolAccess>,
		span: Span,
	},
	/// `as ([types...])`
	Cast {
		types: Vec<NamedType<UnknownType>>,
		span: Span,
	},
	/// `-> ([names...])`
	Bind {
		names: Vec<Spanned<Name>>,
		span: Span,
	},
	/// `([names...])`
	ExpectBind {
		names: Vec<Spanned<Name>>,
		span: Span,
	},

	/// Intrinsic call.
	/// `pop`, `store`, `add`, etc...
	Intrinsic {
		kind: Intrinsic,
		mode: IntrMode,
		span: Span,
	},

	/// Any unknown identifier.
	/// `<access>`
	Symbol { access: SymbolAccess, span: Span },
	/// `&<access>`
	PtrTo {
		access: Spanned<SymbolAccess>,
		span: Span,
	},

	/// `@<label> { [body...] }`
	Block {
		looping: bool,
		label: Spanned<Name>,
		body: Body,
		/// Span of the block's head.
		///
		/// @label {
		/// ^^^^^^^^
		span: Span,
	},
	/// `break @<label>`
	Break { label: Spanned<Name>, span: Span },
	/// `return`
	Return { span: Span },
	/// `if { [body...] }`
	/// `if { [body...] } [elif { [body...] }...] [else { [body...] }]`
	If {
		if_block: IfBlock,
		elif_blocks: Vec<ElifBlock>,
		else_block: Option<IfBlock>,
	},
	/// `while <condition> { [body...] }`
	While {
		condition: Spanned<Vec<Node>>,
		body: Body,
		/// Span of the `while` header.
		///
		/// while <condition> {
		/// ^^^^^^^^^^^^^^^^^
		span: Span,
	},

	// TODO: instruduce `includen` to include first N bytes from a file.
	/// `include "<path>"`
	Include { path: Spanned<PathBuf>, span: Span },
}
impl Expr {
	pub fn span(&self) -> Span {
		match self {
			Self::Byte { span, .. }
			| Self::Short { span, .. }
			| Self::String { span, .. }
			| Self::Padding { span, .. }
			| Self::Store { span, .. }
			| Self::Cast { span, .. }
			| Self::Bind { span, .. }
			| Self::ExpectBind { span, .. }
			| Self::Intrinsic { span, .. }
			| Self::Symbol { span, .. }
			| Self::PtrTo { span, .. }
			| Self::Block { span, .. }
			| Self::Break { span, .. }
			| Self::Return { span, .. }
			| Self::While { span, .. }
			| Self::Include { span, .. } => *span,

			Self::If { if_block, .. } => if_block.span,
		}
	}
}
