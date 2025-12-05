use std::fmt::Debug;

use crate::{
	ast::Node,
	lexer::{Span, Spanned},
	program::{IntrMode, Intrinsic},
	symbols::{Name, NamedType, UnsizedType},
};

/// `else` block
#[derive(Debug, Clone)]
pub struct ElseBlock {
	pub body: Vec<Node>,
	/// Span of the `else` keyword
	pub span: Span,
}

/// `elif` block
#[derive(Debug, Clone)]
pub struct ElseIfBlock {
	pub condition: Spanned<Vec<Node>>,
	pub body: Vec<Node>,
	/// Span of the `elif` keyword
	pub span: Span,
}

/// Expression
#[derive(Debug, Clone)]
pub enum Expr {
	/// Number from 0 to 255
	Byte { value: u8, span: Span },
	/// Number from 0 to 65535
	Short { value: u16, span: Span },
	/// `"<contents...>"`
	String { string: Box<str>, span: Span },
	/// `$<n>`
	Padding { value: u16, span: Span },

	/// `-> <symbol>`
	Store { symbol: Spanned<Name>, span: Span },
	/// `as ([types...])`
	Cast {
		types: Vec<NamedType<UnsizedType>>,
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

	/// Intrinsic call
	/// `pop`, `store`, `add`, etc...
	Intrinsic {
		kind: Intrinsic,
		mode: IntrMode,
		span: Span,
	},

	/// Any unknown identifier
	Symbol { name: Name, span: Span },
	/// `&<symbol>`
	PtrTo { name: Spanned<Name>, span: Span },

	/// `@<label> { [nodes...] }`
	Block {
		looping: bool,
		label: Spanned<Name>,
		body: Vec<Node>,
		/// Span of the block's head
		/// @label {
		/// ^^^^^^^^
		span: Span,
	},
	/// `jump @<label>`
	Jump { label: Spanned<Name>, span: Span },
	/// `return`
	Return { span: Span },
	/// `if { [nodes...] }`
	/// `if { [nodes...] } else { [nodes...] }`
	/// `if { [nodes...] } [elif { [nodes...] }...] [else { [nodes...] }]`
	If {
		if_body: Vec<Node>,
		/// Span of the `if` keyword
		if_span: Span,
		elif_blocks: Vec<ElseIfBlock>,
		else_block: Option<ElseBlock>,
		/// Span of the `if` header
		/// if {
		/// ^^^^
		span: Span,
	},
	/// `while <condition> { [nodes...] }`
	While {
		condition: Spanned<Vec<Node>>,
		body: Vec<Node>,
		/// Swap of the `while` header
		/// while <condition> {
		/// ^^^^^^^^^^^^^^^^^^^
		span: Span,
	},
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
			| Self::Jump { span, .. }
			| Self::Return { span, .. }
			| Self::If { span, .. }
			| Self::While { span, .. } => *span,
		}
	}
}
