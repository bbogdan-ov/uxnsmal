//! # But why is there an AST for a concatenative language??
//!
//! - I want to separate syntax from the intermediate program because i plan to add more syntax sugar
//!   that is simpler to parse first to AST and then parse it to the intermediate code.
//!
//! - Also it would be simpler to typecheck an AST and give more info about the error based on its
//!   context/location because all token spans are stored in the AST nodes themselves, but this is
//!   not possible with intermediate program/code (because i don't want to store any info about the
//!   source code inside intermediate code).

use std::{
	fmt::{Debug, Display},
	path::PathBuf,
	rc::Rc,
};

use crate::{
	ir,
	lexer::{Span, Spanned},
	symbol::{self, Access, FuncSignature, Name},
};

/// AST node.
#[derive(Debug, Clone)]
pub enum Node {
	/// Expression node.
	Expr(Expr),
	/// Definition node.
	Def(Def),
}
impl Node {
	pub fn span(&self) -> Span {
		match self {
			Self::Expr(expr) => expr.span(),
			Self::Def(def) => def.span(),
		}
	}
}

/// AST body `{ ... }`.
#[derive(Debug, Clone)]
pub struct Body {
	pub nodes: Vec<Node>,
	/// Span of the closing '}'
	pub end_span: Span,
}

/// An unknown type used within AST.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownType {
	Byte,
	Short,
	BytePtr(Box<UnknownType>),
	ShortPtr(Box<UnknownType>),
	FuncPtr(FuncSignature<UnknownType>),
	/// Either user type, enum, struct, etc.
	Type(Name),
	Array {
		typ: Box<UnknownType>,
		count: u16,
	},
	UnsizedArray {
		typ: Box<UnknownType>,
	},
}

/// Type and optional name pair.
/// `type:name`
#[derive(Debug, Clone, Eq)]
pub struct Pair<T> {
	pub typ: Spanned<T>,
	pub name: Option<Spanned<Name>>,
	/// Span of the whole node, including type and name.
	pub span: Span,
}
impl<T: Display> Display for Pair<T> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if let Some(name) = &self.name {
			write!(f, "{}:{}", self.typ.x, name.x)
		} else {
			write!(f, "{}", self.typ.x)
		}
	}
}
impl<T: PartialEq> PartialEq for Pair<T> {
	fn eq(&self, other: &Self) -> bool {
		self.typ == other.typ && self.name == other.name
	}
}

/// Program abstract syntax tree.
#[derive(Debug, Clone)]
pub struct Ast {
	pub nodes: Vec<Node>,
}
impl Default for Ast {
	fn default() -> Self {
		Self {
			nodes: Vec::with_capacity(128),
		}
	}
}

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
	Store { access: Spanned<Access>, span: Span },
	/// `as ([types...])`
	Cast {
		types: Vec<Pair<UnknownType>>,
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
	Intr {
		kind: ir::Intr,
		mode: ir::IntrMode,
		span: Span,
	},

	/// Any unknown identifier.
	/// `<access>`
	Symbol { access: Access, span: Span },
	/// `&<access>`
	PtrTo { access: Spanned<Access>, span: Span },

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
			| Self::Intr { span, .. }
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

/// Definition.
#[derive(Debug, Clone)]
pub enum Def {
	Func(FuncDef),
	Var(VarDef),
	Const(ConstDef),
	Data(DataDef),
	Type(TypeDef),
	Enum(EnumDef),
	Struct(StructDef),
}
impl Def {
	pub fn name(&self) -> &Name {
		match self {
			Self::Func(def) => &def.name.x,
			Self::Var(def) => &def.name.x,
			Self::Const(def) => &def.name.x,
			Self::Data(def) => &def.name.x,
			Self::Type(def) => &def.name.x,
			Self::Enum(def) => &def.name.x,
			Self::Struct(def) => &def.name.x,
		}
	}
	pub fn span(&self) -> Span {
		match self {
			Self::Func(def) => def.span,
			Self::Var(def) => def.span,
			Self::Const(def) => def.span,
			Self::Data(def) => def.span,
			Self::Type(def) => def.span,
			Self::Enum(def) => def.span,
			Self::Struct(def) => def.span,
		}
	}
}

/// Function definition.
#[derive(Debug, Clone)]
pub struct FuncDef {
	pub name: Spanned<Name>,
	pub signature: Spanned<FuncSignature<UnknownType>>,
	pub body: Body,
	/// Span of the function header.
	///
	/// fun my-func ( -- ) {
	/// ^^^^^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition.
	pub symbol: Option<Rc<symbol::Func>>,
}

/// Variable definition.
#[derive(Debug, Clone)]
pub struct VarDef {
	pub name: Spanned<Name>,
	pub in_rom: bool,
	pub typ: Spanned<UnknownType>,
	/// Span of the whole var definition.
	pub span: Span,
	/// Symbol associated with this definition.
	pub symbol: Option<Rc<symbol::Var>>,
}

/// Constant definition.
#[derive(Debug, Clone)]
pub struct ConstDef {
	pub name: Spanned<Name>,
	pub typ: Spanned<UnknownType>,
	pub body: Body,
	/// Span of the const header.
	///
	/// const byte MY_CONST {
	/// ^^^^^^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition.
	pub symbol: Option<Rc<symbol::Const>>,
}

// TODO: allow define nested data blocks so they can share
// the same data but different parts of it.

/// Data definition.
#[derive(Debug, Clone)]
pub struct DataDef {
	pub name: Spanned<Name>,
	pub body: Body,
	/// Span of the data header.
	///
	/// data my-data {
	/// ^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition.
	pub symbol: Option<Rc<symbol::Data>>,
}

/// User type definition.
#[derive(Debug, Clone)]
pub struct TypeDef {
	pub name: Spanned<Name>,
	pub inherits: Spanned<UnknownType>,
	pub alias: bool,
	/// Span of the whole type definition.
	pub span: Span,
	/// Symbol associated with this definition.
	pub symbol: Option<Rc<symbol::AnyUserType>>,
}

/// Enum definition variant.
#[derive(Debug, Clone)]
pub struct EnumDefVariant {
	pub name: Spanned<Name>,
	pub body: Option<Body>,
}

/// Enum definition.
#[derive(Debug, Clone)]
pub struct EnumDef {
	pub name: Spanned<Name>,
	pub inherits: Spanned<UnknownType>,
	pub variants: Vec<EnumDefVariant>,
	pub alias: bool,
	/// Span of the enum header.
	///
	/// enum byte MyEnum {
	/// ^^^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition.
	pub symbol: Option<Rc<symbol::Enum>>,
}

/// Structure definition field.
#[derive(Debug, Clone)]
pub struct StructDefField {
	pub typ: Spanned<UnknownType>,
	pub name: Spanned<Name>,
	pub span: Span,
}

/// Structure definition.
#[derive(Debug, Clone)]
pub struct StructDef {
	pub name: Spanned<Name>,
	pub fields: Vec<StructDefField>,
	/// Span of the struct header.
	///
	/// struct MyStruct {
	/// ^^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition.
	pub symbol: Option<Rc<symbol::Struct>>,
}
