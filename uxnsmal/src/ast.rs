//! # But why is there an AST for a concatenative language??
//!
//! - I want to separate syntax from the intermediate program because i plan to add more syntax sugar
//!   that is simpler to parse first to AST and then parse it to the intermediate code.
//!
//! - Also it would be simpler to typecheck an AST and give more info about the error based on its
//!   context/location because all token spans are stored in the AST nodes themselves, but this is
//!   not possible with intermediate program/code (because i don't want to store any info about the
//!   source code inside intermediate code)

use std::fmt::Debug;

use crate::{
	lexer::Spanned,
	program::{Intrinsic, IntrinsicMode},
	symbols::{FuncSignature, Name, Type},
};

/// AST node
#[derive(Clone, PartialEq, Eq)]
pub enum Node {
	/// Expression node
	Expr(Expr),
	/// Definition node
	Def(Def),
}
impl From<Expr> for Node {
	fn from(value: Expr) -> Self {
		Self::Expr(value)
	}
}
impl From<Def> for Node {
	fn from(value: Def) -> Self {
		Self::Def(value)
	}
}
impl Debug for Node {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Expr(e) => write!(f, "Expr({e:?})"),
			Self::Def(s) => write!(f, "Def({s:#?})"),
		}
	}
}

/// Typed symbol
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypedSymbol {
	Func,
	Var,
	Data,
	Const,
}

/// Typed pointer to
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypedPtrTo {
	Func,
	Var,
	Data,
}

/// Typed or not
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum Typed<T> {
	#[default]
	Untyped,
	Typed(T),
}

/// Expression
#[derive(Clone, PartialEq, Eq)]
pub enum Expr {
	Byte(u8),
	Short(u16),
	/// Push string address onto the stack and store the string into ROM
	String(Box<str>),
	// TODO: allow paddings only outside of functions and inside data definitions
	/// Put N number of zero bytes into ROM
	Padding(u16),

	/// Intrinsic call
	Intrinsic(Intrinsic, IntrinsicMode),

	Symbol(Name, Typed<TypedSymbol>),
	PtrTo(Name, Typed<TypedPtrTo>),

	Block {
		looping: bool,
		label: Spanned<Name>,
		body: Box<[Spanned<Node>]>,
	},
	Jump {
		label: Spanned<Name>,
		conditional: bool,
	},
	If {
		if_body: Box<[Spanned<Node>]>,
		else_body: Option<Box<[Spanned<Node>]>>,
	},
	While {
		condition: Box<[Spanned<Node>]>,
		body: Box<[Spanned<Node>]>,
	},
}
impl Debug for Expr {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Byte(_)
			| Self::Short(_)
			| Self::String(_)
			| Self::Padding(_)
			| Self::Intrinsic(_, _)
			| Self::Symbol(_, _)
			| Self::PtrTo(_, _)
			| Self::Jump { .. } => write!(f, "{self:?}"),

			Self::Block { .. } | Self::If { .. } | Self::While { .. } => write!(f, "{self:#?}"),
		}
	}
}

/// Definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Def {
	Func(FuncDef),
	Var(VarDef),
	Const(ConstDef),
	Data(DataDef),
}

/// Function arguments
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FuncArgs {
	Vector,
	Proc {
		inputs: Box<[Spanned<Type>]>,
		outputs: Box<[Spanned<Type>]>,
	},
}
impl FuncArgs {
	pub fn to_signature(&self) -> FuncSignature {
		match self {
			Self::Vector => FuncSignature::Vector,
			Self::Proc { inputs, outputs } => FuncSignature::Proc {
				inputs: inputs.iter().map(|t| t.x.clone()).collect(),
				outputs: outputs.iter().map(|t| t.x.clone()).collect(),
			},
		}
	}
}

/// Function definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncDef {
	pub name: Name,
	pub args: FuncArgs,
	pub body: Box<[Spanned<Node>]>,
}

/// Variable definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDef {
	pub name: Name,
	pub typ: Spanned<Type>,
}

/// Constant definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstDef {
	pub name: Name,
	pub typ: Spanned<Type>,
	pub body: Box<[Spanned<Node>]>,
}

/// Data definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataDef {
	pub name: Name,
	pub body: Box<[Spanned<Node>]>,
}

/// Program abstract syntax tree
#[derive(Debug, Clone)]
pub struct Ast {
	pub nodes: Vec<Spanned<Node>>,
}
impl Default for Ast {
	fn default() -> Self {
		Self {
			nodes: Vec::with_capacity(128),
		}
	}
}

// Typed abstract syntax tree
// A wrapper for [`Ast`] to mark it as "typed"
#[derive(Debug, Clone)]
pub struct TypedAst(pub(crate) Ast);
impl std::ops::Deref for TypedAst {
	type Target = Ast;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}
impl std::ops::DerefMut for TypedAst {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}
