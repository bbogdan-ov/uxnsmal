use std::{
	borrow::Borrow,
	fmt::{Debug, Display},
	rc::Rc,
};

use crate::{
	lexer::Spanned,
	program::{Intrinsic, IntrinsicMode},
	symbols::FuncSignature,
	typechecker::Type,
};

/// Name of a symbol
/// May be not an existant symbol name
#[derive(Default, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(pub Rc<str>);
impl Name {
	pub fn new(string: &str) -> Self {
		Self(string.into())
	}
}
impl Debug for Name {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Name({:?})", self.0)
	}
}
impl Display for Name {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}
impl Borrow<str> for Name {
	fn borrow(&self) -> &str {
		&self.0
	}
}
impl AsRef<str> for Name {
	fn as_ref(&self) -> &str {
		&self.0
	}
}

/// AST node
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
	/// Expression node
	Expr(Expr),
	/// Definition node
	Def(Definition),
}
impl From<Expr> for Node {
	fn from(value: Expr) -> Self {
		Self::Expr(value)
	}
}
impl From<Definition> for Node {
	fn from(value: Definition) -> Self {
		Self::Def(value)
	}
}

/// Expression
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
	Byte(u8),
	Short(u16),
	/// Push string address onto the stack and store the string into ROM
	String(Box<str>),
	// TODO: allow paddings only outside of functions and inside data definitions
	/// Put N number of zero bytes into ROM
	Padding(u16),

	/// Intrinsic call
	/// Always without [`IntrinsicMode::SHORT`] mode
	Intrinsic(Intrinsic, IntrinsicMode),
	/// Use of a symbol
	Symbol(Name),
	/// Pointer to a symbol
	PtrTo(Name),

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
		body: Box<[Spanned<Node>]>,
	},

	Bind(Box<[Spanned<Name>]>),
}

/// Symbol definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Definition {
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
///
/// # But why is there an AST for a concatenative language??
///
/// - I want to separate syntax from the intermediate program because i plan to add more syntax sugar
///   that is simpler to parse first to AST and then parse it to the intermediate code.
///
/// - Also it would be simpler to typecheck an AST and give more info about the error based on its
///   context/location because all token spans are stored in the AST nodes themselves, but this is
///   not possible with intermediate program/code (because i don't want to store any info about the
///   source code inside intermediate code)
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
