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
	program::{IntrMode, Intrinsic},
	symbols::{ConstSignature, FuncSignature, Name, SymbolSignature, Type, VarSignature},
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

// TODO: consider replacing "padding" `$<n>` with `<expr> * <n>`.
// This expression will repeat `<expr>` N times, when "paddings" `$<n>` only repeat zeros N times.
// If i'll consider adding this feature i need to think about changing
// short number literal syntax. (`65535*`)

/// Expression
#[derive(Clone, PartialEq, Eq)]
pub enum Expr {
	Byte(u8),
	Short(u16),
	/// Push string address onto the stack and store the string into ROM
	String(Box<str>),
	/// Put N number of zero bytes into ROM
	Padding(u16),

	/// Intrinsic call
	Intrinsic(Intrinsic, IntrMode),

	Symbol(Name),
	PtrTo(Name),

	Block {
		looping: bool,
		label: Spanned<Name>,
		body: Box<[Spanned<Node>]>,
	},
	Jump {
		label: Spanned<Name>,
	},
	Return,
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
			Self::Byte(b) => write!(f, "Byte({b})"),
			Self::Short(s) => write!(f, "Short({s})"),
			Self::String(s) => write!(f, "String({s:?})"),
			Self::Padding(p) => write!(f, "Padding({p})"),
			Self::Intrinsic(i, m) => write!(f, "Intrinsic({i:?}, {m:?})"),

			Self::Symbol(n) => write!(f, "Symbol({n:?})"),
			Self::PtrTo(n) => write!(f, "PtrTo({n:?})"),

			Self::Block {
				looping,
				label,
				body,
			} => write!(f, "Block({label:?}, {looping}) {body:#?}"),
			Self::Jump { label } => write!(f, "Jump({label:#?})"),
			Self::If { if_body, else_body } => match else_body {
				Some(else_body) => write!(f, "If {if_body:#?} {else_body:#?}"),
				None => write!(f, "If {if_body:#?}"),
			},
			Self::While { condition, body } => write!(f, "While {condition:#?} {body:#?}"),
			Self::Return => write!(f, "Return"),
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
impl Def {
	pub fn name(&self) -> &Name {
		match self {
			Self::Func(f) => &f.name,
			Self::Var(v) => &v.name,
			Self::Const(c) => &c.name,
			Self::Data(d) => &d.name,
		}
	}

	pub fn to_signature(&self) -> SymbolSignature {
		match self {
			Self::Func(def) => SymbolSignature::Func(def.args.to_signature()),
			Self::Var(def) => SymbolSignature::Var(VarSignature {
				typ: def.typ.x.clone(),
			}),
			Self::Const(def) => SymbolSignature::Const(ConstSignature {
				typ: def.typ.x.clone(),
			}),
			Self::Data(_) => SymbolSignature::Data,
		}
	}
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
