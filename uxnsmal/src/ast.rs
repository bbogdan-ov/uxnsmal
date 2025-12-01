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
	error,
	lexer::{Span, Spanned},
	program::{IntrMode, Intrinsic},
	symbols::{
		ConstSignature, FuncSignature, Name, SymbolSignature, SymbolsTable, Type, TypeSignature,
		VarSignature,
	},
};

/// Type name
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeName {
	Byte,
	Short,
	BytePtr(Box<TypeName>),
	ShortPtr(Box<TypeName>),
	FuncPtr(FuncArgs),
	User(Name),
}
impl TypeName {
	pub fn to_type(self, symbols: &SymbolsTable, span: Span) -> error::Result<Type> {
		match self {
			Self::Byte => Ok(Type::Byte),
			Self::Short => Ok(Type::Short),
			Self::BytePtr(t) => Ok(Type::BytePtr(t.to_type(symbols, span)?.into())),
			Self::ShortPtr(t) => Ok(Type::ShortPtr(t.to_type(symbols, span)?.into())),
			Self::FuncPtr(args) => Ok(Type::FuncPtr(args.to_signature(symbols)?)),
			Self::User(name) => {
				let typ = symbols.get_type(&name, span)?;
				Ok(Type::User {
					name,
					size: typ.inherits.size(),
				})
			}
		}
	}
}

/// Type with a binded name
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BindedType {
	pub typ: TypeName,
	pub name: Option<Name>,
	pub span: Span,
}

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElseIf {
	pub condition: Box<[Spanned<Node>]>,
	pub body: Box<[Spanned<Node>]>,
}

/// Expression
#[derive(Clone, PartialEq, Eq)]
pub enum Expr {
	Byte(u8),
	Short(u16),
	/// Push string address onto the stack and store the string into ROM
	String(Box<str>),
	/// Put N number of zero bytes into ROM
	Padding(u16),

	/// Store value on top of the stack to a variable
	Store(Name),
	Cast(Box<[Spanned<TypeName>]>),
	Bind(Box<[Spanned<Name>]>),
	ExpectBind(Box<[Spanned<Name>]>),

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
		elseifs: Box<[ElseIf]>,
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

			Self::Store(n) => write!(f, "Store({n:?})"),
			Self::Cast(ts) => write!(f, "Cast({ts:?})"),
			Self::Bind(ns) => write!(f, "Bind({ns:?})"),
			Self::ExpectBind(ns) => write!(f, "ExpectBind({ns:?})"),

			Self::Intrinsic(i, m) => write!(f, "Intrinsic({i:?}, {m:?})"),

			Self::Symbol(n) => write!(f, "Symbol({n:?})"),
			Self::PtrTo(n) => write!(f, "PtrTo({n:?})"),

			Self::Block {
				looping,
				label,
				body,
			} => write!(f, "Block({label:?}, {looping}) {body:#?}"),
			Self::Jump { label } => write!(f, "Jump({label:#?})"),
			Self::If {
				if_body,
				elseifs: else_if_bodies,
				else_body,
			} => match else_body {
				Some(else_body) => write!(f, "If {if_body:#?} {else_if_bodies:#?} {else_body:#?}"),
				None => write!(f, "If {if_body:#?} {else_if_bodies:#?}"),
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
	Type(TypeDef),
}
impl Def {
	pub fn name(&self) -> &Name {
		match self {
			Self::Func(f) => &f.name,
			Self::Var(v) => &v.name,
			Self::Const(c) => &c.name,
			Self::Data(d) => &d.name,
			Self::Type(t) => &t.name,
		}
	}

	pub fn to_signature(
		&self,
		symbols: &SymbolsTable,
		span: Span,
	) -> error::Result<SymbolSignature> {
		let sig = match self {
			Self::Func(def) => SymbolSignature::Func(def.args.to_signature(symbols)?),
			Self::Var(def) => SymbolSignature::Var(VarSignature {
				typ: def.typ.x.clone().to_type(symbols, span)?,
			}),
			Self::Const(def) => SymbolSignature::Const(ConstSignature {
				typ: def.typ.x.clone().to_type(symbols, span)?,
			}),
			Self::Data(_) => SymbolSignature::Data,
			Self::Type(def) => SymbolSignature::Type(TypeSignature {
				inherits: def.inherits.x.clone().to_type(symbols, span)?,
			}),
		};
		Ok(sig)
	}
}

/// Function arguments
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FuncArgs {
	Vector,
	Proc {
		inputs: Box<[BindedType]>,
		outputs: Box<[BindedType]>,
	},
}
impl FuncArgs {
	pub fn to_signature(&self, symbols: &SymbolsTable) -> error::Result<FuncSignature> {
		match self {
			Self::Vector => Ok(FuncSignature::Vector),
			Self::Proc { inputs, outputs } => Ok(FuncSignature::Proc {
				inputs: inputs
					.iter()
					.map(|t| t.typ.clone().to_type(symbols, t.span))
					.collect::<error::Result<Box<[Type]>>>()?,
				outputs: outputs
					.iter()
					.map(|t| t.typ.clone().to_type(symbols, t.span))
					.collect::<error::Result<Box<[Type]>>>()?,
			}),
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
	pub typ: Spanned<TypeName>,
}

/// Constant definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstDef {
	pub name: Name,
	pub typ: Spanned<TypeName>,
	pub body: Box<[Spanned<Node>]>,
}

/// Data definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataDef {
	pub name: Name,
	pub body: Box<[Spanned<Node>]>,
}

/// Type definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDef {
	pub name: Name,
	pub inherits: Spanned<TypeName>,
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
