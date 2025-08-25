use crate::{
	lexer::Spanned,
	program::{Intrinsic, IntrinsicMode},
	symbols::{FuncSignature, Name},
	typechecker::Type,
};

/// Node operation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeOp {
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
		body: Box<[Spanned<NodeOp>]>,
	},
	Jump {
		label: Spanned<Name>,
		conditional: bool,
	},

	Bind(Box<[Spanned<Name>]>),
}

/// Symbol definition
#[derive(Debug, Clone)]
pub enum Definition {
	Function(FuncDef),
	Variable(VarDef),
	Constant(ConstDef),
	Data(DataDef),
}

/// Function arguments
#[derive(Debug, Clone)]
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
				inputs: inputs.iter().map(|t| t.0.clone()).collect(),
				outputs: outputs.iter().map(|t| t.0.clone()).collect(),
			},
		}
	}
}

/// Function definition
#[derive(Debug, Clone)]
pub struct FuncDef {
	pub name: Name,
	pub args: FuncArgs,
	pub body: Box<[Spanned<NodeOp>]>,
}

/// Variable definition
#[derive(Debug, Clone)]
pub struct VarDef {
	pub name: Name,
	pub typ: Spanned<Type>,
}

/// Constant definition
#[derive(Debug, Clone)]
pub struct ConstDef {
	pub name: Name,
	pub typ: Spanned<Type>,
	pub body: Box<[Spanned<NodeOp>]>,
}

/// Data definition
#[derive(Debug, Clone)]
pub struct DataDef {
	pub name: Name,
	pub body: Box<[Spanned<NodeOp>]>,
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
	pub definitions: Vec<Spanned<Definition>>,
}
impl Default for Ast {
	fn default() -> Self {
		Self {
			definitions: Vec::with_capacity(128),
		}
	}
}
