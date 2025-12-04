use crate::{
	ast::Node,
	error,
	lexer::{Span, Spanned},
	symbols::{FuncSignature, Name, NamedType, SymbolsTable, Type, UnsizedType},
};

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
			Self::Func(f) => &f.name.x,
			Self::Var(v) => &v.name.x,
			Self::Const(c) => &c.name.x,
			Self::Data(d) => &d.name.x,
			Self::Type(t) => &t.name.x,
		}
	}
	pub fn span(&self) -> Span {
		match self {
			Self::Func(f) => f.span,
			Self::Var(v) => v.span,
			Self::Const(c) => c.span,
			Self::Data(d) => d.span,
			Self::Type(t) => t.span,
		}
	}
}

/// Function arguments
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FuncArgs {
	Vector {
		span: Span,
	},
	Proc {
		inputs: Vec<NamedType<UnsizedType>>,
		outputs: Vec<NamedType<UnsizedType>>,
		span: Span,
	},
}
impl FuncArgs {
	pub fn span(&self) -> Span {
		match self {
			Self::Vector { span } | Self::Proc { span, .. } => *span,
		}
	}

	/// Convert into function type signature
	pub fn into_signature(self, symbols: &SymbolsTable) -> error::Result<FuncSignature> {
		type R = error::Result<Vec<NamedType<Type>>>;

		let map = |t: NamedType<UnsizedType>| -> error::Result<NamedType<Type>> {
			Ok(NamedType {
				typ: Spanned::new(t.typ.x.into_sized(symbols, t.typ.span)?, t.typ.span),
				name: t.name,
				span: t.span,
			})
		};

		match self {
			Self::Vector { .. } => Ok(FuncSignature::Vector),
			Self::Proc {
				inputs, outputs, ..
			} => Ok(FuncSignature::Proc {
				inputs: inputs.into_iter().map(map).collect::<R>()?,
				outputs: outputs.into_iter().map(map).collect::<R>()?,
			}),
		}
	}
}

/// Function definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncDef {
	pub name: Spanned<Name>,
	pub args: FuncArgs,
	pub body: Vec<Node>,
	/// Span of the function header
	/// fun my-func ( -- ) {
	/// ^^^^^^^^^^^^^^^^^^^^
	pub span: Span,
}

/// Variable definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDef {
	pub name: Spanned<Name>,
	pub typ: Spanned<UnsizedType>,
	/// Span of the whole var definition
	pub span: Span,
}

/// Constant definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstDef {
	pub name: Spanned<Name>,
	pub typ: Spanned<UnsizedType>,
	pub body: Vec<Node>,
	/// Span of the const header
	/// const byte MY_CONST {
	/// ^^^^^^^^^^^^^^^^^^^^^
	pub span: Span,
}

/// Data definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataDef {
	pub name: Spanned<Name>,
	pub body: Vec<Node>,
	/// Span of the data header
	/// data my-data {
	/// ^^^^^^^^^^^^^^
	pub span: Span,
}

/// Type definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDef {
	pub name: Spanned<Name>,
	pub inherits: Spanned<UnsizedType>,
	/// Span of the whole type definition
	pub span: Span,
}
