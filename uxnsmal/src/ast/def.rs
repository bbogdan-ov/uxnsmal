use std::rc::Rc;

use crate::{
	ast::Node,
	lexer::{Span, Spanned},
	symbols::{
		ConstSymbol, DataSymbol, EnumTypeSymbol, FuncSignature, FuncSymbol, Name, StructTypeSymbol,
		TypeSymbol, UnsizedType, VarSymbol,
	},
};

/// Definition
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

/// Function definition
#[derive(Debug, Clone)]
pub struct FuncDef {
	pub name: Spanned<Name>,
	pub signature: Spanned<FuncSignature<UnsizedType>>,
	pub body: Vec<Node>,
	/// Span of the function header
	/// fun my-func ( -- ) {
	/// ^^^^^^^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition
	pub symbol: Option<Rc<FuncSymbol>>,
}

/// Variable definition
#[derive(Debug, Clone)]
pub struct VarDef {
	pub name: Spanned<Name>,
	pub in_rom: bool,
	pub typ: Spanned<UnsizedType>,
	/// Span of the whole var definition
	pub span: Span,
	/// Symbol associated with this definition
	pub symbol: Option<Rc<VarSymbol>>,
}

/// Constant definition
#[derive(Debug, Clone)]
pub struct ConstDef {
	pub name: Spanned<Name>,
	pub typ: Spanned<UnsizedType>,
	pub body: Vec<Node>,
	/// Span of the const header
	/// const byte MY_CONST {
	/// ^^^^^^^^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition
	pub symbol: Option<Rc<ConstSymbol>>,
}

// TODO: allow define nested data blocks so they can share
// the same data but different parts of it
/// Data definition
#[derive(Debug, Clone)]
pub struct DataDef {
	pub name: Spanned<Name>,
	pub body: Vec<Node>,
	/// Span of the data header
	/// data my-data {
	/// ^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition
	pub symbol: Option<Rc<DataSymbol>>,
}

/// Type definition
#[derive(Debug, Clone)]
pub struct TypeDef {
	pub name: Spanned<Name>,
	pub inherits: Spanned<UnsizedType>,
	/// Span of the whole type definition
	pub span: Span,
	/// Symbol associated with this definition
	pub symbol: Option<Rc<TypeSymbol>>,
}

/// Enum definition variant
#[derive(Debug, Clone)]
pub struct EnumDefVariant {
	pub name: Spanned<Name>,
	pub body: Option<Vec<Node>>,
}

/// Enum definition
#[derive(Debug, Clone)]
pub struct EnumDef {
	pub name: Spanned<Name>,
	pub inherits: Spanned<UnsizedType>,
	pub variants: Vec<EnumDefVariant>,
	pub untyped: bool,
	/// Span of the enum header
	/// enum byte MyEnum {
	/// ^^^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition
	pub symbol: Option<Rc<EnumTypeSymbol>>,
}

/// Structure definition field
#[derive(Debug, Clone)]
pub struct StructDefField {
	pub typ: Spanned<UnsizedType>,
	pub name: Spanned<Name>,
	pub span: Span,
}

/// Structure definition
#[derive(Debug, Clone)]
pub struct StructDef {
	pub name: Spanned<Name>,
	pub fields: Vec<StructDefField>,
	/// Span of the struct header
	/// struct MyStruct {
	/// ^^^^^^^^^^^^^^^
	pub span: Span,
	/// Symbol associated with this definition
	pub symbol: Option<Rc<StructTypeSymbol>>,
}
