use std::{
	borrow::Borrow,
	collections::HashMap,
	fmt::{Debug, Display},
	rc::Rc,
};

use crate::{
	ast::FuncArgs,
	error::{self, Error, SymbolError},
	lexer::{Span, Spanned},
};

/// Unique name of a symbol.
/// Guaranteed to be uuuh, unique?..
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniqueName(pub u32);
impl Debug for UniqueName {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "UniqueName({})", self.0)
	}
}

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

/// Type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
	Byte,
	Short,
	BytePtr(Box<Type>),
	ShortPtr(Box<Type>),
	FuncPtr(FuncSignature),
	Custom { name: Name, size: u16 },
}
impl Type {
	/// Returns whether the two types are the same.
	/// The difference from `==` operator is that this method does not compares the inner types.
	pub fn same_as(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::Byte, Self::Byte) => true,
			(Self::Short, Self::Short) => true,
			(Self::BytePtr(_), Self::BytePtr(_)) => true,
			(Self::ShortPtr(_), Self::ShortPtr(_)) => true,
			(Self::FuncPtr(_), Self::FuncPtr(_)) => true,
			(Self::Custom { name: a, .. }, Self::Custom { name: b, .. }) => a == b,
			_ => false,
		}
	}

	/// Size of the type in bytes
	pub fn size(&self) -> u16 {
		match self {
			Self::Byte => 1,
			Self::Short => 2,
			Self::BytePtr(_) => 1,
			Self::ShortPtr(_) => 2,
			Self::FuncPtr(_) => 2,
			Self::Custom { size, .. } => *size,
		}
	}
}
impl Display for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Byte => write!(f, "byte"),
			Self::Short => write!(f, "short"),
			Self::BytePtr(t) => write!(f, "^{t}"),
			Self::ShortPtr(t) => write!(f, "*{t}"),
			Self::FuncPtr(t) => write!(f, "fun{t}"),
			Self::Custom { name, .. } => write!(f, "{name}"),
		}
	}
}

/// Type with unknown size
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnsizedType {
	Byte,
	Short,
	BytePtr(Box<UnsizedType>),
	ShortPtr(Box<UnsizedType>),
	FuncPtr(FuncArgs),
	Custom(Name),
}
impl UnsizedType {
	pub fn into_sized(self, symbols: &SymbolsTable, span: Span) -> error::Result<Type> {
		match self {
			Self::Byte => Ok(Type::Byte),
			Self::Short => Ok(Type::Short),
			Self::BytePtr(t) => Ok(Type::BytePtr(t.into_sized(symbols, span)?.into())),
			Self::ShortPtr(t) => Ok(Type::ShortPtr(t.into_sized(symbols, span)?.into())),
			Self::FuncPtr(args) => Ok(Type::FuncPtr(args.into_signature(symbols)?)),
			Self::Custom(name) => {
				let typ = symbols.get_type(&name, span)?;
				Ok(Type::Custom {
					name,
					size: typ.inherits.size(),
				})
			}
		}
	}
}

/// Type with a name
#[derive(Debug, Clone, Eq)]
pub struct NamedType<T> {
	pub typ: Spanned<T>,
	pub name: Option<Spanned<Name>>,
	/// Span of the whole node, including type and name
	pub span: Span,
}
impl<T: Display> Display for NamedType<T> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if let Some(name) = &self.name {
			write!(f, "{}:{}", self.typ.x, name.x)
		} else {
			write!(f, "{}", self.typ.x)
		}
	}
}
impl<T: PartialEq> PartialEq for NamedType<T> {
	fn eq(&self, other: &Self) -> bool {
		self.typ == other.typ && self.name == other.name
	}
}

/// Function signature
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FuncSignature {
	Vector,
	Proc {
		inputs: Vec<NamedType<Type>>,
		outputs: Vec<NamedType<Type>>,
	},
}
impl Display for FuncSignature {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Vector => write!(f, "( -> )"),
			Self::Proc { inputs, outputs } => {
				write!(f, "( ")?;
				for input in inputs.iter() {
					write!(f, "{input} ")?;
				}
				write!(f, "-- ")?;
				for output in outputs.iter() {
					write!(f, "{output} ")?;
				}
				write!(f, ")")
			}
		}
	}
}

/// Function symbol
#[derive(Debug, Clone)]
pub struct FuncSymbol {
	pub unique_name: UniqueName,
	pub signature: FuncSignature,
	pub defined_at: Span,
}

/// Variable symbol
#[derive(Debug, Clone)]
pub struct VarSymbol {
	pub unique_name: UniqueName,
	pub typ: Type,
	pub defined_at: Span,
}

/// Constant symbol
#[derive(Debug, Clone)]
pub struct ConstSymbol {
	pub unique_name: UniqueName,
	pub typ: Type,
	pub defined_at: Span,
}

/// Data symbol
#[derive(Debug, Clone)]
pub struct DataSymbol {
	pub unique_name: UniqueName,
	pub defined_at: Span,
}

/// Custom type symbol
#[derive(Debug, Clone)]
pub struct TypeSymbol {
	pub inherits: Type,
	pub defined_at: Span,
}

/// Enum symbol
#[derive(Debug, Clone)]
pub struct EnumSymbol {
	pub inherits: Type,
	pub defined_at: Span,
}

/// Symbol kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
	Func,
	Var,
	Const,
	Data,
	Type,
}
impl SymbolKind {
	/// Returns human-readable representation of this enum in plural form
	pub fn plural(&self) -> &'static str {
		match self {
			Self::Func => "functions",
			Self::Var => "variables",
			Self::Const => "constants",
			Self::Data => "datas",
			Self::Type => "types",
		}
	}
}
impl Display for SymbolKind {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Func => write!(f, "function"),
			Self::Var => write!(f, "variable"),
			Self::Const => write!(f, "constant"),
			Self::Data => write!(f, "data"),
			Self::Type => write!(f, "type"),
		}
	}
}

/// Symbol signature
#[derive(Debug, Clone)]
pub enum Symbol {
	Func(FuncSymbol),
	Var(VarSymbol),
	Const(ConstSymbol),
	Data(DataSymbol),
	Type(TypeSymbol),
}
impl Symbol {
	pub fn kind(&self) -> SymbolKind {
		match self {
			Self::Func(_) => SymbolKind::Func,
			Self::Var(_) => SymbolKind::Var,
			Self::Const(_) => SymbolKind::Const,
			Self::Data(_) => SymbolKind::Data,
			Self::Type(_) => SymbolKind::Type,
		}
	}
	pub fn defined_at(&self) -> Span {
		match self {
			Self::Func(sym) => sym.defined_at,
			Self::Var(sym) => sym.defined_at,
			Self::Const(sym) => sym.defined_at,
			Self::Data(sym) => sym.defined_at,
			Self::Type(sym) => sym.defined_at,
		}
	}
}

fn err_expected_symbol(expected: SymbolKind, defined_at: Span, span: Span) -> Error {
	Error::InvalidSymbol {
		error: SymbolError::Expected { expected },
		defined_at,
		span,
	}
}

/// Symbols table
#[derive(Debug)]
pub struct SymbolsTable {
	pub unique_name_id: u32,
	pub table: HashMap<Name, Symbol>,
}
impl Default for SymbolsTable {
	fn default() -> Self {
		Self {
			unique_name_id: 0,
			table: HashMap::with_capacity(32),
		}
	}
}
impl SymbolsTable {
	#[must_use]
	pub fn new_unique_name(&mut self) -> UniqueName {
		self.unique_name_id += 1;
		UniqueName(self.unique_name_id - 1)
	}

	pub fn define_symbol(&mut self, name: Name, symbol: Symbol) -> error::Result<()> {
		let defined_at = symbol.defined_at();
		let prev = self.table.insert(name, symbol);
		if let Some(prev) = prev {
			// Symbol redefinition occured
			Err(Error::InvalidSymbol {
				error: SymbolError::Redefinition {
					redefined: prev.kind(),
				},
				defined_at: prev.defined_at(),
				span: defined_at,
			})
		} else {
			Ok(())
		}
	}

	pub fn get(&self, name: &Name) -> Option<&Symbol> {
		self.table.get(name)
	}
	pub fn get_func(&self, name: &Name, span: Span) -> error::Result<&FuncSymbol> {
		match self.get(name) {
			Some(Symbol::Func(func)) => Ok(func),
			Some(s) => Err(err_expected_symbol(SymbolKind::Func, s.defined_at(), span)),
			None => Err(Error::UnknownSymbol(span)),
		}
	}
	pub fn get_var(&self, name: &Name, span: Span) -> error::Result<&VarSymbol> {
		match self.get(name) {
			Some(Symbol::Var(var)) => Ok(var),
			Some(s) => Err(err_expected_symbol(SymbolKind::Var, s.defined_at(), span)),
			None => Err(Error::UnknownSymbol(span)),
		}
	}
	pub fn get_const(&self, name: &Name, span: Span) -> error::Result<&ConstSymbol> {
		match self.get(name) {
			Some(Symbol::Const(cnst)) => Ok(cnst),
			Some(s) => Err(err_expected_symbol(SymbolKind::Const, s.defined_at(), span)),
			None => Err(Error::UnknownSymbol(span)),
		}
	}
	pub fn get_data(&self, name: &Name, span: Span) -> error::Result<&DataSymbol> {
		match self.get(name) {
			Some(Symbol::Data(data)) => Ok(data),
			Some(s) => Err(err_expected_symbol(SymbolKind::Data, s.defined_at(), span)),
			None => Err(Error::UnknownSymbol(span)),
		}
	}
	pub fn get_type(&self, name: &Name, span: Span) -> error::Result<&TypeSymbol> {
		match self.get(name) {
			Some(Symbol::Type(typ)) => Ok(typ),
			Some(s) => Err(err_expected_symbol(SymbolKind::Type, s.defined_at(), span)),
			None => Err(Error::UnknownSymbol(span)),
		}
	}

	/// Returns size of the type in bytes
	pub fn type_size(&self, typ: &UnsizedType, span: Span) -> error::Result<u16> {
		match typ {
			UnsizedType::Byte => Ok(1),
			UnsizedType::Short => Ok(2),
			UnsizedType::BytePtr(_) => Ok(1),
			UnsizedType::ShortPtr(_) => Ok(2),
			UnsizedType::FuncPtr(_) => Ok(2),
			UnsizedType::Custom(name) => {
				let typ = self.get_type(name, span)?;
				Ok(typ.inherits.size())
			}
		}
	}
}
