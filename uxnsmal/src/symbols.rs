use std::{
	borrow::Borrow,
	collections::HashMap,
	fmt::{Debug, Display},
	rc::Rc,
};

use crate::{
	ast::FuncArgs,
	error::{self, Error},
	lexer::Span,
	typechecker::StackItem,
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
impl PartialEq<StackItem> for Type {
	fn eq(&self, rhs: &StackItem) -> bool {
		*self == rhs.typ
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

/// Function signature
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FuncSignature {
	Vector,
	Proc {
		inputs: Vec<Type>,
		outputs: Vec<Type>,
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
			Err(Error::SymbolRedefinition {
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
			Some(_) => todo!("'not a function' error"),
			None => Err(Error::UnknownSymbol(span)),
		}
	}
	pub fn get_var(&self, name: &Name, span: Span) -> error::Result<&VarSymbol> {
		match self.get(name) {
			Some(Symbol::Var(var)) => Ok(var),
			Some(_) => todo!("'not a var' error"),
			None => Err(Error::UnknownSymbol(span)),
		}
	}
	pub fn get_const(&self, name: &Name, span: Span) -> error::Result<&ConstSymbol> {
		match self.get(name) {
			Some(Symbol::Const(cnst)) => Ok(cnst),
			Some(_) => todo!("'not a constant' error"),
			None => Err(Error::UnknownSymbol(span)),
		}
	}
	pub fn get_data(&self, name: &Name, span: Span) -> error::Result<&DataSymbol> {
		match self.get(name) {
			Some(Symbol::Data(data)) => Ok(data),
			Some(_) => todo!("'not a data' error"),
			None => Err(Error::UnknownSymbol(span)),
		}
	}
	pub fn get_type(&self, name: &Name, span: Span) -> error::Result<&TypeSymbol> {
		match self.get(name) {
			Some(Symbol::Type(typ)) => Ok(typ),
			Some(_) => todo!("'not a type' error"),
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
