use std::{
	borrow::Borrow,
	collections::HashMap,
	fmt::{Debug, Display},
	rc::Rc,
};

use vec1::Vec1;

use crate::{
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
	FuncPtr(FuncSignature<Type>),
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
	FuncPtr(FuncSignature<UnsizedType>),
	Custom(Name),
}
impl UnsizedType {
	pub fn into_sized(self, symbols: &SymbolsTable, span: Span) -> error::Result<Type> {
		match self {
			Self::Byte => Ok(Type::Byte),
			Self::Short => Ok(Type::Short),
			Self::BytePtr(t) => Ok(Type::BytePtr(t.into_sized(symbols, span)?.into())),
			Self::ShortPtr(t) => Ok(Type::ShortPtr(t.into_sized(symbols, span)?.into())),
			Self::FuncPtr(sig) => Ok(Type::FuncPtr(sig.into_sized(symbols)?)),
			Self::Custom(name) => {
				let typ = symbols.get_type(&name, span)?;
				Ok(Type::Custom {
					name,
					size: typ.typ().size(),
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
pub enum FuncSignature<T> {
	Vector,
	Proc {
		inputs: Vec<NamedType<T>>,
		outputs: Vec<NamedType<T>>,
	},
}
impl FuncSignature<UnsizedType> {
	/// Convert into a sized function type signature
	pub fn into_sized(self, symbols: &SymbolsTable) -> error::Result<FuncSignature<Type>> {
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
impl<T: Display> Display for FuncSignature<T> {
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

/// Symbol access
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum SymbolAccess {
	#[default]
	Single,
	Fields(Vec1<Spanned<Name>>),
}

/// Function symbol
#[derive(Debug, Clone)]
pub struct FuncSymbol {
	pub unique_name: UniqueName,
	pub signature: FuncSignature<Type>,
	pub defined_at: Span,
}

/// Variable symbol
#[derive(Debug, Clone)]
pub struct VarSymbol {
	pub unique_name: UniqueName,
	pub typ: Type,
	pub defined_at: Span,
}

/// Constant symbol kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstSymbolKind {
	Normal,
	EnumVariant,
}

/// Constant symbol
#[derive(Debug, Clone)]
pub struct ConstSymbol {
	pub kind: ConstSymbolKind,
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

/// Enum type symbol variant
#[derive(Debug, Clone)]
pub struct EnumSymbolVariant {
	pub symbol: Rc<ConstSymbol>,
}

/// Enum type symbol variant
#[derive(Debug, Clone)]
pub struct StructSymbolField {
	pub offset: u16,
	pub typ: Type,
}

/// Type symbol
#[derive(Debug, Clone)]
pub enum TypeSymbol {
	Normal {
		inherits: Type,
		defined_at: Span,
	},
	Enum {
		typ: Type,
		inherits: Type,
		variants: HashMap<Name, EnumSymbolVariant>,
		defined_at: Span,
	},
	Struct {
		typ: Type,
		fields: HashMap<Name, StructSymbolField>,
		defined_at: Span,
	},
}
impl TypeSymbol {
	pub fn typ(&self) -> &Type {
		match self {
			Self::Normal { inherits, .. } => inherits,
			Self::Enum { typ, .. } | Self::Struct { typ, .. } => typ,
		}
	}
	pub fn defined_at(&self) -> Span {
		match self {
			Self::Normal { defined_at, .. }
			| Self::Enum { defined_at, .. }
			| Self::Struct { defined_at, .. } => *defined_at,
		}
	}
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
	Enum,
	EnumVariant,
	Struct,
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
			Self::Enum => "enums",
			Self::EnumVariant => "enum variants",
			Self::Struct => "structs",
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
			Self::Enum => write!(f, "enum"),
			Self::EnumVariant => write!(f, "enum variant"),
			Self::Struct => write!(f, "structs"),
		}
	}
}

/// Symbol signature
#[derive(Debug, Clone)]
pub enum Symbol {
	Func(Rc<FuncSymbol>),
	Var(Rc<VarSymbol>),
	Const(Rc<ConstSymbol>),
	Data(Rc<DataSymbol>),
	Type(Rc<TypeSymbol>),
}
impl Symbol {
	pub fn kind(&self) -> SymbolKind {
		match self {
			Self::Func(_) => SymbolKind::Func,
			Self::Var(_) => SymbolKind::Var,
			Self::Data(_) => SymbolKind::Data,
			Self::Const(s) => match s.kind {
				ConstSymbolKind::Normal => SymbolKind::Const,
				ConstSymbolKind::EnumVariant => SymbolKind::EnumVariant,
			},
			Self::Type(s) => match s.as_ref() {
				TypeSymbol::Normal { .. } => SymbolKind::Type,
				TypeSymbol::Enum { .. } => SymbolKind::Enum,
				TypeSymbol::Struct { .. } => SymbolKind::Struct,
			},
		}
	}
	pub fn defined_at(&self) -> Span {
		match self {
			Self::Func(sym) => sym.defined_at,
			Self::Var(sym) => sym.defined_at,
			Self::Const(sym) => sym.defined_at,
			Self::Data(sym) => sym.defined_at,
			Self::Type(sym) => sym.defined_at(),
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

	pub fn struct_field_or_single<'a>(
		&'a self,
		typ: &'a Type,
		access: &SymbolAccess,
		span: Span,
	) -> error::Result<(&'a Type, u16)> {
		match access {
			SymbolAccess::Single => Ok((typ, 0)),
			SymbolAccess::Fields(fields) => {
				let field = self.struct_field(typ, fields, span)?;
				Ok((&field.typ, field.offset))
			}
		}
	}

	/// Retrieve a struct field by walking through nested structure types using `fields` path.
	pub fn struct_field(
		&self,
		typ: &Type,
		fields: &Vec1<Spanned<Name>>,
		span: Span,
	) -> error::Result<&StructSymbolField> {
		let mut cur_type = typ;

		let mut cur_field = fields.first();
		let mut fields_iter = fields.iter().skip(1);
		let mut cur_struct_field: &StructSymbolField;

		loop {
			let symbol = match cur_type {
				Type::Custom { name, .. } => self.get_type(name, span)?,
				_ => todo!("'type not a struct at {span}' error"),
			};
			let struct_fields = match symbol {
				TypeSymbol::Struct { fields, .. } => fields,
				_ => todo!("'not a struct as {span}' error"),
			};

			cur_struct_field = struct_fields
				.get(&cur_field.x)
				.ok_or_else(|| todo!("'no such field at {}' error", cur_field.span))?;

			if let Some(field) = fields_iter.next() {
				cur_field = field;
				cur_type = &cur_struct_field.typ;
			} else {
				return Ok(cur_struct_field);
			}
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
				Ok(typ.typ().size())
			}
		}
	}
}
