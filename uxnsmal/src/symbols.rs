use std::{
	borrow::Borrow,
	collections::HashMap,
	fmt::{Debug, Display},
	rc::Rc,
};

use vec1::Vec1;

use crate::{
	error::{self, Error, SymbolError, TypeError},
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
	BytePtr(Box<ComplexType>),
	ShortPtr(Box<ComplexType>),
	FuncPtr(FuncSignature<Type>),
	Custom(Rc<CustomTypeSymbol>),
	Enum(Rc<EnumTypeSymbol>),
}
impl Type {
	pub fn from_symbol(symbol: &TypeSymbol, span: Span) -> error::Result<Self> {
		match symbol {
			TypeSymbol::Normal(t) => Ok(Self::Custom(Rc::clone(t))),
			TypeSymbol::Enum(t) => match t.untyped {
				true => Ok(t.inherits.clone()),
				false => Ok(Self::Enum(Rc::clone(t))),
			},
			TypeSymbol::Struct(t) => Err(Error::InvalidType {
				error: TypeError::IllegalStruct {
					defined_at: t.defined_at,
				},
				span,
			}),
		}
	}

	pub fn byte_ptr(t: impl Into<ComplexType>) -> Self {
		Self::BytePtr(Box::new(t.into()))
	}
	pub fn short_ptr(t: impl Into<ComplexType>) -> Self {
		Self::ShortPtr(Box::new(t.into()))
	}

	/// Returns whether the two types are the same.
	/// The difference from `==` operator is that this method does not compares the inner types.
	pub fn same_as(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::Byte, Self::Byte) => true,
			(Self::Short, Self::Short) => true,
			(Self::BytePtr(_), Self::BytePtr(_)) => true,
			(Self::ShortPtr(_), Self::ShortPtr(_)) => true,
			(Self::FuncPtr(_), Self::FuncPtr(_)) => true,
			(Self::Custom(a), Self::Custom(b)) => a == b,
			(Self::Enum(a), Self::Enum(b)) => a == b,
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
			Self::Custom(t) => t.inherits.size(),
			Self::Enum(t) => t.inherits.size(),
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
			Self::Custom(t) => write!(f, "{}", t.name),
			Self::Enum(t) => write!(f, "{}", t.name),
		}
	}
}

/// Complex type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComplexType {
	Primitive(Type),
	Struct(Rc<StructTypeSymbol>),
	Array { typ: Box<ComplexType>, count: u16 },
	UnsizedArray { typ: Box<ComplexType> },
}
impl ComplexType {
	pub fn size(&self, span: Span) -> error::Result<u16> {
		match self {
			Self::Primitive(t) => Ok(t.size()),
			Self::Struct(t) => Ok(t.size),
			Self::Array { typ, count } => Ok(typ.size(span)? * count),
			Self::UnsizedArray { .. } => Err(Error::InvalidType {
				error: TypeError::UnknownArraySize,
				span,
			}),
		}
	}
	/// Type is either a sized or unsized array
	pub fn is_array(&self) -> bool {
		matches!(self, Self::Array { .. } | Self::UnsizedArray { .. })
	}

	/// Get primitive type.
	/// Returns an error if this complex type is not a primitive one!!!
	pub fn primitive(&self, span: Span) -> error::Result<&Type> {
		match self {
			Self::Primitive(t) => Ok(t),
			Self::Struct(t) => Err(Error::InvalidType {
				error: TypeError::IllegalStruct {
					defined_at: t.defined_at,
				},
				span,
			}),
			Self::Array { .. } | Self::UnsizedArray { .. } => Err(Error::InvalidType {
				error: TypeError::IllegalArray,
				span,
			}),
		}
	}
}
impl From<Type> for ComplexType {
	fn from(value: Type) -> Self {
		Self::Primitive(value)
	}
}
impl Display for ComplexType {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Primitive(t) => write!(f, "{t}"),
			Self::Struct(t) => write!(f, "{}", t.name),
			Self::Array { typ, count } => write!(f, "[{count}]{typ}"),
			Self::UnsizedArray { typ } => write!(f, "[]{typ}"),
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
	/// Either custom type, enum, struct, etc
	Type(Name),
	Array {
		typ: Box<UnsizedType>,
		count: u16,
	},
	UnsizedArray {
		typ: Box<UnsizedType>,
	},
}
impl UnsizedType {
	pub fn into_sized(self, symbols: &SymbolsTable, span: Span) -> error::Result<Type> {
		match self {
			Self::Byte => Ok(Type::Byte),
			Self::Short => Ok(Type::Short),
			Self::BytePtr(t) => Ok(Type::BytePtr(t.into_complex_sized(symbols, span)?.into())),
			Self::ShortPtr(t) => Ok(Type::ShortPtr(t.into_complex_sized(symbols, span)?.into())),
			Self::FuncPtr(sig) => Ok(Type::FuncPtr(sig.into_sized(symbols)?).into()),
			Self::Type(name) => {
				let typ = symbols.get_type(&name, span)?;
				Ok(Type::from_symbol(typ, span)?)
			}
			Self::Array { .. } | Self::UnsizedArray { .. } => Err(Error::InvalidType {
				error: TypeError::IllegalArray,
				span,
			}),
		}
	}
	pub fn into_complex_sized(
		self,
		symbols: &SymbolsTable,
		span: Span,
	) -> error::Result<ComplexType> {
		match self {
			Self::Byte => Ok(Type::Byte.into()),
			Self::Short => Ok(Type::Short.into()),
			Self::BytePtr(t) => {
				Ok(Type::BytePtr(t.into_complex_sized(symbols, span)?.into()).into())
			}
			Self::ShortPtr(t) => {
				Ok(Type::ShortPtr(t.into_complex_sized(symbols, span)?.into()).into())
			}
			Self::FuncPtr(sig) => Ok(Type::FuncPtr(sig.into_sized(symbols)?).into()),
			Self::Type(name) => {
				let typ = symbols.get_type(&name, span)?;
				match typ {
					TypeSymbol::Normal(t) => Ok(Type::Custom(Rc::clone(t)).into()),
					TypeSymbol::Enum(t) => Ok(enum_type(t).into()),
					TypeSymbol::Struct(t) => Ok(ComplexType::Struct(Rc::clone(t))),
				}
			}
			Self::Array { typ, count } => Ok(ComplexType::Array {
				typ: typ.into_complex_sized(symbols, span)?.into(),
				count,
			}),
			Self::UnsizedArray { typ } => Ok(ComplexType::UnsizedArray {
				typ: typ.into_complex_sized(symbols, span)?.into(),
			}),
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

/// Symbol field access
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldAccess {
	pub name: Name,
	/// Trying to access the field as an array
	pub is_array: bool,
	pub span: Span,
}

/// Symbol access
#[derive(Debug, Clone)]
pub struct SymbolAccess {
	/// First item is always a symbol name
	pub fields: Vec1<FieldAccess>,
}
impl SymbolAccess {
	pub fn symbol(&self) -> &FieldAccess {
		self.fields.first()
	}
	pub fn has_fields(&self) -> bool {
		self.fields.len() > 1
	}
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
	pub typ: Spanned<ComplexType>,
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

/// Struct symbol field
#[derive(Debug, Clone)]
pub struct StructField {
	pub typ: Spanned<ComplexType>,
	pub offset: u16,
	pub defined_at: Span,
}

/// Enum symbol variant
#[derive(Debug, Clone)]
pub struct EnumVariant {
	pub name: Name,
	pub unique_name: UniqueName,
	pub defined_at: Span,
}

/// Normal type symbol
#[derive(Debug, Clone, Eq)]
pub struct CustomTypeSymbol {
	pub name: Name,
	pub inherits: Type,
	pub defined_at: Span,
}
impl PartialEq for CustomTypeSymbol {
	fn eq(&self, other: &Self) -> bool {
		self.name == other.name
	}
}

pub fn enum_type(enm: &Rc<EnumTypeSymbol>) -> Type {
	if enm.untyped {
		enm.inherits.clone()
	} else {
		Type::Enum(Rc::clone(enm))
	}
}

/// Enum type symbol
#[derive(Debug, Clone)]
pub struct EnumTypeSymbol {
	pub name: Name,
	pub untyped: bool,
	pub inherits: Type,
	pub variants: HashMap<Name, EnumVariant>,
	pub defined_at: Span,
}
impl Eq for EnumTypeSymbol {}
impl PartialEq for EnumTypeSymbol {
	fn eq(&self, other: &Self) -> bool {
		self.name == other.name
	}
}

/// Struct type symbol
#[derive(Debug, Clone)]
pub struct StructTypeSymbol {
	pub name: Name,
	pub fields: HashMap<Name, StructField>,
	pub size: u16,
	pub defined_at: Span,
}
impl Eq for StructTypeSymbol {}
impl PartialEq for StructTypeSymbol {
	fn eq(&self, other: &Self) -> bool {
		self.name == other.name
	}
}

/// Type symbol
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeSymbol {
	Normal(Rc<CustomTypeSymbol>),
	Enum(Rc<EnumTypeSymbol>),
	Struct(Rc<StructTypeSymbol>),
}
impl TypeSymbol {
	pub fn name(&self) -> &Name {
		match self {
			Self::Normal(t) => &t.name,
			Self::Enum(t) => &t.name,
			Self::Struct(t) => &t.name,
		}
	}
	pub fn defined_at(&self) -> Span {
		match self {
			Self::Normal(t) => t.defined_at,
			Self::Enum(t) => t.defined_at,
			Self::Struct(t) => t.defined_at,
		}
	}
	pub fn kind(&self) -> SymbolKind {
		match self {
			Self::Normal(_) => SymbolKind::Type,
			Self::Enum(_) => SymbolKind::Enum,
			Self::Struct(_) => SymbolKind::Struct,
		}
	}
	pub fn size(&self) -> u16 {
		match self {
			Self::Normal(t) => t.inherits.size(),
			Self::Enum(t) => t.inherits.size(),
			Self::Struct(t) => t.size,
		}
	}
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
	Type(TypeSymbol),
}
impl Symbol {
	pub fn kind(&self) -> SymbolKind {
		match self {
			Self::Func(_) => SymbolKind::Func,
			Self::Var(_) => SymbolKind::Var,
			Self::Data(_) => SymbolKind::Data,
			Self::Const(_) => SymbolKind::Const,
			Self::Type(s) => s.kind(),
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

/// Found field
#[derive(Debug)]
pub struct FoundField<'a> {
	pub symbol: &'a Symbol,
	pub field: Option<&'a StructField>,
	pub indexing_type: Option<Spanned<&'a ComplexType>>,
}

/// Resolved symbol access
#[derive(Debug)]
pub enum ResolvedAccess<'a> {
	Var {
		var: &'a Rc<VarSymbol>,
		field_type: Spanned<&'a ComplexType>,
		field_offset: u16,
		indexing_type: Option<Spanned<&'a ComplexType>>,
	},
	Enum {
		enm: &'a Rc<EnumTypeSymbol>,
		variant: &'a EnumVariant,
	},
	Func(&'a Rc<FuncSymbol>),
	Const(&'a Rc<ConstSymbol>),
	Data(&'a Rc<DataSymbol>),
	Type(&'a Rc<CustomTypeSymbol>),
	Struct(&'a Rc<StructTypeSymbol>),
}
impl ResolvedAccess<'_> {
	pub fn kind(&self) -> SymbolKind {
		match self {
			Self::Var { .. } => SymbolKind::Var,
			Self::Enum { .. } => SymbolKind::Enum,
			Self::Func(_) => SymbolKind::Func,
			Self::Const(_) => SymbolKind::Const,
			Self::Data(_) => SymbolKind::Data,
			Self::Type(_) => SymbolKind::Type,
			Self::Struct(_) => SymbolKind::Struct,
		}
	}
	pub fn defined_at(&self) -> Span {
		match self {
			Self::Var { var, .. } => var.defined_at,
			Self::Enum { enm, .. } => enm.defined_at,
			Self::Func(sym) => sym.defined_at,
			Self::Const(sym) => sym.defined_at,
			Self::Data(sym) => sym.defined_at,
			Self::Type(sym) => sym.defined_at,
			Self::Struct(sym) => sym.defined_at,
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
	pub fn try_get(&self, name: &Name, span: Span) -> error::Result<&Symbol> {
		match self.get(name) {
			Some(symbol) => Ok(symbol),
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

	pub fn resolve_access<'a>(
		&'a self,
		access: &SymbolAccess,
		span: Span,
	) -> error::Result<ResolvedAccess<'a>> {
		use ResolvedAccess as RA;
		use TypeSymbol as TS;

		let first = access.fields.first();
		let symbol = self.try_get(&access.symbol().name, access.symbol().span)?;

		let single = !first.is_array && !access.has_fields();

		match symbol {
			Symbol::Var(sym) => self.resolve_var_access(sym, access, span),
			Symbol::Type(TS::Enum(enm)) if !first.is_array => {
				self.resolve_enum_access(enm, access, span)
			}

			Symbol::Func(sym) if single => Ok(RA::Func(sym)),
			Symbol::Const(sym) if single => Ok(RA::Const(sym)),
			Symbol::Data(sym) if single => Ok(RA::Data(sym)),
			Symbol::Type(TS::Normal(t)) if single => Ok(RA::Type(t)),
			Symbol::Type(TS::Struct(t)) if single => Ok(RA::Struct(t)),

			_ if access.has_fields() => Err(Error::InvalidType {
				error: TypeError::SymbolsNotStructs {
					kind: symbol.kind(),
					defined_at: symbol.defined_at(),
				},
				span: first.span,
			}),
			_ => Err(Error::InvalidType {
				error: TypeError::SymbolsNotArrays {
					kind: symbol.kind(),
					defined_at: symbol.defined_at(),
				},
				span: first.span,
			}),
		}
	}
	fn resolve_var_access<'a>(
		&'a self,
		var: &'a Rc<VarSymbol>,
		access: &SymbolAccess,
		span: Span,
	) -> error::Result<ResolvedAccess<'a>> {
		let mut field = access.fields.first();
		let mut fields_iter = access.fields.iter().skip(1);

		let mut field_type: Spanned<&ComplexType> = Spanned::new(&var.typ.x, var.typ.span);
		let mut field_offset = 0;
		let mut indexing_type: Option<Spanned<&ComplexType>> = None;

		loop {
			if field.is_array {
				if indexing_type.is_some() {
					return Err(Error::NoMutltipleArraysAccessYet(span));
				}

				field_type = match &field_type.x {
					ComplexType::Array { typ, .. } | ComplexType::UnsizedArray { typ } => {
						Spanned::new(typ.as_ref(), field_type.span)
					}
					_ => {
						return Err(Error::InvalidType {
							error: TypeError::NotArray {
								defined_at: field_type.span,
							},
							span: field.span,
						});
					}
				};

				indexing_type = Some(Spanned::new(&field_type.x, field.span));
			}

			if let (0, _) = fields_iter.size_hint() {
				break;
			}

			let ComplexType::Struct(struct_type) = &field_type.x else {
				return Err(Error::InvalidType {
					error: TypeError::NotStruct {
						defined_at: field_type.span,
					},
					span: field.span,
				});
			};

			match fields_iter.next() {
				Some(f) => field = f,
				None => break,
			}

			if let Some(f) = struct_type.fields.get(&field.name) {
				field_type = Spanned::new(&f.typ.x, f.typ.span);
				field_offset = f.offset;
			} else {
				return Err(Error::InvalidType {
					error: TypeError::UnknownField {
						defined_at: struct_type.defined_at,
					},
					span: field.span,
				});
			}
		}

		Ok(ResolvedAccess::Var {
			var,
			field_type,
			field_offset,
			indexing_type,
		})
	}
	fn resolve_enum_access<'a>(
		&'a self,
		enm: &'a Rc<EnumTypeSymbol>,
		access: &SymbolAccess,
		_span: Span,
	) -> error::Result<ResolvedAccess<'a>> {
		match access.fields.len() {
			2 => (/* ok */),
			0 => unreachable!("`Vec1` is never empty"),
			1 => todo!("'cannot use enum by itself' erro"),
			3.. => todo!("'too many variants' error"),
		}

		let vari_name = &access.fields[1];

		let Some(variant) = enm.variants.get(&vari_name.name) else {
			todo!("'no such variant' error");
		};

		Ok(ResolvedAccess::Enum { enm, variant })
	}
}
