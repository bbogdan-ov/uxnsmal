use std::{
	borrow::Borrow,
	collections::HashMap,
	fmt::{Debug, Display},
	rc::Rc,
};

use vec1::Vec1;

use crate::{
	bug, err,
	lexer::{Span, Spanned},
	note,
	problem::Problem,
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

pub fn option_name_str(name: Option<&Name>) -> &str {
	match name {
		Some(name) => name.as_ref(),
		None => "_",
	}
}

/// Name of a symbol.
/// May be not an existant symbol name.
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

/// Type.
#[derive(Clone, PartialEq, Eq)]
pub enum Type {
	Byte,
	Short,
	BytePtr(Box<ComplexType>),
	ShortPtr(Box<ComplexType>),
	FuncPtr(FuncSignature<Type>),
	User(Rc<UserTypeSymbol>),
	Enum(Rc<EnumTypeSymbol>),
}
impl Type {
	/// Create a `Type` from a `TypeSymbol`.
	/// Returns `None` if the symbol is structure.
	pub fn from_symbol(symbol: &TypeSymbol) -> Option<Self> {
		match symbol {
			TypeSymbol::User(t) => Some(type_of_user_type(t)),
			TypeSymbol::Enum(t) => Some(type_of_enum(t)),
			TypeSymbol::Struct(_) => None,
		}
	}

	pub fn byte_ptr(t: impl Into<ComplexType>) -> Self {
		Self::BytePtr(Box::new(t.into()))
	}
	pub fn short_ptr(t: impl Into<ComplexType>) -> Self {
		Self::ShortPtr(Box::new(t.into()))
	}

	/// Returns whether the two types are similar.
	/// The difference from `==` operator is that this method does not compare the inner types of
	/// pointers.
	pub fn similar(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::Byte, Self::Byte) => true,
			(Self::Short, Self::Short) => true,
			(Self::BytePtr(_), Self::BytePtr(_)) => true,
			(Self::ShortPtr(_), Self::ShortPtr(_)) => true,
			(Self::FuncPtr(_), Self::FuncPtr(_)) => true,
			(Self::User(a), Self::User(b)) => a == b,
			(Self::Enum(a), Self::Enum(b)) => a == b,
			_ => false,
		}
	}

	/// Size of the type in bytes.
	/// Should never return a value different from 1 or 2.
	pub fn size(&self) -> u16 {
		match self {
			Self::Byte => 1,
			Self::Short => 2,
			Self::BytePtr(_) => 1,
			Self::ShortPtr(_) => 2,
			Self::FuncPtr(_) => 2,
			Self::User(t) => t.inherits.size(),
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
			Self::User(t) => write!(f, "{}", t.name),
			Self::Enum(t) => write!(f, "{}", t.name),
		}
	}
}
impl Debug for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Byte => write!(f, "Byte"),
			Self::Short => write!(f, "Short"),
			Self::BytePtr(t) => write!(f, "BytePtr({t:?})"),
			Self::ShortPtr(t) => write!(f, "*ShortPtr({t:?})"),
			Self::FuncPtr(t) => write!(f, "FuncPtr({t:?})"),
			Self::User(t) => write!(f, "User({:?})", t.name),
			Self::Enum(t) => write!(f, "Enum({:?})", t.name),
		}
	}
}

/// Complex type.
#[derive(Clone, Eq)]
pub enum ComplexType {
	Primitive(Type),
	Struct(Rc<StructTypeSymbol>),
	Array { typ: Box<ComplexType>, count: u16 },
	UnsizedArray { typ: Box<ComplexType> },
}
impl ComplexType {
	pub fn byte_ptr(t: impl Into<ComplexType>) -> Self {
		Self::Primitive(Type::BytePtr(Box::new(t.into())))
	}
	pub fn short_ptr(t: impl Into<ComplexType>) -> Self {
		Self::Primitive(Type::ShortPtr(Box::new(t.into())))
	}
	pub fn func_ptr(signature: FuncSignature<Type>) -> Self {
		Self::Primitive(Type::FuncPtr(signature))
	}
	pub fn array(typ: impl Into<ComplexType>, count: u16) -> Self {
		Self::Array {
			typ: Box::new(typ.into()),
			count,
		}
	}
	pub fn unsized_array(typ: impl Into<ComplexType>) -> Self {
		Self::UnsizedArray {
			typ: Box::new(typ.into()),
		}
	}

	pub fn size(&self) -> u16 {
		match self {
			Self::Primitive(t) => t.size(),
			Self::Struct(t) => t.size,
			Self::Array { typ, count } => typ.size() * count,
			Self::UnsizedArray { .. } => {
				bug!("`ComplexType` must never be `UnsizedArray` outside a pointer type")
			}
		}
	}
	/// Type is either a sized or unsized array.
	pub fn is_array(&self) -> bool {
		matches!(self, Self::Array { .. } | Self::UnsizedArray { .. })
	}
}
impl PartialEq for ComplexType {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::Primitive(a), Self::Primitive(b)) => a == b,
			(Self::Struct(a), Self::Struct(b)) => a == b,
			(Self::Array { typ: a, count: ac }, Self::Array { typ: b, count: bc }) => {
				a == b && ac == bc
			}
			(Self::UnsizedArray { typ: a }, Self::UnsizedArray { typ: b }) => a == b,
			(Self::Array { typ: a, .. }, Self::UnsizedArray { typ: b }) => a == b,
			(Self::UnsizedArray { typ: a }, Self::Array { typ: b, .. }) => a == b,
			_ => false,
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
impl Debug for ComplexType {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Primitive(t) => write!(f, "{t:?}"),
			Self::Struct(t) => write!(f, "Struct({:?})", t.name),
			Self::Array { typ, count } => write!(f, "Array({typ:?}, {count})"),
			Self::UnsizedArray { typ } => write!(f, "UnsizedArray({typ:?})"),
		}
	}
}

/// Type with a name.
#[derive(Debug, Clone, Eq)]
pub struct NamedType<T> {
	pub typ: Spanned<T>,
	pub name: Option<Spanned<Name>>,
	/// Span of the whole node, including type and name.
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

/// Function signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FuncSignature<T> {
	Vector,
	Proc {
		inputs: Vec<NamedType<T>>,
		outputs: Vec<NamedType<T>>,
	},
}
impl<T: Display> Display for FuncSignature<T> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Vector => write!(f, "(->)"),
			Self::Proc { inputs, outputs } => {
				write!(f, "(")?;
				for input in inputs.iter() {
					write!(f, "{input} ")?;
				}
				write!(f, "--")?;
				for output in outputs.iter() {
					write!(f, " {output}")?;
				}
				write!(f, ")")
			}
		}
	}
}

/// Symbol field access.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldAccess {
	pub name: Name,
	/// Trying to access the field as an array.
	pub is_array: bool,
	pub span: Span,
}

/// Symbol access.
#[derive(Debug, Clone)]
pub struct SymbolAccess {
	/// First item is always a symbol name.
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

/// Function symbol.
#[derive(Debug, Clone)]
pub struct FuncSymbol {
	pub name: Name,
	pub unique_name: UniqueName,
	pub signature: FuncSignature<Type>,
	pub defined_at: Span,
}

/// Variable symbol.
#[derive(Debug, Clone)]
pub struct VarSymbol {
	pub name: Name,
	pub unique_name: UniqueName,
	/// Whether the variable should be allocated in the ROM address space.
	pub in_rom: bool,
	pub typ: Spanned<ComplexType>,
	pub defined_at: Span,
}

/// Constant symbol.
#[derive(Debug, Clone)]
pub struct ConstSymbol {
	pub name: Name,
	pub unique_name: UniqueName,
	pub typ: Type,
	pub defined_at: Span,
}

/// Data symbol.
#[derive(Debug, Clone)]
pub struct DataSymbol {
	pub name: Name,
	pub unique_name: UniqueName,
	pub defined_at: Span,
}

/// Struct symbol field.
#[derive(Debug, Clone)]
pub struct StructField {
	pub name: Name,
	pub typ: Spanned<ComplexType>,
	pub offset: u16,
	pub defined_at: Span,
}

/// Enum symbol variant.
#[derive(Debug, Clone)]
pub struct EnumVariant {
	pub name: Name,
	pub unique_name: UniqueName,
	pub defined_at: Span,
}

/// User type symbol.
#[derive(Debug, Clone, Eq)]
pub struct UserTypeSymbol {
	pub name: Name,
	pub inherits: Type,
	pub alias: bool,
	pub defined_at: Span,
}
impl PartialEq for UserTypeSymbol {
	fn eq(&self, other: &Self) -> bool {
		self.name == other.name
	}
}

/// Enum type symbol.
#[derive(Debug, Clone)]
pub struct EnumTypeSymbol {
	pub name: Name,
	pub alias: bool,
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

pub fn type_of_user_type(typ: &Rc<UserTypeSymbol>) -> Type {
	if typ.alias {
		typ.inherits.clone()
	} else {
		Type::User(Rc::clone(typ))
	}
}
pub fn type_of_enum(enm: &Rc<EnumTypeSymbol>) -> Type {
	if enm.alias {
		enm.inherits.clone()
	} else {
		Type::Enum(Rc::clone(enm))
	}
}

/// Struct type symbol.
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

/// Type symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeSymbol {
	User(Rc<UserTypeSymbol>),
	Enum(Rc<EnumTypeSymbol>),
	Struct(Rc<StructTypeSymbol>),
}
impl TypeSymbol {
	pub fn name(&self) -> &Name {
		match self {
			Self::User(t) => &t.name,
			Self::Enum(t) => &t.name,
			Self::Struct(t) => &t.name,
		}
	}
	pub fn defined_at(&self) -> Span {
		match self {
			Self::User(t) => t.defined_at,
			Self::Enum(t) => t.defined_at,
			Self::Struct(t) => t.defined_at,
		}
	}
	pub fn kind(&self) -> SymbolKind {
		match self {
			Self::User(_) => SymbolKind::Type,
			Self::Enum(_) => SymbolKind::Enum,
			Self::Struct(_) => SymbolKind::Struct,
		}
	}
	pub fn size(&self) -> u16 {
		match self {
			Self::User(t) => t.inherits.size(),
			Self::Enum(t) => t.inherits.size(),
			Self::Struct(t) => t.size,
		}
	}
}

/// Symbol kind.
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
	/// Returns human-readable representation of this enum in plural form.
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
			Self::Type => write!(f, "user type"),
			Self::Enum => write!(f, "enum"),
			Self::Struct => write!(f, "struct type"),
		}
	}
}

/// Symbol signature.
#[derive(Debug, Clone)]
pub enum Symbol {
	Func(Rc<FuncSymbol>),
	Var(Rc<VarSymbol>),
	Const(Rc<ConstSymbol>),
	Data(Rc<DataSymbol>),
	Type(TypeSymbol),
}
impl Symbol {
	pub fn name(&self) -> &Name {
		match self {
			Self::Func(s) => &s.name,
			Self::Var(s) => &s.name,
			Self::Data(s) => &s.name,
			Self::Const(s) => &s.name,
			Self::Type(s) => s.name(),
		}
	}
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

/// Found field.
#[derive(Debug)]
pub struct FoundField<'a> {
	pub symbol: &'a Symbol,
	pub field: Option<&'a StructField>,
	pub indexing_type: Option<Spanned<&'a ComplexType>>,
}

/// Resolved symbol access.
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
	Data {
		data: &'a Rc<DataSymbol>,
		indexing: bool,
	},
	Func(&'a Rc<FuncSymbol>),
	Const(&'a Rc<ConstSymbol>),
	Type(&'a Rc<UserTypeSymbol>),
	Struct(&'a Rc<StructTypeSymbol>),
}
impl ResolvedAccess<'_> {
	pub fn kind(&self) -> SymbolKind {
		match self {
			Self::Var { .. } => SymbolKind::Var,
			Self::Enum { .. } => SymbolKind::Enum,
			Self::Data { .. } => SymbolKind::Data,
			Self::Func(_) => SymbolKind::Func,
			Self::Const(_) => SymbolKind::Const,
			Self::Type(_) => SymbolKind::Type,
			Self::Struct(_) => SymbolKind::Struct,
		}
	}
	pub fn defined_at(&self) -> Span {
		match self {
			Self::Var { var, .. } => var.defined_at,
			Self::Enum { enm, .. } => enm.defined_at,
			Self::Data { data, .. } => data.defined_at,
			Self::Func(sym) => sym.defined_at,
			Self::Const(sym) => sym.defined_at,
			Self::Type(sym) => sym.defined_at,
			Self::Struct(sym) => sym.defined_at,
		}
	}
}

/// Symbols table.
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

	pub fn define_symbol(&mut self, name: Name, symbol: Symbol) -> Result<(), Problem> {
		let defined_at = symbol.defined_at();
		if let Some(prev) = self.table.get(&name) {
			let e = err!(defined_at, "redefinition of {} `{name}`", prev.kind());
			let n = note!(prev.defined_at(), "defined here");
			Err(e.with_note(n))
		} else {
			self.table.insert(name, symbol);
			Ok(())
		}
	}

	pub fn get(&self, name: &Name) -> Option<&Symbol> {
		self.table.get(name)
	}
	pub fn try_get(&self, name: &Name, span: Span) -> Result<&Symbol, Problem> {
		match self.get(name) {
			Some(symbol) => Ok(symbol),
			None => Err(err!(span, "unknown symbol `{name}`")),
		}
	}
	pub fn get_type(&self, name: &Name, span: Span) -> Result<&TypeSymbol, Problem> {
		match self.get(name) {
			Some(Symbol::Type(typ)) => Ok(typ),
			Some(s) => {
				let e = err!(span, "`{name}` is not a type but a {}", s.kind());
				let n = note!(s.defined_at(), "defined here");
				Err(e.with_note(n))
			}
			None => Err(err!(span, "unknown type `{name}`")),
		}
	}

	pub fn resolve_access<'a>(
		&'a self,
		access: &SymbolAccess,
		span: Span,
	) -> Result<ResolvedAccess<'a>, Problem> {
		// TODO: refactor this method, i'm not happy with how it looks like.

		use ResolvedAccess as RA;
		use TypeSymbol as TS;

		let first = access.fields.first();
		let symbol = self.try_get(&access.symbol().name, access.symbol().span)?;

		let single = !first.is_array && !access.has_fields();

		match symbol {
			Symbol::Var(sym) => self.resolve_var_access(sym, access, span),
			Symbol::Type(TS::Enum(sym)) if !first.is_array => {
				self.resolve_enum_access(sym, access, span)
			}
			Symbol::Data(data) if !access.has_fields() => Ok(ResolvedAccess::Data {
				data,
				indexing: first.is_array,
			}),

			Symbol::Func(sym) if single => Ok(RA::Func(sym)),
			Symbol::Const(sym) if single => Ok(RA::Const(sym)),
			Symbol::Type(TS::User(t)) if single => Ok(RA::Type(t)),
			Symbol::Type(TS::Struct(t)) if single => Ok(RA::Struct(t)),

			s if access.has_fields() => Err(err!(
				span,
				"expected a variable or enum but got {} `{}`",
				s.kind(),
				s.name()
			)),
			s => Err(err!(
				span,
				"expected a variable or data but got {} `{}`",
				s.kind(),
				s.name()
			)),
		}
	}
	fn resolve_var_access<'a>(
		&'a self,
		var: &'a Rc<VarSymbol>,
		access: &SymbolAccess,
		span: Span,
	) -> Result<ResolvedAccess<'a>, Problem> {
		let mut field = access.fields.first();
		let mut fields_iter = access.fields.iter().skip(1);

		let mut field_type: Spanned<&ComplexType> = Spanned::new(&var.typ.x, var.typ.span);
		let mut field_offset = 0;
		let mut indexing_type: Option<Spanned<&ComplexType>> = None;

		loop {
			if field.is_array {
				if indexing_type.is_some() {
					return Err(err!(span, "no multiple array access yet..."));
				}

				field_type = match &field_type.x {
					ComplexType::Array { typ, .. } | ComplexType::UnsizedArray { typ } => {
						Spanned::new(typ.as_ref(), field_type.span)
					}
					_ => {
						return Err(err!(
							field.span,
							"type of `{}` is `{}` which is not an array",
							field.name,
							field_type.x
						));
					}
				};

				indexing_type = Some(Spanned::new(field_type.x, field.span));
			}

			if let (0, _) = fields_iter.size_hint() {
				break;
			}

			let ComplexType::Struct(struct_type) = &field_type.x else {
				return Err(err!(
					span,
					"typeof `{}` is `{}` which is not a struct",
					var.name,
					field_type.x
				));
			};

			match fields_iter.next() {
				Some(f) => field = f,
				None => break,
			}

			if let Some(f) = struct_type.fields.get(&field.name) {
				field_type = Spanned::new(&f.typ.x, f.typ.span);
				field_offset = f.offset;
			} else {
				return Err(err!(
					span,
					"struct `{}` doesn't have field `{}`",
					struct_type.name,
					field.name
				));
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
		span: Span,
	) -> Result<ResolvedAccess<'a>, Problem> {
		match access.fields.len() {
			2 => (/* ok */),
			0 => unreachable!("`Vec1` is never empty"),
			1 => {
				let e = err!(span, "expected an enum variant");
				let n = note!(enm.defined_at, "defined here");
				return Err(e.with_note(n));
			}
			3.. => return Err(err!(span, "unexpected enum variant field access")),
		}

		let vari = &access.fields[1];

		let Some(variant) = enm.variants.get(&vari.name) else {
			let e = err!(
				vari.span,
				"unknown variant `{}` of enum `{}`",
				vari.name,
				enm.name
			);
			let n = note!(enm.defined_at, "defined here");
			return Err(e.with_note(n));
		};

		Ok(ResolvedAccess::Enum { enm, variant })
	}
}
