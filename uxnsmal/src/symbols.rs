use std::{
	borrow::Borrow,
	collections::HashMap,
	fmt::{Debug, Display},
	rc::Rc,
};

use crate::{
	ast::{Ast, Node},
	error::{self, Error},
	lexer::Span,
	typechecker::StackItem,
};

/// Unique name of a symbol
/// Guaranteed to be an existant symbol name
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
	User { name: Name, size: u16 },
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
			(Self::User { name: a, .. }, Self::User { name: b, .. }) => a == b,
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
			Self::User { size, .. } => *size,
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
			Self::User { name, .. } => write!(f, "{name}"),
		}
	}
}
impl PartialEq<StackItem> for Type {
	fn eq(&self, rhs: &StackItem) -> bool {
		*self == rhs.typ
	}
}

/// Function signature
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FuncSignature {
	Vector,
	Proc {
		inputs: Box<[Type]>,
		outputs: Box<[Type]>,
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

/// Variable signature
#[derive(Debug, Clone)]
pub struct VarSignature {
	pub typ: Type,
}

/// Constant signature
#[derive(Debug, Clone)]
pub struct ConstSignature {
	pub typ: Type,
}

/// User type signature
#[derive(Debug, Clone)]
pub struct TypeSignature {
	pub inherits: Type,
}

/// Symbol signature
#[derive(Debug, Clone)]
pub enum SymbolSignature {
	Func(FuncSignature),
	Var(VarSignature),
	Const(ConstSignature),
	Data,
	Type(TypeSignature),
}

/// Symbol
#[derive(Debug, Clone)]
pub struct Symbol {
	pub unique_name: UniqueName,
	pub signature: SymbolSignature,
	/// Location at which this symbol is defined
	pub span: Span,
}
impl Symbol {
	pub fn new(unique_name: UniqueName, signature: SymbolSignature, span: Span) -> Self {
		Self {
			unique_name,
			signature,
			span,
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

	/// Walk through AST and collect all top-level symbol definitions
	pub fn collect(&mut self, ast: &Ast) -> error::Result<()> {
		for node in ast.nodes.iter() {
			let node_span = node.span;
			let Node::Def(def) = &node.x else {
				continue;
			};

			let sig = def.to_signature(self, node.span)?;
			self.define_symbol(def.name().clone(), sig, node_span)?;
		}

		Ok(())
	}
	pub fn define_symbol(
		&mut self,
		name: Name,
		signature: SymbolSignature,
		span: Span,
	) -> error::Result<()> {
		let symbol = Symbol::new(self.new_unique_name(), signature, span);
		let prev = self.table.insert(name, symbol);
		if let Some(prev) = prev {
			Err(Error::SymbolRedefinition {
				defined_at: prev.span,
				span,
			})
		} else {
			Ok(())
		}
	}
	/// Get or define a new symbol
	/// Errors only when `signature` returns an error
	pub fn get_or_define_symbol(
		&mut self,
		name: &Name,
		signature: impl FnOnce() -> error::Result<SymbolSignature>,
		span: Span,
	) -> error::Result<&Symbol> {
		if !self.table.contains_key(name) {
			let symbol = Symbol::new(self.new_unique_name(), signature()?, span);
			self.table.insert(name.clone(), symbol);
		}

		// SAFETY: there always will be symbol with name == `name` because if there is not,
		// it will be defined above
		Ok(&self.table[name])
	}

	pub fn get_type(&self, name: &Name, span: Span) -> error::Result<&TypeSignature> {
		match self.table.get(name) {
			Some(symbol) => match &symbol.signature {
				SymbolSignature::Type(sig) => Ok(&sig),
				_ => {
					return Err(Error::NotType {
						defined_at: symbol.span,
						span,
					});
				}
			},
			None => return Err(Error::UnknownType(span)),
		}
	}
}
