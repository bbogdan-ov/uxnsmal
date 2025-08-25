use std::{
	borrow::Borrow,
	collections::HashMap,
	fmt::{Debug, Display},
	rc::Rc,
	str::FromStr,
};

use crate::{
	error::{self, Error, ErrorKind},
	lexer::{Span, Spanned},
	program::{Intrinsic, Type},
};

/// Name of a symbol
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

/// Data signature
#[derive(Debug, Clone)]
pub struct DataSignature;

/// Symbol
#[derive(Debug, Clone)]
pub enum Symbol {
	Function(FuncSignature),
	Variable(VarSignature),
	Constant(ConstSignature),
	Data(DataSignature),
}
impl From<FuncSignature> for Symbol {
	fn from(value: FuncSignature) -> Self {
		Self::Function(value)
	}
}
impl From<VarSignature> for Symbol {
	fn from(value: VarSignature) -> Self {
		Self::Variable(value)
	}
}
impl From<ConstSignature> for Symbol {
	fn from(value: ConstSignature) -> Self {
		Self::Constant(value)
	}
}
impl From<DataSignature> for Symbol {
	fn from(value: DataSignature) -> Self {
		Self::Data(value)
	}
}

/// Symbols table
#[derive(Debug, Clone)]
pub struct SymbolsTable {
	pub table: HashMap<Name, Spanned<Symbol>>,
	/// Block labels available in the current scope
	/// `Spanned(depth, definition_span)`
	pub labels: HashMap<Name, Spanned<usize>>,
}
impl Default for SymbolsTable {
	fn default() -> Self {
		Self {
			table: HashMap::with_capacity(128),
			labels: HashMap::with_capacity(32),
		}
	}
}
impl SymbolsTable {
	pub fn define(
		&mut self,
		name: Name,
		symbol: impl Into<Symbol>,
		span: Span,
	) -> error::Result<()> {
		self.ensure_not_exists(&name, span)?;
		self.table.insert(name, Spanned(symbol.into(), span));
		Ok(())
	}

	pub fn get(&self, name: impl AsRef<str>) -> Option<&Spanned<Symbol>> {
		self.table.get(name.as_ref())
	}
	pub fn ensure_not_exists(&self, name: impl AsRef<str>, span: Span) -> error::Result<()> {
		if Intrinsic::from_str(name.as_ref()).is_ok() {
			return Err(ErrorKind::NameTakedByIntrinsic.err(span));
		}

		if let Some(prev_symbol) = self.get(name) {
			Err(Error::symbol_redefinition(span, prev_symbol.1))
		} else {
			Ok(())
		}
	}
}
