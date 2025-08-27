use std::{
	collections::HashMap,
	fmt::{Debug, Display},
	str::FromStr,
};

use crate::{
	ast::Name,
	error::{self, Error, ErrorKind},
	lexer::{Span, Spanned},
	program::Intrinsic,
	typechecker::{Type, UniqueName},
};

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
	Function(UniqueName, FuncSignature),
	Variable(UniqueName, VarSignature),
	Constant(UniqueName, ConstSignature),
	Data(UniqueName, DataSignature),
}
impl Symbol {
	pub fn unique_name(&self) -> &UniqueName {
		match self {
			Self::Function(name, _)
			| Self::Variable(name, _)
			| Self::Constant(name, _)
			| Self::Data(name, _) => name,
		}
	}
}

/// Symbols table
#[derive(Debug, Clone)]
pub struct Label {
	pub unique_name: UniqueName,
	pub depth: usize,
	pub span: Span,
}

/// Symbols table
#[derive(Debug, Clone)]
pub struct SymbolsTable {
	pub table: HashMap<Name, Spanned<Symbol>>,
	/// Block labels available in the current scope
	/// `Spanned(depth, definition_span)`
	pub labels: HashMap<Name, Label>,
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
		self.table.insert(name, Spanned::new(symbol.into(), span));
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
			Err(Error::symbol_redefinition(span, prev_symbol.span))
		} else {
			Ok(())
		}
	}
}
