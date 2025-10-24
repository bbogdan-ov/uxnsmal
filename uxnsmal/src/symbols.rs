use std::{
	borrow::Borrow,
	fmt::{Debug, Display},
	rc::Rc,
};

use crate::lexer::Span;

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
}
impl Type {
	/// Size of the type in bytes
	pub fn size(&self) -> u8 {
		match self {
			Self::Byte => 1,
			Self::Short => 2,
			Self::BytePtr(_) => 1,
			Self::ShortPtr(_) => 2,
			Self::FuncPtr(_) => 2,
		}
	}

	/// Returns whether the type is 2 bytes in size
	pub fn is_short(&self) -> bool {
		matches!(self, Self::Short | Self::ShortPtr(_) | Self::FuncPtr(_))
	}
}
impl Display for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Byte => write!(f, "byte"),
			Self::Short => write!(f, "short"),
			Self::BytePtr(t) => write!(f, "ptr {t}"),
			Self::ShortPtr(t) => write!(f, "ptr2 {t}"),
			Self::FuncPtr(t) => write!(f, "funptr{t}"),
		}
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

/// Symbol signature
#[derive(Debug, Clone)]
pub enum SymbolSignature {
	Func(FuncSignature),
	Var(VarSignature),
	Const(ConstSignature),
	Data,
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

/// Symbol
#[derive(Debug, Clone)]
pub struct Label {
	pub unique_name: UniqueName,
	/// Number of the nested block to which this label is belong to.
	///
	/// # Example
	///
	/// ```plain
	/// fun on-reset ( -> ) { // top-level
	///     @exit { // depth is 0
	///         @a {} // depth is 1
	///         @b {} // depth is 1
	///         @c {  // depth is 1
	///             @d {} // depth is 2
	///         }
	///     }
	/// }
	/// ```
	pub depth: u32,
	/// Location at which this label is defined
	pub span: Span,
}
impl Label {
	pub fn new(unique_name: UniqueName, depth: u32, span: Span) -> Self {
		Self {
			unique_name,
			depth,
			span,
		}
	}
}
