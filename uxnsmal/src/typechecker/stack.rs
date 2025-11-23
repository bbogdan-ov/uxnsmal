use std::{borrow::Borrow, fmt::Debug};

use crate::{
	lexer::{Span, Spanned},
	symbols::{Name, Type},
	typechecker::Consumer,
};

/// Stack match
/// How stacks should be compared
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackMatch {
	/// Only tails of the comparable stacks must be equal
	Tail,
	/// Comparable stacks must be exactly the same
	Exact,
}

/// Stack item
#[derive(Clone, Eq)]
pub struct StackItem {
	pub typ: Type,
	pub name: Option<Name>,
	/// Span of the operation that pushed this type onto the stack
	/// Used error reporting
	pub pushed_at: Span,
}
impl StackItem {
	pub fn new(typ: Type, pushed_at: Span) -> Self {
		Self {
			typ,
			name: None,
			pushed_at,
		}
	}
}
impl PartialEq for StackItem {
	fn eq(&self, rhs: &Self) -> bool {
		self.typ == rhs.typ && self.name == rhs.name
	}
}
impl From<(Type, Span)> for StackItem {
	fn from(value: (Type, Span)) -> Self {
		Self::new(value.0, value.1)
	}
}
impl Borrow<Type> for StackItem {
	fn borrow(&self) -> &Type {
		&self.typ
	}
}
impl Debug for StackItem {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "StackItem({:?}, {})", self.typ, self.pushed_at)
	}
}

/// Stack
#[derive(Debug)]
pub struct Stack {
	pub items: Vec<StackItem>,
	/// List of consumed items.
	/// `spanned.span` points to the operation that consumed this item.
	pub consumed: Vec<Spanned<StackItem>>,
}
impl Default for Stack {
	fn default() -> Self {
		Self {
			items: Vec::with_capacity(256),
			consumed: Vec::with_capacity(256),
		}
	}
}
impl Stack {
	pub fn push(&mut self, item: impl Into<StackItem>) {
		// TODO: restrict size of the stack (256 bytes)
		self.items.push(item.into());
	}

	/// Consume N items from the top of the stack
	/// `n` can be larger than number of items in the stack
	pub fn drain(&mut self, n: usize, span: Span) {
		let start = self.len().saturating_sub(n);

		let items = self.items.drain(start..);
		let items = items.map(|t| Spanned::new(t, span));
		self.consumed.extend(items);
	}

	pub fn consumer<'a>(&'a mut self, span: Span) -> Consumer<'a> {
		Consumer::new(self, span)
	}
	pub fn consumer_keep<'a>(&'a mut self, span: Span) -> Consumer<'a> {
		self.consumer(span).with_keep(true)
	}

	pub fn reset(&mut self) {
		self.items.clear();
		self.consumed.clear();
	}

	pub fn len(&self) -> usize {
		self.items.len()
	}
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	// TODO: come up with a better name
	/// Returns spans that point to operations that caused stack exhaustion
	pub fn consumed_by(&self, expected_n: usize) -> Vec<Span> {
		if self.len() >= expected_n {
			return Vec::default();
		}

		let n = expected_n - self.len();
		let start = self.consumed.len().saturating_sub(n);
		self.consumed[start..]
			.iter()
			.map(|t| t.span)
			.rev()
			.collect()
	}
	// TODO: come up with a better name
	/// Returns spans that point to operations that caused stack overflow
	pub fn too_many_items(&self, expected_n: usize) -> Vec<Span> {
		if self.len() <= expected_n {
			return Vec::default();
		}

		let n = self.len() - expected_n;
		let start = self.len().saturating_sub(n);
		self.items[start..]
			.iter()
			.map(|t| t.pushed_at)
			.rev()
			.collect()
	}
}
