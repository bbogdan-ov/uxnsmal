use std::{
	borrow::Borrow,
	fmt::{Debug, Display},
};

use crate::{
	lexer::Span,
	symbols::{Name, Type},
	typechecker::Consumer,
};

/// Convenience function, returns an empty iterator of `StackItem`s
pub fn empty_stack<'a>() -> std::iter::Empty<&'a StackItem> {
	std::iter::empty::<&StackItem>()
}

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
#[derive(Debug, Clone, Eq)]
pub struct StackItem {
	pub typ: Type,
	pub name: Option<Name>,
	/// Span of the operation that pushed this item onto the stack
	/// Used for error reporting
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
	pub fn named(typ: Type, name: Option<Name>, pushed_at: Span) -> Self {
		Self {
			typ,
			name,
			pushed_at,
		}
	}
}
impl PartialEq for StackItem {
	fn eq(&self, rhs: &Self) -> bool {
		self.typ == rhs.typ && self.name == rhs.name
	}
}
impl Borrow<Type> for StackItem {
	fn borrow(&self) -> &Type {
		&self.typ
	}
}
impl PartialEq<Type> for StackItem {
	fn eq(&self, rhs: &Type) -> bool {
		self.typ == *rhs
	}
}
impl Display for StackItem {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self.name {
			Some(name) => write!(f, "{}:{}", self.typ, name),
			None => write!(f, "{}", self.typ),
		}
	}
}

/// Consumed stack item
#[derive(Debug, Clone, Eq)]
pub struct ConsumedStackItem {
	pub item: StackItem,
	/// Span of the operation that consumed this type from the stack
	/// Used for error reporting
	pub consumed_at: Span,
}
impl ConsumedStackItem {
	pub fn new(item: StackItem, consumed_at: Span) -> Self {
		Self { item, consumed_at }
	}
}
impl PartialEq for ConsumedStackItem {
	fn eq(&self, rhs: &Self) -> bool {
		self.item == rhs.item
	}
}

/// Stack
#[derive(Debug)]
pub struct Stack {
	pub items: Vec<StackItem>,
	/// List of consumed items.
	/// `spanned.span` points to the operation that consumed this item.
	pub consumed: Vec<ConsumedStackItem>,
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
	pub fn push(&mut self, item: StackItem) {
		// TODO: restrict size of the stack (256 bytes)
		self.items.push(item.into());
	}

	/// Pop a single item from the top of the stack
	pub fn pop(&mut self, span: Span) -> Option<StackItem> {
		let item = self.items.pop()?;
		let consumed = ConsumedStackItem::new(item.clone(), span);
		self.consumed.push(consumed);
		Some(item)
	}
	/// Consume N items from the top of the stack
	/// `n` can be larger than number of items in the stack
	pub fn drain(&mut self, n: usize, span: Span) {
		let start = self.len().saturating_sub(n);

		let items = self
			.items
			.drain(start..)
			.map(|t| ConsumedStackItem::new(t, span));
		self.consumed.extend(items);
	}
	/// Slice of the last N items
	pub fn tail(&mut self, n: usize) -> &[StackItem] {
		if n >= self.len() {
			&self.items
		} else {
			&self.items[self.len() - n..]
		}
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
}
