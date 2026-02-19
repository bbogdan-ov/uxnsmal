use std::{
	borrow::Borrow,
	fmt::{Debug, Display},
};

use crate::{
	lexer::Span,
	symbol::{Name, Type},
};

/// Stack item.
#[derive(Debug, Clone, Eq)]
pub struct Item {
	pub typ: Type,
	pub name: Option<Name>,
	/// Span of the operation that pushed this item onto the stack.
	/// Used for error reporting.
	pub pushed_at: Span,
}
impl Item {
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
impl PartialEq for Item {
	fn eq(&self, rhs: &Self) -> bool {
		self.typ == rhs.typ && self.name == rhs.name
	}
}
impl Borrow<Type> for Item {
	fn borrow(&self) -> &Type {
		&self.typ
	}
}
impl PartialEq<Type> for Item {
	fn eq(&self, rhs: &Type) -> bool {
		self.typ == *rhs
	}
}
impl Display for Item {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self.name {
			Some(name) => write!(f, "{}:{}", self.typ, name),
			None => write!(f, "{}", self.typ),
		}
	}
}

/// Consumed stack item.
#[derive(Debug, Clone, Eq)]
pub struct ConsumedItem {
	pub item: Item,
	/// Span of the operation that consumed this item from a stack.
	/// Used for error reporting.
	pub consumed_at: Span,
}
impl ConsumedItem {
	pub fn new(item: Item, consumed_at: Span) -> Self {
		Self { item, consumed_at }
	}
}
impl PartialEq for ConsumedItem {
	fn eq(&self, rhs: &Self) -> bool {
		self.item == rhs.item
	}
}

/// Stack.
#[derive(Debug)]
pub struct Stack {
	pub items: Vec<Item>,
	/// List of consumed items.
	/// `spanned.span` points to the operation that consumed this item.
	pub consumed: Vec<ConsumedItem>,

	/// Whether "keep" mode is enabled.
	/// If `true` items will not be consumed when popping.
	pub keep: bool,
	/// Index from the end of an item to be cloned with "keep" mode.
	keep_cursor: usize,
}
impl Default for Stack {
	fn default() -> Self {
		Self::new(Vec::with_capacity(256))
	}
}
impl Stack {
	pub fn new(items: Vec<Item>) -> Self {
		Self {
			items,
			consumed: Vec::with_capacity(256),

			keep: false,
			keep_cursor: 0,
		}
	}

	pub fn push(&mut self, item: Item) {
		// TODO: restrict size of the stack (256 bytes).
		self.items.push(item);
	}

	/// Pop a single item from the top of the stack.
	pub fn pop(&mut self, span: Span) -> Option<Item> {
		let item = if self.keep {
			if self.keep_cursor < self.len() {
				let idx = self.len() - self.keep_cursor - 1;
				let item = self.items[idx].clone();
				self.keep_cursor += 1;
				item
			} else {
				return None;
			}
		} else {
			self.items.pop()?
		};

		let consumed = ConsumedItem::new(item.clone(), span);
		self.consumed.push(consumed);

		Some(item)
	}
	/// Consume N items from the top of the stack.
	/// `n` can be larger than number of items in the stack.
	pub fn drain(&mut self, n: usize, span: Span) {
		let start = self.len().saturating_sub(n);

		let items = self
			.items
			.drain(start..)
			.map(|t| ConsumedItem::new(t, span));
		self.consumed.extend(items);
	}
	/// Slice of the last N items.
	pub fn tail(&mut self, n: usize) -> &[Item] {
		if n >= self.len() {
			&self.items
		} else {
			&self.items[self.len() - n..]
		}
	}

	pub fn reset(&mut self) {
		self.items.clear();
		self.consumed.clear();
		self.reset_keep();
	}
	pub fn reset_keep(&mut self) {
		self.keep = false;
		self.keep_cursor = 0;
	}

	pub fn len(&self) -> usize {
		self.items.len()
	}
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}
}
