use std::{borrow::Borrow, fmt::Debug};

use crate::{
	error::{self, Error},
	lexer::{Span, Spanned},
	symbols::Type,
	typechecker::{Consumer, CurrentSnapshot},
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
	/// Span of the operation that pushed this type onto the stack
	/// Used error reporting
	pub pushed_at: Span,
}
impl StackItem {
	pub fn new(typ: Type, pushed_at: Span) -> Self {
		Self { typ, pushed_at }
	}
}
impl PartialEq for StackItem {
	fn eq(&self, rhs: &Self) -> bool {
		self.typ == rhs.typ
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
	/// List of stack snapshots (copies) taken at each block start.
	/// Used to typecheck blocks.
	pub snapshots: Vec<Vec<StackItem>>,
}
impl Default for Stack {
	fn default() -> Self {
		Self {
			items: Vec::with_capacity(256),
			consumed: Vec::with_capacity(256),
			snapshots: Vec::with_capacity(16),
		}
	}
}
impl Stack {
	pub fn push(&mut self, item: impl Into<StackItem>) {
		// TODO: restrict size of the stack (256 bytes)
		self.items.push(item.into());
	}

	pub fn pop_one(&mut self, keep: bool, span: Span) -> error::Result<StackItem> {
		Consumer::new(self, span)
			.with_keep(keep)
			.with_expected_n(1)
			.pop()
	}
	pub fn consumer<'a>(&'a mut self, span: Span) -> Consumer<'a> {
		Consumer::new(self, span)
	}
	pub fn consumer_keep<'a>(&'a mut self, span: Span) -> Consumer<'a> {
		self.consumer(span).with_keep(true)
	}
	pub fn consumer_n<'a>(&'a mut self, expected_n: usize, keep: bool, span: Span) -> Consumer<'a> {
		self.consumer(span)
			.with_expected_n(expected_n)
			.with_keep(keep)
	}

	#[must_use]
	pub fn take_snapshot(&mut self) -> CurrentSnapshot {
		let snapshot = self.items.clone();
		self.snapshots.push(snapshot);
		CurrentSnapshot
	}
	pub fn compare_snapshot(&mut self, snapshot: CurrentSnapshot, span: Span) -> error::Result<()> {
		let snapshot = self.pop_snapshot(snapshot);
		self.consumer(span)
			.with_keep(true)
			.compare(&snapshot, StackMatch::Exact)
	}
	pub fn pop_snapshot(&mut self, _snapshot: CurrentSnapshot) -> Vec<StackItem> {
		self.snapshots
			.pop()
			.expect("unexpected empty `snapshots` list")
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

	/// Build [`Error::TooFewItems`]
	pub fn error_too_few_items(&mut self, n: usize, span: Span) -> Error {
		let mut consumed_by = Vec::with_capacity(n);

		while consumed_by.len() < n {
			let Some(consumed) = self.consumed.pop() else {
				break;
			};

			if consumed.span != span {
				consumed_by.push(consumed.span);
			}
		}

		Error::TooFewItems { consumed_by, span }
	}
	/// Build [`Error::TooManyItems`]
	pub fn error_too_many_items(&mut self, n: usize, span: Span) -> Error {
		let mut caused_by = Vec::with_capacity(n);

		for _ in 0..self.len().saturating_sub(n) {
			let Some(item) = self.items.pop() else {
				break;
			};
			caused_by.push(item.pushed_at);
		}

		Error::TooManyItems { caused_by, span }
	}
}
