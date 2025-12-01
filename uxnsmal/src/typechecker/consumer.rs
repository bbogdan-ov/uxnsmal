use std::borrow::Borrow;

use crate::{
	error::{self, Error, StackError},
	lexer::{Span, Spanned},
	symbols::Type,
	typechecker::{ConsumedStackItem, Stack, StackItem, StackMatch},
};

/// Stack consumer
pub struct Consumer<'a> {
	pub stack: &'a mut Stack,

	/// Whether the consumer should clone items instead of popping them from the stack
	pub keep: bool,
	pub keep_cursor: usize,

	/// Number of consumed items by this consumer
	pub consumed_n: usize,
	/// Number of expected items
	pub expected_n: usize,

	pub span: Span,
}
impl<'a> Consumer<'a> {
	pub fn new(stack: &'a mut Stack, span: Span) -> Self {
		Self {
			stack,

			keep: false,
			keep_cursor: 0,
			consumed_n: 0,
			expected_n: 0,

			span,
		}
	}

	pub fn with_keep(mut self, keep: bool) -> Self {
		self.keep = keep;
		self
	}

	pub fn pop(&mut self) -> Option<StackItem> {
		self.expected_n += 1;

		let item = if self.keep {
			if self.keep_cursor < self.stack.len() {
				let idx = self.stack.len() - self.keep_cursor - 1;
				let item = self.stack.items[idx].clone();
				self.keep_cursor += 1;
				item
			} else {
				return None;
			}
		} else {
			self.stack.items.pop()?
		};

		let consumed = ConsumedStackItem::new(item.clone(), self.span);
		self.stack.consumed.push(consumed);
		self.consumed_n += 1;

		Some(item)
	}

	/// Compare types on the stack with types in the array
	pub fn compare<T>(&mut self, signature: &[T], mtch: StackMatch) -> error::Result<()>
	where
		T: Borrow<Type> + PartialEq<StackItem>,
	{
		let stack_len = self.stack.len();
		self.expected_n = signature.len();
		self.consumed_n = self.expected_n;

		let expected = || -> Vec<Type> { signature.iter().map(Borrow::borrow).cloned().collect() };

		if mtch == StackMatch::Exact && self.expected_n < stack_len {
			// Too many items on the stack
			return Err(Error::InvalidStack {
				expected: expected(),
				found: self.stack.items.clone(),
				stack: StackError::TooMany {
					caused_by: self.overflow_caused_by(),
				},
				span: self.span,
			});
		}

		if self.expected_n > stack_len {
			// Too few items on the stack
			return Err(Error::InvalidStack {
				expected: expected(),
				found: self.stack.items.clone(),
				stack: StackError::TooFew {
					consumed_by: self.underflow_caused_by(),
				},
				span: self.span,
			});
		}

		// Check each item on the stack
		for (i, typ) in signature.iter().rev().enumerate() {
			// SAFETY: it is safe to index items because we checked them for exhaustion above
			let item = &self.stack.items[stack_len - 1 - i];

			if *typ != *item {
				return Err(Error::InvalidStack {
					expected: expected(),
					found: self.stack.tail(self.expected_n).to_vec(),
					stack: StackError::Invalid,
					span: self.span,
				});
			}
		}

		if !self.keep {
			// Consume items from the stack
			self.stack.drain(self.expected_n, self.span);
		}

		Ok(())
	}

	/// Items consumed by this consumer
	pub fn consumed(&'a self) -> &'a [ConsumedStackItem] {
		let start = self.stack.consumed.len().saturating_sub(self.consumed_n);
		&self.stack.consumed[start..]
	}

	/// Items consumed by this consumer.
	/// Used for error constructing.
	pub fn found(&self) -> Vec<StackItem> {
		self.consumed().iter().map(|t| t.item.clone()).collect()
	}
	/// Sized of items consumed by this consumer.
	/// Used for error constructing.
	pub fn found_sizes(&self) -> Vec<Spanned<u16>> {
		self.consumed()
			.iter()
			.map(|t| Spanned::new(t.item.typ.size(), t.item.pushed_at))
			.collect()
	}
	/// Spans of operations that caused items exhaustion.
	/// Used for error constructing.
	pub fn underflow_caused_by(&self) -> Vec<Span> {
		let mut spans = Vec::default();

		let mut n = self.expected_n.saturating_sub(self.consumed_n);
		for item in self.stack.consumed.iter().rev() {
			if n == 0 {
				break;
			}
			if item.consumed_at != self.span {
				spans.push(item.consumed_at);
				n -= 1;
			}
		}

		spans
	}
	/// Spans of operations that caused items overflow.
	/// Used for error constructing.
	pub fn overflow_caused_by(&self) -> Vec<Span> {
		self.stack.items[self.expected_n..]
			.iter()
			.rev()
			.map(|t| t.pushed_at)
			.collect()
	}

	/// Returns `StackError` based on how many items were consumed and how many were expected.
	/// Used for error constructing.
	pub fn stack_error(&self) -> StackError {
		if self.expected_n > self.consumed_n {
			StackError::TooFew {
				consumed_by: self.underflow_caused_by(),
			}
		} else {
			StackError::Invalid
		}
	}
}
