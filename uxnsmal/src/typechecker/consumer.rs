use std::borrow::Borrow;

use crate::{
	error::{self, Error, StackError},
	lexer::{Span, Spanned},
	symbols::Type,
	typechecker::{Stack, StackItem, StackMatch},
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

		let consumed = Spanned::new(item.clone(), self.span);
		self.stack.consumed.push(consumed);
		self.consumed_n += 1;

		Some(item)
	}

	/// Compare types in the stack with types in the iterator
	pub fn compare<T>(&mut self, signature: &[T], mtch: StackMatch) -> error::Result<()>
	where
		T: Borrow<Type>,
	{
		let stack_len = self.stack.len();
		let sig_len = signature.len();

		// Check for stack length
		if mtch == StackMatch::Exact && sig_len < stack_len {
			let expected = signature.iter().map(Borrow::borrow).cloned().collect();
			// TODO: refactor this var to somewhere else
			let found = self.stack.items[stack_len - sig_len - 1..].to_vec();

			return Err(Error::InvalidStack {
				expected,
				stack: StackError::TooMany {
					found,
					caused_by: self.stack.too_many_items(sig_len),
				},
				span: self.span,
			});
		}
		if sig_len > stack_len {
			let expected = signature.iter().map(Borrow::borrow).cloned().collect();
			let found = self.stack.items.clone();

			return Err(Error::InvalidStack {
				expected,
				stack: StackError::TooFew {
					found,
					consumed_by: (self.stack.consumed_by(sig_len)),
				},
				span: self.span,
			});
		}

		// Check each item on the stack
		for (i, typ) in signature.iter().rev().enumerate() {
			// SAFETY: it is safe to index items because we checked them for exhaustion above
			let item = &self.stack.items[stack_len - 1 - i];

			if *typ.borrow() != item.typ {
				let expected = signature.iter().map(Borrow::borrow).cloned().collect();
				let found = self.stack.items[stack_len - sig_len..].to_vec();

				return Err(Error::InvalidStack {
					expected,
					stack: StackError::Invalid { found },
					span: self.span,
				});
			}
		}

		// Consume items from the stack
		if !self.keep {
			self.stack.drain(sig_len, self.span);
		}

		Ok(())
	}

	/// Items consumed by this consumer
	pub fn consumed(&'a self) -> &'a [Spanned<StackItem>] {
		let start = self.stack.consumed.len().saturating_sub(self.consumed_n);
		&self.stack.consumed[start..]
	}

	/// Items consumed by this consumer
	pub fn found(&self) -> Vec<StackItem> {
		self.consumed().iter().map(|t| t.x.clone()).collect()
	}
	pub fn found_sizes(&self) -> Vec<Spanned<u16>> {
		self.consumed()
			.iter()
			.map(|t| Spanned::new(t.x.typ.size(), t.x.pushed_at))
			.collect()
	}
	/// Spans of operations that caused items exhaustion
	pub fn consumed_by(&self) -> Vec<Span> {
		let start = self.stack.consumed.len().saturating_sub(self.expected_n);
		self.stack.consumed[start..]
			.iter()
			.map(|t| t.span)
			.collect()
	}

	pub fn stack_error(&self) -> StackError {
		if self.expected_n > self.consumed_n {
			StackError::TooFew {
				found: self.found(),
				consumed_by: self.consumed_by(),
			}
		} else {
			StackError::Invalid {
				found: self.found(),
			}
		}
	}
}
