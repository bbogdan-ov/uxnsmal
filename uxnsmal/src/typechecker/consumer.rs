use std::borrow::Borrow;

use crate::{
	error::{self, Error, ExpectedNames, ExpectedStack, FoundNames, FoundStack, StackError},
	lexer::{Span, Spanned},
	symbols::{Name, Type},
	typechecker::{ConsumedStackItem, Stack, StackItem, StackMatch},
};

/// Stack consumer.
pub struct Consumer<'a> {
	pub stack: &'a mut Stack,

	/// Whether the consumer should clone items instead of popping them from the stack.
	pub keep: bool,
	pub keep_cursor: usize,

	/// Number of consumed items by this consumer.
	pub consumed_n: usize,
	/// Number of expected items.
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

	/// Compare types on the stack with types in the iterator.
	pub fn compare<'t, T, I>(&mut self, signature: I, mtch: StackMatch) -> error::Result<()>
	where
		T: Borrow<Type> + 't,
		I: Iterator<Item = &'t T> + ExactSizeIterator + DoubleEndedIterator + Clone,
	{
		let stack_len = self.stack.len();
		self.expected_n = signature.len();

		macro_rules! found {
			() => {
				match mtch {
					StackMatch::Exact => &self.stack.items,
					StackMatch::Tail => self.stack.tail(self.expected_n),
				}
			};
		}

		macro_rules! stack_err {
			($error:expr) => {
				Error::InvalidStack {
					expected: ExpectedStack::Types(signature.map(|t| t.borrow().clone()).collect()),
					found: FoundStack(found!().to_vec()),
					error: $error,
					span: self.span,
				}
			};
		}

		if mtch == StackMatch::Exact && self.expected_n < stack_len {
			// Too many items on the stack.
			return Err(stack_err!(StackError::TooMany {
				caused_by: self.overflow_caused_by(),
			}));
		}

		if self.expected_n > stack_len {
			// Too few items on the stack.
			return Err(stack_err!(StackError::TooFew {
				consumed_by: self.underflow_caused_by(),
			}));
		}

		// Check each item on the stack.
		for (i, typ) in signature.clone().rev().enumerate() {
			// SAFETY: it is safe to index items because we checked them for exhaustion above.
			let item = &self.stack.items[stack_len - 1 - i];

			if item.typ != *typ.borrow() {
				return Err(stack_err!(StackError::Invalid));
			}
		}

		if !self.keep {
			// Consume items from the stack.
			self.stack.drain(self.expected_n, self.span);
		}

		self.consumed_n = self.expected_n;

		Ok(())
	}

	pub fn compare_names<T, I>(&mut self, names: I) -> error::Result<()>
	where
		T: Borrow<Name>,
		I: Iterator<Item = Option<T>> + ExactSizeIterator + DoubleEndedIterator + Clone,
	{
		let stack_len = self.stack.len();
		self.expected_n = names.len();

		macro_rules! names_err {
			($error:expr) => {{
				let found = FoundNames::from_items(&self.stack.items);
				let expected = names.map(|n| n.map(|n| n.borrow().clone())).collect();

				Error::InvalidNames {
					error: $error,
					found,
					expected: ExpectedNames(expected),
					span: self.span,
				}
			}};
		}

		if self.expected_n > stack_len {
			// Too few items on the stack.
			return Err(names_err!(StackError::TooFew {
				consumed_by: self.underflow_caused_by(),
			}));
		}

		for (i, name) in names.clone().rev().enumerate() {
			let len = self.stack.items.len();
			let item = &self.stack.items[len - 1 - i];

			let has_match = match name {
				Some(name) => item.name.as_ref().is_some_and(|n| n == name.borrow()),
				None => item.name.is_none(),
			};

			if !has_match {
				return Err(names_err!(StackError::Invalid));
			}
		}

		if !self.keep {
			// Consume items from the stack.
			self.stack.drain(self.expected_n, self.span);
		}

		self.consumed_n = self.expected_n;

		Ok(())
	}

	/// Items consumed by this consumer.
	pub fn consumed(&'a self) -> &'a [ConsumedStackItem] {
		let start = self.stack.consumed.len().saturating_sub(self.consumed_n);
		&self.stack.consumed[start..]
	}

	/// Items consumed by this consumer.
	/// Used for error constructing.
	pub fn found(&self) -> FoundStack {
		FoundStack(
			self.consumed()
				.iter()
				.rev()
				.map(|t| t.item.clone())
				.collect(),
		)
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

		let mut n = self.expected_n.saturating_sub(self.stack.len());
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
