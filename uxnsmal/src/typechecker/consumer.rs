use std::borrow::Borrow;

use crate::{
	error::{self, Error},
	lexer::{Span, Spanned},
	symbols::Type,
	typechecker::{Stack, StackItem, StackMatch},
};

/// Stack consumer
pub struct Consumer<'a> {
	pub stack: &'a mut Stack,

	/// Expected number of items on the stack
	pub expected_n: usize,
	/// Whether the consumer should clone items instead of popping them from the stack
	pub keep: bool,
	pub keep_cursor: usize,
	pub span: Span,
}
impl<'a> Consumer<'a> {
	pub fn new(stack: &'a mut Stack, span: Span) -> Self {
		Self {
			stack,

			expected_n: 0,
			keep: false,
			keep_cursor: 0,
			span,
		}
	}

	pub fn with_keep(mut self, keep: bool) -> Self {
		self.keep = keep;
		self
	}
	pub fn with_expected_n(mut self, expected_n: usize) -> Self {
		self.expected_n = expected_n;
		self
	}

	pub fn pop(&mut self) -> error::Result<StackItem> {
		let item = if self.keep {
			if self.keep_cursor < self.stack.len() {
				let idx = self.stack.len() - self.keep_cursor - 1;
				let item = self.stack.items[idx].clone();
				self.keep_cursor += 1;
				Some(item)
			} else {
				None
			}
		} else {
			self.stack.items.pop()
		};

		let Some(item) = item else {
			return Err(Error::TooFewItems {
				consumed_by: self.stack.consumed_by(self.expected_n),
				span: self.span,
			});
		};

		self.expected_n = self.expected_n.saturating_sub(1);

		self.stack
			.consumed
			.push(Spanned::new(item.clone(), self.span));

		Ok(item)
	}

	/// Compare types in the stack with types in the iterator
	pub fn compare<T>(&mut self, signature: &[T], mtch: StackMatch) -> error::Result<()>
	where
		T: Borrow<Type>,
	{
		let stack_len = self.stack.len();

		if mtch == StackMatch::Exact && signature.len() < stack_len {
			return Err(Error::TooManyItems {
				caused_by: self.stack.too_many_items(signature.len()),
				span: self.span,
			});
		}
		if signature.len() > stack_len {
			return Err(Error::TooFewItems {
				consumed_by: self.stack.consumed_by(signature.len()),
				span: self.span,
			});
		}

		for (i, typ) in signature.iter().rev().enumerate() {
			// SAFETY: it is safe to index items because we checked them for exhaustion above
			let item = &self.stack.items[stack_len - 1 - i];

			if *typ.borrow() != item.typ {
				let expected = signature.iter().map(Borrow::borrow).cloned().collect();
				let found = self.stack.items[stack_len - signature.len()..].to_vec();

				return Err(Error::InvalidStackSignature {
					expected,
					found,
					span: self.span,
				});
			}
		}

		if !self.keep {
			self.stack.drain(signature.len(), self.span);
		}

		Ok(())
	}
}
