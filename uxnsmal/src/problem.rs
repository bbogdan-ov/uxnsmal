use std::fmt::Display;

use crate::{
	lexer::Span,
	symbol::{self, Name, Type},
	typechecker::{Item, Stack},
};

pub type Result<T> = std::result::Result<T, Problem>;

/// Fatal error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FatalError;

#[macro_export]
macro_rules! err {
	($span:expr, $($arg:tt)*) => {
		$crate::problem::Problem::err(format!($($arg)*), $span)
	};
}

#[macro_export]
macro_rules! warn {
	($span:expr, $($arg:tt)*) => {
		$crate::problem::Problem::warn(format!($($arg)*), $span)
	};
}

#[macro_export]
macro_rules! note {
	($span:expr, $($arg:tt)*) => {
		$crate::problem::Note::new(format!($($arg)*), $span)
	};
}

#[macro_export]
macro_rules! bug {
	($($arg:tt)+) => {
		panic!("this is a bug: {}", format_args!($($arg)+))
	};
}

/// Problem kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProblemKind {
	Error,
	Warning,
}

/// Problem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Problem {
	pub kind: ProblemKind,
	pub msg: String,
	pub span: Span,
	pub notes: Vec<Note>,
}
impl Problem {
	pub fn err(msg: String, span: Span) -> Self {
		Self {
			kind: ProblemKind::Error,
			msg,
			span,
			notes: Vec::default(),
		}
	}
	pub fn warn(msg: String, span: Span) -> Self {
		Self {
			kind: ProblemKind::Warning,
			msg,
			span,
			notes: Vec::default(),
		}
	}

	#[inline(always)]
	pub fn with_note(mut self, note: Note) -> Self {
		self.notes.push(note);
		self
	}
	#[inline(always)]
	pub fn with_notes(mut self, notes: impl IntoIterator<Item = Note>) -> Self {
		self.notes.extend(notes);
		self
	}

	/// Notes to items which caused stack underflow.
	pub fn with_notes_consumed_here(mut self, stack: &Stack, n: usize) -> Self {
		// TODO: accumulate number of consumed items into one "note" if multiple consumtions
		// happened in one place/operation. Also display how many items this operation spat out.
		for item in stack.consumed.iter().rev().take(n) {
			self.notes.push(note!(item.consumed_at, "consumed here"));
		}
		self
	}
	/// Notes to items which caused stack overflow.
	pub fn with_notes_caused_by(mut self, stack: &Stack, n: usize) -> Self {
		for item in stack.items.iter().rev().take(n) {
			self.notes.push(note!(item.pushed_at, "caused by this"));
		}
		self
	}
}
impl std::error::Error for Problem {}
impl std::fmt::Display for Problem {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.msg)
	}
}

/// Problem "note" message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Note {
	pub msg: String,
	pub span: Span,
}
impl Note {
	pub fn new(msg: String, span: Span) -> Self {
		Self { msg, span }
	}
}
impl std::fmt::Display for Note {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.msg)
	}
}

/// Problems.
#[derive(Default, Debug)]
pub struct Problems {
	pub list: Vec<Problem>,
}
impl Problems {
	#[inline(always)]
	pub fn push(&mut self, problem: Problem) {
		self.list.push(problem);
	}
	/// Convenience function, pushes `problem` and always returns `Err(FatalError)`.
	#[inline(always)]
	pub fn fatal<T>(&mut self, problem: Problem) -> std::result::Result<T, FatalError> {
		self.push(problem);
		Err(FatalError)
	}
}

// --------------------
// Helper functions
// --------------------

pub fn err_redefinition(name: &Name, what: impl Display, defined_at: Span, span: Span) -> Problem {
	let e = err!(span, "redefinition of {what} `{name}`");
	let n = note!(defined_at, "defined here");
	e.with_note(n)
}

pub fn note_this_is(item: &Item) -> Note {
	let span = item.pushed_at;
	note!(span, "this is `{}`", item.typ)
}
pub fn note_size_is(item: &Item) -> Note {
	let span = item.pushed_at;
	let size = item.typ.size();
	if size == 1 {
		note!(span, "`{}` is {size} byte", item.typ)
	} else {
		note!(span, "`{}` is {size} bytes", item.typ)
	}
}
pub fn note_this_is_but_expected(item: &Item, expected: &Type) -> Note {
	let span = item.pushed_at;
	let typ = &item.typ;
	note!(span, "this is `{typ}`, expected `{expected}`",)
}
pub fn note_name_is_but_expected(item: &Item, expected: Option<&Name>) -> Note {
	note!(
		item.pushed_at,
		"name is \"{}\", expected \"{}\"",
		symbol::option_name_str(item.name.as_ref()),
		symbol::option_name_str(expected)
	)
}
