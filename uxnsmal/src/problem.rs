use crate::lexer::Span;

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

	pub fn with_note(mut self, note: Note) -> Self {
		self.notes.push(note);
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
	pub fn fatal<T>(&mut self, problem: Problem) -> Result<T, FatalError> {
		self.push(problem);
		Err(FatalError)
	}
}
