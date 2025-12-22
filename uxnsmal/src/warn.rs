use std::fmt::Display;

use crate::lexer::Span;

/// Warning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Warn {
	DeadCode(Span),
}
impl std::error::Error for Warn {}
impl Display for Warn {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::DeadCode(_) => write!(f, "dead code"),
		}
	}
}
impl Warn {
	pub fn span(&self) -> Option<Span> {
		match self {
			Self::DeadCode(span) => Some(*span),
		}
	}
}
