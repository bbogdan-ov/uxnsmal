use crate::lexer::Span;

/// Warning
#[derive(thiserror::Error, Debug, Clone, PartialEq, Eq)]
pub enum Warn {
	#[error("dead code")]
	DeadCode(Span),
}
impl Warn {
	pub fn span(&self) -> Option<Span> {
		match self {
			Self::DeadCode(span) => Some(*span),
		}
	}
}
