use crate::lexer::Span;

/// Warning
#[derive(thiserror::Error, Debug, Clone, PartialEq, Eq)]
pub enum Warn {
	#[error("dead code")]
	DeadCode(Span),
}
