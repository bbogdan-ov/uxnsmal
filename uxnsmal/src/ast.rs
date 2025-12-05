//! # But why is there an AST for a concatenative language??
//!
//! - I want to separate syntax from the intermediate program because i plan to add more syntax sugar
//!   that is simpler to parse first to AST and then parse it to the intermediate code.
//!
//! - Also it would be simpler to typecheck an AST and give more info about the error based on its
//!   context/location because all token spans are stored in the AST nodes themselves, but this is
//!   not possible with intermediate program/code (because i don't want to store any info about the
//!   source code inside intermediate code)

mod def;
mod expr;

pub use def::*;
pub use expr::*;

use std::fmt::Debug;

use crate::lexer::Span;

/// AST node
#[derive(Debug, Clone)]
pub enum Node {
	/// Expression node
	Expr(Expr),
	/// Definition node
	Def(Def),
}
impl Node {
	pub fn span(&self) -> Span {
		match self {
			Self::Expr(expr) => expr.span(),
			Self::Def(def) => def.span(),
		}
	}
}

/// Program abstract syntax tree
#[derive(Debug, Clone)]
pub struct Ast {
	pub nodes: Vec<Node>,
}
impl Default for Ast {
	fn default() -> Self {
		Self {
			nodes: Vec::with_capacity(128),
		}
	}
}
