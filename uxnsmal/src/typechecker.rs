use std::{borrow::Borrow, collections::HashMap};

use crate::{
	ast::{Ast, Expr, FuncArgs, Node, Stmt, Typed, TypedAst, TypedPtrTo, TypedSymbol},
	error,
	lexer::{Span, Spanned},
	symbols::{Name, Type},
};

/// Stack match
/// How stacks should be compared
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackMatch {
	/// Only tails of the stacks must be equal
	Tail,
	/// Stack must be exact the same
	Exact,
}

/// Stack item
#[derive(Debug, Clone, Eq)]
struct StackItem {
	pub typ: Type,
	/// Span of the operation that pushed this type onto the stack
	pub pushed_at: Span,
}
impl StackItem {
	pub fn new(typ: Type, pushed_at: Span) -> Self {
		Self { typ, pushed_at }
	}
}
impl PartialEq for StackItem {
	fn eq(&self, rhs: &Self) -> bool {
		return self.typ == rhs.typ;
	}
}
impl From<(Type, Span)> for StackItem {
	fn from(value: (Type, Span)) -> Self {
		Self::new(value.0, value.1)
	}
}

/// Stack
#[derive(Debug)]
struct Stack {
	pub items: Vec<StackItem>,
}
impl Default for Stack {
	fn default() -> Self {
		Self {
			items: Vec::with_capacity(256),
		}
	}
}
impl Stack {
	pub fn push(&mut self, item: impl Into<StackItem>) {
		self.items.push(item.into());
	}
	pub fn pop(&mut self) -> Option<StackItem> {
		self.items.pop()
	}

	pub fn reset(&mut self) {
		self.items.clear();
	}

	pub fn compare_len(&mut self, len: usize, span: Span) -> error::Result<()> {
		if len != self.len() {
			todo!("'unmatched stacks length' error {span}");
		}
		Ok(())
	}

	/// Consume and compare types in the stack with types in the iterator
	pub fn compare<I, T>(&mut self, iter: I, mtch: StackMatch, span: Span) -> error::Result<()>
	where
		T: Borrow<Type>,
		I: IntoIterator<Item = T>,
		I::IntoIter: DoubleEndedIterator,
	{
		let iter = iter.into_iter();
		let len = iter.size_hint().1.unwrap_or(0);

		if mtch == StackMatch::Exact {
			self.compare_len(len, span)?;
		}

		for typ in iter {
			let Some(item) = self.pop() else {
				todo!("'not enough items' error");
			};

			if *typ.borrow() != item.typ {
				todo!("'unmatched types' error");
				break;
			}
		}

		Ok(())
	}

	pub fn len(&self) -> usize {
		self.items.len()
	}
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}
}

/// Symbol kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SymbolKind {
	Func,
	Var,
	Const,
	Data,
}

/// Typechecker
/// Performs type-checking of the specified untyped AST and spits a typed one.
pub struct Typechecker {
	/// Working stack
	ws: Stack,

	symbols: HashMap<Name, SymbolKind>,
}
impl Typechecker {
	pub fn check(mut ast: Ast) -> error::Result<TypedAst> {
		let mut checker = Self {
			ws: Stack::default(),

			symbols: HashMap::with_capacity(128),
		};

		checker.collect(&ast)?;
		checker.check_nodes(&mut ast.nodes)?;

		Ok(TypedAst(ast))
	}

	/// Walk through AST and collect all symbols definitions
	fn collect(&mut self, ast: &Ast) -> error::Result<()> {
		for node in ast.nodes.iter() {
			let Node::Stmt(stmt) = &node.x else {
				continue;
			};

			match stmt {
				Stmt::FuncDef(def) => self.define_symbol(def.name.clone(), SymbolKind::Func)?,
				Stmt::VarDef(def) => self.define_symbol(def.name.clone(), SymbolKind::Var)?,
				Stmt::ConstDef(def) => self.define_symbol(def.name.clone(), SymbolKind::Const)?,
				Stmt::DataDef(def) => self.define_symbol(def.name.clone(), SymbolKind::Data)?,

				_ => (),
			}
		}

		Ok(())
	}
	fn define_symbol(&mut self, name: Name, kind: SymbolKind) -> error::Result<()> {
		let prev = self.symbols.insert(name, kind);
		if prev.is_some() {
			todo!("'symbol redifinition' error");
		} else {
			Ok(())
		}
	}

	fn check_nodes(&mut self, nodes: &mut [Spanned<Node>]) -> error::Result<()> {
		for node in nodes.iter_mut() {
			self.check_node(&mut node.x, node.span)?;
		}
		Ok(())
	}
	fn check_node(&mut self, node: &mut Node, node_span: Span) -> error::Result<()> {
		match node {
			Node::Expr(expr) => self.check_expr(expr, node_span),
			Node::Stmt(stmt) => self.check_stmt(stmt, node_span),
		}
	}
	fn check_expr(&mut self, expr: &mut Expr, expr_span: Span) -> error::Result<()> {
		match expr {
			Expr::Symbol(n, Typed::Typed(_)) => unreachable!("unexpected typed symbol {n:?}"),
			Expr::PtrTo(n, Typed::Typed(_)) => unreachable!("unexpected typed pointer to {n:?}"),

			Expr::Byte(_) => self.ws.push((Type::Byte, expr_span)),
			Expr::Short(_) => self.ws.push((Type::Short, expr_span)),
			Expr::String(_) => self.ws.push((Type::ShortPtr(Type::Byte.into()), expr_span)),
			Expr::Padding(_) => (/* ignore */),

			Expr::Intrinsic(i, m) => todo!("check intrinsic"),

			Expr::Symbol(name, t @ Typed::Untyped) => {
				*t = match self.symbols.get(name) {
					Some(SymbolKind::Func) => Typed::Typed(TypedSymbol::Func),
					Some(SymbolKind::Var) => Typed::Typed(TypedSymbol::Var),
					Some(SymbolKind::Const) => Typed::Typed(TypedSymbol::Const),
					Some(SymbolKind::Data) => Typed::Typed(TypedSymbol::Data),
					None => todo!("'unknown symbol' error"),
				};
			}
			Expr::PtrTo(name, t @ Typed::Untyped) => {
				*t = match self.symbols.get(name) {
					Some(SymbolKind::Func) => Typed::Typed(TypedPtrTo::Func),
					Some(SymbolKind::Var) => Typed::Typed(TypedPtrTo::Var),
					Some(SymbolKind::Data) => Typed::Typed(TypedPtrTo::Data),

					Some(SymbolKind::Const) => todo!("'illegal ptr to const' error"),
					None => todo!("'unknown symbol' error"),
				};
			}
		}

		Ok(())
	}
	fn check_stmt(&mut self, stmt: &mut Stmt, stmt_span: Span) -> error::Result<()> {
		match stmt {
			Stmt::FuncDef(def) => {
				self.reset();

				if let FuncArgs::Proc { inputs, .. } = &def.args {
					for input in inputs.iter() {
						self.ws.push((input.x.clone(), input.span));
					}
				}

				self.check_nodes(&mut def.body)?;

				match &def.args {
					FuncArgs::Vector => {
						self.ws.compare_len(0, stmt_span)?;
					}
					FuncArgs::Proc { outputs, .. } => {
						let iter = outputs.iter().map(|t| &t.x);
						self.ws.compare(iter, StackMatch::Exact, stmt_span)?;
					}
				}
			}

			Stmt::VarDef(_) => todo!("check var def"),

			Stmt::ConstDef(def) => {
				self.reset();
				self.check_nodes(&mut def.body)?;
				self.ws
					.compare([Type::Byte], StackMatch::Exact, stmt_span)?;
			}

			Stmt::DataDef(_) => todo!("check data def"),

			Stmt::Block {
				looping,
				label,
				body,
			} => todo!("check block"),
			Stmt::Jump { label, conditional } => todo!("check jump"),
			Stmt::If { if_body, else_body } => todo!("check if"),
			Stmt::While { condition, body } => todo!("check while"),
		}

		Ok(())
	}

	/// Reset all stacks
	fn reset(&mut self) {
		self.ws.reset();
	}
}
