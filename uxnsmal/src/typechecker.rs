use std::{borrow::Borrow, collections::HashMap};

use crate::{
	ast::{Ast, Expr, FuncArgs, Node, Stmt, Typed, TypedAst, TypedPtrTo, TypedSymbol},
	error,
	lexer::{Span, Spanned},
	program::{Intrinsic, IntrinsicMode},
	symbols::{ConstSignature, FuncSignature, Name, Type, VarSignature},
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
pub struct StackItem {
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
pub struct Stack {
	pub items: Vec<StackItem>,

	keep_cursor: usize,
}
impl Default for Stack {
	fn default() -> Self {
		Self {
			items: Vec::with_capacity(256),

			keep_cursor: 0,
		}
	}
}
impl Stack {
	pub fn push(&mut self, item: impl Into<StackItem>) {
		self.keep_cursor = 0;
		self.items.push(item.into());
	}
	pub fn pop(&mut self, keep: bool) -> error::Result<StackItem> {
		let item: Option<StackItem>;

		if keep {
			if self.items.is_empty() {
				todo!("'empty stack' error")
			}

			let idx = self.items.len() - self.keep_cursor - 1;
			item = self.items.get(idx).cloned();
			self.keep_cursor += 1;
		} else {
			self.keep_cursor = 0;
			item = self.items.pop();
		}

		item.ok_or_else(|| todo!("'empty stack' error"))
	}

	pub fn reset(&mut self) {
		self.items.clear();
		self.keep_cursor = 0;
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

		for typ in iter.rev() {
			let item = self.pop(false)?;

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
#[derive(Debug, Clone)]
enum Symbol {
	Func(FuncSignature),
	Var(VarSignature),
	Const(ConstSignature),
	Data,
}

/// Typechecker
/// Performs type-checking of the specified untyped AST and spits a typed one.
pub struct Typechecker {
	/// Working stack
	pub ws: Stack,

	symbols: HashMap<Name, Symbol>,
}
impl Default for Typechecker {
	fn default() -> Self {
		Self {
			ws: Stack::default(),

			symbols: HashMap::with_capacity(128),
		}
	}
}
impl Typechecker {
	pub fn check(mut ast: Ast) -> error::Result<TypedAst> {
		let mut checker = Self::default();

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
				Stmt::FuncDef(def) => {
					let sig = def.args.to_signature();
					self.define_symbol(def.name.clone(), Symbol::Func(sig))?
				}
				Stmt::VarDef(def) => {
					let sig = VarSignature {
						typ: def.typ.x.clone(),
					};
					self.define_symbol(def.name.clone(), Symbol::Var(sig))?
				}
				Stmt::ConstDef(def) => {
					let sig = ConstSignature {
						typ: def.typ.x.clone(),
					};
					self.define_symbol(def.name.clone(), Symbol::Const(sig))?;
				}
				Stmt::DataDef(def) => {
					self.define_symbol(def.name.clone(), Symbol::Data)?;
				}

				_ => (),
			}
		}

		Ok(())
	}
	fn define_symbol(&mut self, name: Name, kind: Symbol) -> error::Result<()> {
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
	pub fn check_expr(&mut self, expr: &mut Expr, expr_span: Span) -> error::Result<()> {
		match expr {
			Expr::Symbol(n, Typed::Typed(_)) => unreachable!("unexpected typed symbol {n:?}"),
			Expr::PtrTo(n, Typed::Typed(_)) => unreachable!("unexpected typed pointer to {n:?}"),

			Expr::Byte(_) => self.ws.push((Type::Byte, expr_span)),
			Expr::Short(_) => self.ws.push((Type::Short, expr_span)),
			Expr::String(_) => self.ws.push((Type::ShortPtr(Type::Byte.into()), expr_span)),
			Expr::Padding(_) => (/* ignore */),

			Expr::Intrinsic(intr, mode) => self.check_intrinsic(*intr, mode, expr_span)?,

			Expr::Symbol(name, t @ Typed::Untyped) => {
				*t = match self.symbols.get(name) {
					// Function call
					Some(Symbol::Func(sig)) => match sig {
						FuncSignature::Vector => todo!("'illegal vector call' error"),
						FuncSignature::Proc { inputs, outputs } => {
							// Check function inputs
							let iter = inputs.iter();
							self.ws.compare(iter, StackMatch::Tail, expr_span)?;

							// Push function outputs
							for output in outputs.iter() {
								self.ws.push((output.clone(), expr_span));
							}

							Typed::Typed(TypedSymbol::Func)
						}
					},
					// Variable load
					Some(Symbol::Var(sig)) => {
						self.ws.push((sig.typ.clone(), expr_span));
						Typed::Typed(TypedSymbol::Var)
					}
					// Constant use
					Some(Symbol::Const(sig)) => {
						self.ws.push((sig.typ.clone(), expr_span));
						Typed::Typed(TypedSymbol::Const)
					}
					// Data load
					Some(Symbol::Data) => {
						self.ws.push((Type::Byte, expr_span));
						Typed::Typed(TypedSymbol::Data)
					}

					None => todo!("'unknown symbol' error"),
				};
			}
			Expr::PtrTo(name, t @ Typed::Untyped) => {
				*t = match self.symbols.get(name) {
					Some(Symbol::Func(sig)) => {
						let typ = Type::FuncPtr(sig.clone());
						self.ws.push((typ, expr_span));
						Typed::Typed(TypedPtrTo::Func)
					}
					Some(Symbol::Var(sig)) => {
						let typ = Type::BytePtr(sig.typ.clone().into());
						self.ws.push((typ, expr_span));
						Typed::Typed(TypedPtrTo::Var)
					}
					Some(Symbol::Data) => {
						let typ = Type::ShortPtr(Type::Byte.into());
						self.ws.push((typ, expr_span));
						Typed::Typed(TypedPtrTo::Data)
					}

					Some(Symbol::Const(_)) => todo!("'illegal ptr to const' error"),
					None => todo!("'unknown symbol' error"),
				};
			}
		}

		Ok(())
	}
	pub fn check_stmt(&mut self, stmt: &mut Stmt, stmt_span: Span) -> error::Result<()> {
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
				looping: _,
				label: _,
				body: _,
			} => todo!("check block"),
			Stmt::Jump {
				label: _,
				conditional: _,
			} => todo!("check jump"),
			Stmt::If {
				if_body: _,
				else_body: _,
			} => todo!("check if"),
			Stmt::While {
				condition: _,
				body: _,
			} => todo!("check while"),
		}

		Ok(())
	}

	pub fn check_intrinsic(
		&mut self,
		intr: Intrinsic,
		mode: &mut IntrinsicMode,
		intr_span: Span,
	) -> error::Result<()> {
		let keep = mode.contains(IntrinsicMode::KEEP);

		match intr {
			Intrinsic::Load(Typed::Typed(_)) => unreachable!("unexpected typed 'load' intrinsic"),
			Intrinsic::Store(Typed::Typed(_)) => unreachable!("unexpected typed 'store' intrinsic"),

			Intrinsic::Add | Intrinsic::Sub | Intrinsic::Mul | Intrinsic::Div => {
				// ( a b -- a+b )
				self.check_arithmetic_intr(mode, intr_span)?;
			}

			Intrinsic::Inc => {
				// ( a -- a+1 )
				let a = self.ws.pop(keep)?;
				if a.typ.is_short() {
					*mode |= IntrinsicMode::SHORT;
				}
				self.ws.push(a);
			}

			Intrinsic::Shift => {
				// ( a shift8 -- c )
				let shift8 = self.ws.pop(keep)?;
				let a = self.ws.pop(keep)?;

				if shift8.typ != Type::Byte {
					todo!("'wrong shift input' error");
				}

				match a.typ {
					Type::Byte => self.ws.push((Type::Byte, intr_span)),
					Type::Short => {
						*mode |= IntrinsicMode::SHORT;
						self.ws.push((Type::Short, intr_span))
					}
					_ => todo!("'wrong a input' error"),
				}
			}
			Intrinsic::And | Intrinsic::Or | Intrinsic::Xor => {
				// ( a b -- c )
				let b = self.ws.pop(keep)?;
				let a = self.ws.pop(keep)?;

				let output = match (a.typ, b.typ) {
					(Type::Byte, Type::Byte) => Type::Byte,
					(Type::Short, Type::Short) => Type::Short,
					_ => todo!("'input types dont match' error"),
				};
				if output.is_short() {
					*mode |= IntrinsicMode::SHORT;
				}

				self.ws.push((output, intr_span));
			}

			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				// ( a b -- bool8 )
				let b = self.ws.pop(keep)?;
				let a = self.ws.pop(keep)?;
				let short = match (a.typ, b.typ) {
					(Type::Byte, Type::Byte) => false,
					(Type::Short, Type::Short) => true,
					// NOTE: we don't care what inner types are
					(Type::BytePtr(_), Type::BytePtr(_)) => false,
					(Type::ShortPtr(_), Type::ShortPtr(_)) => true,
					(Type::FuncPtr(_), Type::FuncPtr(_)) => true,
					_ => todo!("'input types dont match' error"),
				};

				if short {
					*mode |= IntrinsicMode::SHORT;
				}

				self.ws.push((Type::Byte, intr_span));
			}

			Intrinsic::Pop => todo!("Pop intrinsic"),
			Intrinsic::Swap => todo!("Swap intrinsic"),
			Intrinsic::Nip => todo!("Nip intrinsic"),
			Intrinsic::Rot => todo!("Rot intrinsic"),
			Intrinsic::Dup => todo!("Dup intrinsic"),
			Intrinsic::Over => todo!("Over intrinsic"),

			Intrinsic::Load(Typed::Untyped) => todo!("Load intrinsic"),
			Intrinsic::Store(Typed::Untyped) => todo!("Store intrinsic"),

			Intrinsic::Input | Intrinsic::Input2 => {
				// ( device8 -- value )
				let device8 = self.ws.pop(keep)?;
				if device8.typ != Type::Byte {
					todo!("'wrong device input' error");
				}

				if intr == Intrinsic::Input2 {
					*mode |= IntrinsicMode::SHORT;
					self.ws.push((Type::Short, intr_span));
				} else {
					self.ws.push((Type::Byte, intr_span));
				}
			}
			Intrinsic::Output => {
				// ( val device8 -- )
				let device8 = self.ws.pop(keep)?;
				let _val = self.ws.pop(keep)?;
				if device8.typ != Type::Byte {
					todo!("'wrong device input' error");
				}
			}
		}

		Ok(())
	}
	fn check_arithmetic_intr(
		&mut self,
		mode: &mut IntrinsicMode,
		intr_span: Span,
	) -> error::Result<()> {
		let keep = mode.contains(IntrinsicMode::KEEP);
		let b = self.ws.pop(keep)?;
		let a = self.ws.pop(keep)?;

		let output = match (a.typ, b.typ) {
			(Type::Byte, Type::Byte) => Type::Byte,
			(Type::Short, Type::Short) => Type::Short,

			(Type::Byte, Type::BytePtr(t)) => Type::BytePtr(t),
			(Type::Short, Type::ShortPtr(t)) => Type::ShortPtr(t),
			(Type::Short, Type::FuncPtr(t)) => Type::FuncPtr(t),
			(Type::BytePtr(t), Type::Byte) => Type::BytePtr(t),
			(Type::ShortPtr(t), Type::Short) => Type::ShortPtr(t),
			(Type::FuncPtr(t), Type::Short) => Type::FuncPtr(t),

			(Type::BytePtr(a), Type::BytePtr(b)) => {
				if a == b {
					Type::BytePtr(a)
				} else {
					todo!("'wrong inner ptr type' error")
				}
			}
			(Type::ShortPtr(a), Type::ShortPtr(b)) => {
				if a == b {
					Type::ShortPtr(a)
				} else {
					todo!("'wrong inner ptr type' error")
				}
			}
			(Type::FuncPtr(a), Type::FuncPtr(b)) => {
				if a == b {
					Type::FuncPtr(a)
				} else {
					todo!("'wrong inner ptr type' error")
				}
			}

			_ => todo!("'wrong inputs' error"),
		};

		if output.is_short() {
			*mode |= IntrinsicMode::SHORT;
		}

		self.ws.push((output, intr_span));

		Ok(())
	}

	/// Reset all stacks
	fn reset(&mut self) {
		self.ws.reset();
	}
}
