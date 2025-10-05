use std::{borrow::Borrow, collections::HashMap};

use crate::{
	ast::{Ast, Def, Expr, FuncArgs, Node},
	error::{self, ErrorKind},
	lexer::{Span, Spanned},
	program::{IntrMode, Intrinsic},
	symbols::{ConstSignature, FuncSignature, Name, Type, UniqueName, VarSignature},
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
impl Borrow<Type> for StackItem {
	fn borrow(&self) -> &Type {
		&self.typ
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
		// TODO: restrict size of the stack (256 bytes)
		self.keep_cursor = 0;
		self.items.push(item.into());
	}
	pub fn pop(&mut self, keep: bool) -> Option<StackItem> {
		if self.items.is_empty() {
			return None;
		}

		if keep {
			if self.keep_cursor >= self.items.len() {
				return None;
			}

			let idx = self.items.len() - self.keep_cursor - 1;
			let item = self.items.get(idx).cloned()?;
			self.keep_cursor += 1;
			Some(item)
		} else {
			self.keep_cursor = 0;
			self.items.pop()
		}
	}
	pub fn pop_err(&mut self, keep: bool, span: Span) -> error::Result<StackItem> {
		match self.pop(keep) {
			Some(item) => Ok(item),
			None => Err(ErrorKind::NotEnoughInputs.err(span)),
		}
	}

	#[must_use]
	pub fn take_snapshot(&mut self) -> Vec<StackItem> {
		self.items.clone()
	}
	pub fn compare_snapshot(&mut self, snapshot: Vec<StackItem>, span: Span) -> error::Result<()> {
		self.compare(snapshot, StackMatch::Exact, true, span)
	}

	pub fn reset(&mut self) {
		self.items.clear();
		self.keep_cursor = 0;
	}

	/// Consume and compare types in the stack with types in the iterator
	pub fn compare<I, T>(
		&mut self,
		iter: I,
		mtch: StackMatch,
		keep: bool,
		span: Span,
	) -> error::Result<()>
	where
		T: Borrow<Type>,
		I: IntoIterator<Item = T>,
		I::IntoIter: DoubleEndedIterator,
	{
		// TODO: hint expected stack
		// TODO: hint to operations that caused an error

		let iter = iter.into_iter();
		let len = iter.size_hint().1.unwrap_or(0);

		if mtch == StackMatch::Exact && len != self.len() {
			return Err(ErrorKind::NotEnoughInputs.err(span));
		}

		for typ in iter.rev() {
			let item = self.pop_err(keep, span)?;

			if *typ.borrow() != item.typ {
				return Err(ErrorKind::InvalidStackSignature.err(span));
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

/// Symbol signature
#[derive(Debug, Clone)]
enum SymbolSignature {
	Func(FuncSignature),
	Var(VarSignature),
	Const(ConstSignature),
	Data,
}

/// Symbol
#[derive(Debug, Clone)]
struct Symbol {
	unique_name: UniqueName,
	signature: SymbolSignature,
}
impl Symbol {
	pub fn new(unique_name: UniqueName, signature: SymbolSignature) -> Self {
		Self {
			unique_name,
			signature,
		}
	}
}

/// Typechecker
/// Performs type-checking of the specified AST and generates an intermediate representation
pub struct Typechecker {
	/// Working stack
	pub ws: Stack,

	unique_name_id: u32,
	symbols: HashMap<Name, Symbol>,
	/// Table of labels accessible in the current scope.
	/// It is a separate table because labels have a separate namespace.
	labels: HashMap<Name, UniqueName>,
}
impl Default for Typechecker {
	fn default() -> Self {
		Self {
			ws: Stack::default(),

			unique_name_id: 0,
			symbols: HashMap::with_capacity(128),
			labels: HashMap::with_capacity(32),
		}
	}
}
impl Typechecker {
	pub fn check(mut ast: Ast) -> error::Result<()> {
		let mut checker = Self::default();

		checker.collect(&ast)?;
		checker.check_nodes(&mut ast.nodes)?;

		todo!("return IR")
	}

	// ==============================
	// Symbols related stuff
	// ==============================

	fn new_unique_name(&mut self) -> UniqueName {
		self.unique_name_id += 1;
		UniqueName(self.unique_name_id - 1)
	}

	/// Walk through AST and collect all top-level symbol definitions
	fn collect(&mut self, ast: &Ast) -> error::Result<()> {
		for node in ast.nodes.iter() {
			let node_span = node.span;
			let Node::Def(def) = &node.x else {
				continue;
			};

			match def {
				Def::Func(def) => {
					let sig = SymbolSignature::Func(def.args.to_signature());
					self.define_symbol(def.name.clone(), sig, node_span)?
				}
				Def::Var(def) => {
					let sig = SymbolSignature::Var(VarSignature {
						typ: def.typ.x.clone(),
					});
					self.define_symbol(def.name.clone(), sig, node_span)?
				}
				Def::Const(def) => {
					let sig = SymbolSignature::Const(ConstSignature {
						typ: def.typ.x.clone(),
					});
					self.define_symbol(def.name.clone(), sig, node_span)?;
				}
				Def::Data(def) => {
					let sig = SymbolSignature::Data;
					self.define_symbol(def.name.clone(), sig, node_span)?;
				}
			}
		}

		Ok(())
	}
	fn define_symbol(
		&mut self,
		name: Name,
		signature: SymbolSignature,
		span: Span,
	) -> error::Result<()> {
		let symbol = Symbol::new(self.new_unique_name(), signature);
		let prev = self.symbols.insert(name, symbol);
		if prev.is_some() {
			// TODO: hint to the previosly defined symbol
			return Err(ErrorKind::SymbolRedefinition.err(span));
		} else {
			Ok(())
		}
	}

	fn define_label(&mut self, name: Name, span: Span) -> error::Result<()> {
		let unique_name = self.new_unique_name();
		let prev = self.labels.insert(name, unique_name);
		if prev.is_some() {
			// TODO: hint to previosly defined label
			return Err(ErrorKind::LabelRedefinition.err(span));
		} else {
			Ok(())
		}
	}
	fn undefine_label(&mut self, name: &Name) {
		let prev = self.labels.remove(name);
		if prev.is_none() {
			unreachable!("unexpected unexisting label {name:?}");
		}
	}

	// ==============================
	// Node typechecking
	// ==============================

	fn check_nodes(&mut self, nodes: &mut [Spanned<Node>]) -> error::Result<()> {
		for node in nodes.iter_mut() {
			self.check_node(&mut node.x, node.span)?;
		}
		Ok(())
	}
	fn check_node(&mut self, node: &mut Node, node_span: Span) -> error::Result<()> {
		match node {
			Node::Expr(expr) => self.check_expr(expr, node_span),
			Node::Def(def) => self.check_def(def, node_span),
		}
	}
	pub fn check_expr(&mut self, expr: &mut Expr, expr_span: Span) -> error::Result<()> {
		match expr {
			Expr::Byte(_) => self.ws.push((Type::Byte, expr_span)),
			Expr::Short(_) => self.ws.push((Type::Short, expr_span)),
			Expr::String(_) => self.ws.push((Type::ShortPtr(Type::Byte.into()), expr_span)),
			Expr::Padding(_) => (/* ignore */),

			Expr::Intrinsic(intr, mode) => self.check_intrinsic(intr, mode, expr_span)?,

			Expr::Symbol(name) => {
				self.check_symbol(name, expr_span)?;
			}
			Expr::PtrTo(name) => {
				self.check_ptr_to(name, expr_span)?;
			}

			Expr::Block {
				looping: _,
				label,
				body,
			} => {
				let snapshot = self.begin_block();

				self.define_label(label.x.clone(), label.span)?;
				self.check_nodes(body)?;
				self.undefine_label(&label.x);

				self.end_block(snapshot, expr_span)?;
			}

			Expr::Jump { label, conditional } => {
				if !self.labels.contains_key(&label.x) {
					return Err(ErrorKind::UnknownLabel.err(label.span));
				}

				if *conditional {
					let bool8 = self.ws.pop_err(false, expr_span)?;
					if bool8.typ != Type::Byte {
						// TODO: hint expected type
						return Err(ErrorKind::InvalidStackSignature.err(expr_span));
					}
				}
			}

			Expr::If { if_body, else_body } => {
				// Check input condition
				let bool8 = self.ws.pop_err(false, expr_span)?;
				if bool8.typ != Type::Byte {
					// TODO: hint expected type
					return Err(ErrorKind::InvalidStackSignature.err(expr_span));
				}

				if let Some(else_body) = else_body {
					// If-else chain

					// 'if' block
					let snapshot = self.begin_block();
					self.check_nodes(if_body)?;

					// Take snapshot of the stack at the end of 'if' block
					let if_snapshot = self.begin_block();
					// Restore the stack to the state before 'if' block
					self.ws.items = snapshot;

					// 'else' block
					self.check_nodes(else_body)?;
					// Stack at the end of 'else' block and 'if' block must be equal
					self.end_block(if_snapshot, expr_span)?;
				} else {
					// Single 'if'
					let snapshot = self.begin_block();
					self.check_nodes(if_body)?;
					self.end_block(snapshot, expr_span)?;
				}
			}

			Expr::While { condition, body } => {
				let snapshot = self.begin_block();

				// TODO: check condition to NOT consume items outside itself
				self.check_nodes(condition)?;
				let a = self.ws.pop_err(false, expr_span)?;
				if a.typ != Type::Byte {
					// TODO: hint expected type
					return Err(ErrorKind::InvalidConditionOutput.err(expr_span));
				}

				self.check_nodes(body)?;

				self.end_block(snapshot, expr_span)?;
			}
		}

		Ok(())
	}

	fn check_symbol(&mut self, name: &Name, symbol_span: Span) -> error::Result<()> {
		let Some(symbol) = self.symbols.get(name) else {
			return Err(ErrorKind::UnknownSymbol.err(symbol_span));
		};

		match &symbol.signature {
			// Function call
			SymbolSignature::Func(sig) => match sig {
				FuncSignature::Vector => {
					// TODO: hint to the definition of this function
					return Err(ErrorKind::IllegalVectorCall.err(symbol_span));
				}
				FuncSignature::Proc { inputs, outputs } => {
					// Check function inputs
					let iter = inputs.iter();
					self.ws
						.compare(iter, StackMatch::Tail, false, symbol_span)?;

					// Push function outputs
					for output in outputs.iter() {
						self.ws.push((output.clone(), symbol_span));
					}

					todo!("generate ops");
				}
			},
			// Variable load
			SymbolSignature::Var(sig) => {
				self.ws.push((sig.typ.clone(), symbol_span));
				todo!("generate ops");
			}
			// Constant use
			SymbolSignature::Const(sig) => {
				self.ws.push((sig.typ.clone(), symbol_span));
				todo!("generate ops");
			}
			// Data load
			SymbolSignature::Data => {
				self.ws.push((Type::Byte, symbol_span));
				todo!("generate ops");
			}
		};

		Ok(())
	}
	fn check_ptr_to(&mut self, name: &Name, symbol_span: Span) -> error::Result<()> {
		let Some(symbol) = self.symbols.get(name) else {
			return Err(ErrorKind::UnknownSymbol.err(symbol_span));
		};

		let output = match &symbol.signature {
			SymbolSignature::Func(sig) => {
				let typ = Type::FuncPtr(sig.clone());
				todo!("generate ops");
			}
			SymbolSignature::Var(sig) => {
				let typ = Type::BytePtr(sig.typ.clone().into());
				todo!("generate ops");
			}
			SymbolSignature::Data => {
				let typ = Type::ShortPtr(Type::Byte.into());
				todo!("generate ops");
			}

			// TODO: hint to the definition of this const
			SymbolSignature::Const(_) => {
				// TODO: hint to the definition of this constant
				return Err(ErrorKind::IllegalPtrToConst.err(symbol_span));
			}
		};

		self.ws.push((output, symbol_span));

		Ok(())
	}

	pub fn check_def(&mut self, def: &mut Def, def_span: Span) -> error::Result<()> {
		match def {
			Def::Var(_) => (/* ignore */),

			Def::Func(def) => {
				self.reset();

				// Push function inputs onto the stack
				if let FuncArgs::Proc { inputs, .. } = &def.args {
					for input in inputs.iter() {
						self.ws.push((input.x.clone(), input.span));
					}
				}

				// Check function body
				self.check_nodes(&mut def.body)?;

				// Compare body output stack with expected function outputs
				match &def.args {
					FuncArgs::Vector => {
						if self.ws.len() > 0 {
							// TODO: hint to the expressions that caused this error
							return Err(ErrorKind::VectorNonEmptyStack.err(def_span));
						}
					}
					FuncArgs::Proc { outputs, .. } => {
						let iter = outputs.iter().map(|t| &t.x);
						self.ws.compare(iter, StackMatch::Exact, false, def_span)?;
					}
				}
			}

			Def::Const(def) => {
				self.reset();
				self.check_nodes(&mut def.body)?;
				self.ws.compare(
					std::iter::once(&def.typ.x),
					StackMatch::Exact,
					false,
					def_span,
				)?;
			}

			Def::Data(def) => {
				for node in def.body.iter() {
					match node.x {
						Node::Expr(Expr::Byte(_))
						| Node::Expr(Expr::Short(_))
						| Node::Expr(Expr::String(_))
						| Node::Expr(Expr::Padding(_)) => (),
						_ => return Err(ErrorKind::NoDataCodeEvaluationYet.err(node.span)),
					}
				}
			}
		}

		Ok(())
	}

	// ==============================
	// Intrinsic typechecking
	// ==============================

	pub fn check_intrinsic(
		&mut self,
		intr: &mut Intrinsic,
		mode: &mut IntrMode,
		intr_span: Span,
	) -> error::Result<()> {
		let keep = mode.contains(IntrMode::KEEP);

		match intr {
			Intrinsic::Add | Intrinsic::Sub | Intrinsic::Mul | Intrinsic::Div => {
				// ( a b -- a+b )
				self.check_arithmetic_intr(mode, intr_span)?;
			}

			Intrinsic::Inc => {
				// ( a -- a+1 )
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() {
					todo!("set short mode");
				}
				self.ws.push((a.typ, intr_span));
			}

			Intrinsic::Shift => {
				// ( a shift8 -- c )
				let shift8 = self.ws.pop_err(keep, intr_span)?;
				let a = self.ws.pop_err(keep, intr_span)?;

				if shift8.typ != Type::Byte {
					// TODO: hint expected type
					return Err(ErrorKind::InvalidStackSignature.err(intr_span));
				}

				match a.typ {
					Type::Byte => self.ws.push((Type::Byte, intr_span)),
					Type::Short => {
						todo!("set short mode");
						self.ws.push((Type::Short, intr_span))
					}
					_ => {
						// TODO: hint expected type
						return Err(ErrorKind::InvalidStackSignature.err(intr_span));
					}
				}
			}
			Intrinsic::And | Intrinsic::Or | Intrinsic::Xor => {
				// ( a b -- c )
				let b = self.ws.pop_err(keep, intr_span)?;
				let a = self.ws.pop_err(keep, intr_span)?;

				let output = match (a.typ, b.typ) {
					(Type::Byte, Type::Byte) => Type::Byte,
					(Type::Short, Type::Short) => Type::Short,
					_ => {
						// TODO: hint expected types
						return Err(ErrorKind::UnmatchedInputs.err(intr_span));
					}
				};
				if output.is_short() {
					todo!("set short mode");
				}

				self.ws.push((output, intr_span));
			}

			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				// ( a b -- bool8 )
				let b = self.ws.pop_err(keep, intr_span)?;
				let a = self.ws.pop_err(keep, intr_span)?;
				let short = match (a.typ, b.typ) {
					(Type::Byte, Type::Byte) => false,
					(Type::Short, Type::Short) => true,
					// NOTE: we don't care what inner types are
					(Type::BytePtr(_), Type::BytePtr(_)) => false,
					(Type::ShortPtr(_), Type::ShortPtr(_)) => true,
					(Type::FuncPtr(_), Type::FuncPtr(_)) => true,
					_ => {
						// TODO: hint expected types
						return Err(ErrorKind::UnmatchedInputs.err(intr_span));
					}
				};

				if short {
					todo!("set short mode");
				}

				self.ws.push((Type::Byte, intr_span));
			}

			Intrinsic::Pop => {
				// ( a b -- a )
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() {
					todo!("set short mode");
				}
			}
			Intrinsic::Swap => {
				// ( a b -- b a )
				let b = self.ws.pop_err(keep, intr_span)?;
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() != b.typ.is_short() {
					// TODO: hint expected sizes
					return Err(ErrorKind::UnmatchedInputsSize.err(intr_span));
				}
				if a.typ.is_short() {
					todo!("set short mode");
				}
				self.ws.push(b);
				self.ws.push(a);
			}
			Intrinsic::Nip => {
				// ( a b -- b )
				let b = self.ws.pop_err(keep, intr_span)?;
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() != b.typ.is_short() {
					// TODO: hint expected sizes
					return Err(ErrorKind::UnmatchedInputsSize.err(intr_span));
				}
				if a.typ.is_short() {
					todo!("set short mode");
				}
				self.ws.push(b);
			}
			Intrinsic::Rot => {
				// ( a b c -- b c a )
				let c = self.ws.pop_err(keep, intr_span)?;
				let b = self.ws.pop_err(keep, intr_span)?;
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() != b.typ.is_short() || b.typ.is_short() != c.typ.is_short() {
					// TODO: hint expected sizes
					return Err(ErrorKind::UnmatchedInputsSize.err(intr_span));
				}
				if a.typ.is_short() {
					todo!("set short mode");
				}
				self.ws.push(b);
				self.ws.push(c);
				self.ws.push(a);
			}
			Intrinsic::Dup => {
				// ( a -- a a )
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() {
					todo!("set short mode");
				}
				self.ws.push(a.clone());
				self.ws.push((a.typ, intr_span));
			}
			Intrinsic::Over => {
				// ( a b -- a b a )
				let b = self.ws.pop_err(keep, intr_span)?;
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() != b.typ.is_short() {
					// TODO: hint expected sizes
					return Err(ErrorKind::UnmatchedInputsSize.err(intr_span));
				}
				if a.typ.is_short() {
					todo!("set short mode");
				}
				self.ws.push(a.clone());
				self.ws.push(b);
				self.ws.push((a.typ, intr_span));
			}

			Intrinsic::Load => {
				// ( addr -- value )
				let addr = self.ws.pop_err(keep, intr_span)?;
				let output = match addr.typ {
					Type::BytePtr(t) => {
						todo!("set addr kind");
						*t
					}
					Type::ShortPtr(t) => {
						todo!("set addr kind");
						*t
					}
					_ => {
						// TODO: hint expected type
						return Err(ErrorKind::InvalidStackSignature.err(intr_span));
					}
				};
				if output.is_short() {
					todo!("set short mode");
				}

				self.ws.push((output, intr_span));
			}
			Intrinsic::Store => {
				// ( value addr -- )
				let addr = self.ws.pop_err(keep, intr_span)?;
				let value = self.ws.pop_err(keep, intr_span)?;
				match addr.typ {
					Type::BytePtr(t) => {
						if *t == value.typ {
							todo!("set addr kind");
						} else {
							// TODO: hint expected type
							return Err(ErrorKind::InvalidStackSignature.err(intr_span));
						}
					}
					Type::ShortPtr(t) => {
						if *t == value.typ {
							todo!("set addr kind");
						} else {
							// TODO: hint expected type
							return Err(ErrorKind::InvalidStackSignature.err(intr_span));
						}
					}
					_ => {
						// TODO: hint expected type
						return Err(ErrorKind::InvalidStackSignature.err(intr_span));
					}
				}

				if value.typ.is_short() {
					todo!("set short mode");
				}
			}

			Intrinsic::Input | Intrinsic::Input2 => {
				// ( device8 -- value )
				let device8 = self.ws.pop_err(keep, intr_span)?;
				if device8.typ != Type::Byte {
					// TODO: hint expected type
					return Err(ErrorKind::InvalidStackSignature.err(intr_span));
				}

				if *intr == Intrinsic::Input2 {
					todo!("set short mode");
					self.ws.push((Type::Short, intr_span));
				} else {
					self.ws.push((Type::Byte, intr_span));
				}
			}
			Intrinsic::Output => {
				// ( val device8 -- )
				let device8 = self.ws.pop_err(keep, intr_span)?;
				let val = self.ws.pop_err(keep, intr_span)?;
				if device8.typ != Type::Byte {
					// TODO: hint expected type
					return Err(ErrorKind::InvalidStackSignature.err(intr_span));
				}

				if val.typ.is_short() {
					todo!("set short mode");
				}
			}
		}

		Ok(())
	}
	fn check_arithmetic_intr(&mut self, mode: &mut IntrMode, intr_span: Span) -> error::Result<()> {
		let keep = mode.contains(IntrMode::KEEP);
		let b = self.ws.pop_err(keep, intr_span)?;
		let a = self.ws.pop_err(keep, intr_span)?;

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
					// TODO: hint expected types
					return Err(ErrorKind::UnmatchedInputs.err(intr_span));
				}
			}
			(Type::ShortPtr(a), Type::ShortPtr(b)) => {
				if a == b {
					Type::ShortPtr(a)
				} else {
					// TODO: hint expected types
					return Err(ErrorKind::UnmatchedInputs.err(intr_span));
				}
			}
			(Type::FuncPtr(a), Type::FuncPtr(b)) => {
				if a == b {
					Type::FuncPtr(a)
				} else {
					// TODO: hint expected types
					return Err(ErrorKind::UnmatchedInputs.err(intr_span));
				}
			}

			_ => {
				// TODO: hint expected types
				return Err(ErrorKind::InvalidStackSignature.err(intr_span));
			}
		};

		if output.is_short() {
			todo!("set short mode");
		}

		self.ws.push((output, intr_span));

		Ok(())
	}

	// ==============================
	// Helper functions
	// ==============================

	/// Reset all stacks
	fn reset(&mut self) {
		self.ws.reset();
	}

	#[must_use]
	fn begin_block(&mut self) -> Vec<StackItem> {
		self.ws.take_snapshot()
	}
	fn end_block(&mut self, snapshot: Vec<StackItem>, span: Span) -> error::Result<()> {
		self.ws.compare_snapshot(snapshot, span)
	}
}
