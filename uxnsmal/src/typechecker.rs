use std::{borrow::Borrow, collections::HashMap, fmt::Debug};

use crate::{
	ast::{Ast, Def, Expr, FuncArgs, Node},
	error::{self, ErrorKind},
	lexer::{Span, Spanned},
	program::{
		Constant, Data, Function, IntrMode, Intrinsic, Op, Program, TypedIntrMode, Variable,
	},
	symbols::{FuncSignature, Label, Name, Symbol, SymbolSignature, Type, UniqueName},
};

/// Stack match
/// How stacks should be compared
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackMatch {
	/// Only tails of the comparable stacks must be equal
	Tail,
	/// Comparable stacks must be exactly the same
	Exact,
}

/// Stack item
#[derive(Clone, Eq)]
pub struct StackItem {
	pub typ: Type,
	/// Span of the operation that pushed this type onto the stack
	/// Used error reporting
	pub pushed_at: Span,
}
impl StackItem {
	pub fn new(typ: Type, pushed_at: Span) -> Self {
		Self { typ, pushed_at }
	}
}
impl PartialEq for StackItem {
	fn eq(&self, rhs: &Self) -> bool {
		self.typ == rhs.typ
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
impl Debug for StackItem {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "StackItem({:?}, {})", self.typ, self.pushed_at)
	}
}

/// Current scope stack snapshot
/// Unit struct to not forget to pop the snapshot
pub struct CurrentSnapshot;

/// Stack
#[derive(Debug)]
pub struct Stack {
	pub items: Vec<StackItem>,
	/// List of stack snapshots taken at each block start.
	/// Used to typecheck blocks.
	snapshots: Vec<Vec<StackItem>>,

	keep_cursor: usize,
}
impl Default for Stack {
	fn default() -> Self {
		Self {
			items: Vec::with_capacity(256),
			snapshots: Vec::with_capacity(16),

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
	pub fn take_snapshot(&mut self) -> CurrentSnapshot {
		let snapshot = self.items.clone();
		self.snapshots.push(snapshot);
		CurrentSnapshot
	}
	pub fn compare_snapshot(&mut self, snapshot: CurrentSnapshot, span: Span) -> error::Result<()> {
		let snapshot = self.pop_snapshot(snapshot);
		self.compare(snapshot, StackMatch::Exact, true, span)
	}
	pub fn pop_snapshot(&mut self, _snapshot: CurrentSnapshot) -> Vec<StackItem> {
		self.snapshots
			.pop()
			.expect("unexpected empty `snapshots` list")
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

/// Block depth
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Depth {
	TopLevel,
	Level(u32),
}

/// Typechecker
/// Performs type-checking of the specified AST and generates an intermediate representation
pub struct Typechecker {
	/// Working stack
	pub ws: Stack,

	program: Program,

	unique_name_id: u32,
	symbols: HashMap<Name, Symbol>,
	/// Table of labels accessible in the current scope.
	/// It is a separate table because labels have a separate namespace.
	labels: HashMap<Name, Label>,
}
impl Default for Typechecker {
	fn default() -> Self {
		Self {
			ws: Stack::default(),

			program: Program::default(),

			unique_name_id: 0,
			symbols: HashMap::with_capacity(128),
			labels: HashMap::with_capacity(32),
		}
	}
}
impl Typechecker {
	pub fn check(ast: Ast) -> error::Result<Program> {
		let mut checker = Self::default();

		checker.collect(&ast)?;
		checker.check_nodes(ast.nodes, Depth::TopLevel, &mut vec![])?;

		Ok(checker.program)
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

			self.define_symbol(def.name().clone(), def.to_signature(), node_span)?;
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
			Err(ErrorKind::SymbolRedefinition.err(span))
		} else {
			Ok(())
		}
	}
	fn get_or_define_symbol(
		&mut self,
		name: &Name,
		signature: impl FnOnce() -> SymbolSignature,
	) -> &Symbol {
		if !self.symbols.contains_key(name) {
			let symbol = Symbol::new(self.new_unique_name(), signature());
			self.symbols.insert(name.clone(), symbol);
		}

		// SAFETY: there always will be symbol with name == `name` because if there is not,
		// it will be defined above
		&self.symbols[name]
	}

	fn define_label(&mut self, name: Name, level: u32, span: Span) -> error::Result<UniqueName> {
		let unique_name = self.new_unique_name();
		let prev = self.labels.insert(name, Label::new(unique_name, level));
		if prev.is_some() {
			// TODO: hint to previosly defined label
			Err(ErrorKind::LabelRedefinition.err(span))
		} else {
			Ok(unique_name)
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

	// Clippy argues that i should remove `.to_owned()` and use `.iter().cloned()` instead, this
	// obviously is not possible and i am not sure if this is a bug of clippy or not
	#[allow(clippy::unnecessary_to_owned)]
	fn check_nodes<I>(&mut self, nodes: I, depth: Depth, ops: &mut Vec<Op>) -> error::Result<()>
	where
		I: ToOwned,
		I::Owned: IntoIterator<Item = Spanned<Node>>,
	{
		for node in nodes.to_owned() {
			self.check_node(node.x, node.span, depth, ops)?;
		}
		Ok(())
	}
	fn check_node(
		&mut self,
		node: Node,
		node_span: Span,
		depth: Depth,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		self.ws.keep_cursor = 0;

		match node {
			Node::Expr(expr) => self.check_expr(expr, node_span, depth, ops),
			Node::Def(def) => self.check_def(def, node_span, depth),
		}
	}
	pub fn check_expr(
		&mut self,
		expr: Expr,
		expr_span: Span,
		depth: Depth,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Depth::Level(level) = depth else {
			return Err(ErrorKind::IllegalTopLevelExpr.err(expr_span));
		};

		match expr {
			Expr::Byte(b) => {
				self.ws.push((Type::Byte, expr_span));
				ops.push(Op::Byte(b));
			}
			Expr::Short(s) => {
				self.ws.push((Type::Short, expr_span));
				ops.push(Op::Short(s));
			}
			Expr::String(s) => {
				self.ws.push((Type::ShortPtr(Type::Byte.into()), expr_span));

				let unique_name = self.new_unique_name();
				let data = Data {
					body: s.as_bytes().into(),
				};
				self.program.datas.insert(unique_name, data);

				ops.push(Op::AbsShortAddrOf(unique_name));
			}
			Expr::Padding(_) => {
				todo!("`Expr::Padding` outside 'data' blocks should error before typecheck stage");
			}

			Expr::Intrinsic(intr, mode) => self.check_intrinsic(intr, mode, expr_span, ops)?,
			Expr::Symbol(name) => self.check_symbol(name, expr_span, ops)?,
			Expr::PtrTo(name) => self.check_ptr_to(name, expr_span, ops)?,

			Expr::Block {
				looping: _,
				label,
				body,
			} => {
				let snapshot = self.begin_block();

				self.new_unique_name();
				let label_unique_name = self.define_label(label.x.clone(), level, label.span)?;
				self.check_nodes(body, Depth::Level(level + 1), ops)?;
				ops.push(Op::Label(label_unique_name));
				self.undefine_label(&label.x);

				self.end_block(snapshot, expr_span)?;
			}

			Expr::Jump { label, conditional } => {
				let Some(block_label) = self.labels.get(&label.x).cloned() else {
					return Err(ErrorKind::UnknownLabel.err(label.span));
				};

				// If we jump out of a parenting block we need to ensure that stack signature before
				// this jump is equal to the expected stack of the block we want to jump out
				if level >= 1 && block_label.depth < level - 1 {
					// FIXME: it is better not to clone the snapshot
					let snapshot = self.ws.snapshots[block_label.depth as usize].clone();
					self.ws
						.compare(snapshot, StackMatch::Exact, true, expr_span)?;
				}

				if conditional {
					let bool8 = self.ws.pop_err(false, expr_span)?;
					if bool8.typ != Type::Byte {
						// TODO: hint expected type
						return Err(ErrorKind::InvalidStackSignature.err(expr_span));
					}
				}

				if conditional {
					ops.push(Op::JumpIf(block_label.unique_name));
				} else {
					ops.push(Op::Jump(block_label.unique_name));
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

					let if_begin_label = self.new_unique_name();
					let end_label = self.new_unique_name();

					ops.push(Op::JumpIf(if_begin_label));

					// 'else' block
					let snapshot = self.begin_block();
					self.check_nodes(else_body, Depth::Level(level + 1), ops)?;
					ops.push(Op::Jump(end_label));

					// Take snapshot of the stack at the end of 'else' block
					let restored = self.ws.pop_snapshot(snapshot);
					let else_snapshot = self.begin_block();
					// Restore the stack to the state before 'else' block
					self.ws.items = restored;

					// 'if' block
					ops.push(Op::Label(if_begin_label));
					self.check_nodes(if_body, Depth::Level(level + 1), ops)?;
					ops.push(Op::Label(end_label));
					// Stack at the end of 'else' block and 'if' block must be equal
					self.end_block(else_snapshot, expr_span)?;
				} else {
					let if_begin_label = self.new_unique_name();
					let end_label = self.new_unique_name();

					// Single 'if'
					let snapshot = self.begin_block();

					ops.push(Op::JumpIf(if_begin_label));
					ops.push(Op::Jump(end_label));
					ops.push(Op::Label(if_begin_label));
					self.check_nodes(if_body, Depth::Level(level + 1), ops)?;
					ops.push(Op::Label(end_label));

					self.end_block(snapshot, expr_span)?;
				}
			}

			Expr::While { condition, body } => {
				let again_label = self.new_unique_name();
				let continue_label = self.new_unique_name();
				let end_label = self.new_unique_name();

				let snapshot = self.begin_block();

				ops.push(Op::Label(again_label));

				// TODO: check condition to NOT consume items outside itself
				self.check_nodes(condition, Depth::Level(level + 1), ops)?;
				ops.push(Op::JumpIf(continue_label));
				ops.push(Op::Jump(end_label));
				ops.push(Op::Label(continue_label));

				let a = self.ws.pop_err(false, expr_span)?;
				if a.typ != Type::Byte {
					// TODO: hint expected type
					return Err(ErrorKind::InvalidConditionOutput.err(expr_span));
				}

				self.check_nodes(body, Depth::Level(level + 1), ops)?;
				ops.push(Op::Jump(again_label));
				ops.push(Op::Label(end_label));

				self.end_block(snapshot, expr_span)?;
			}
		}

		Ok(())
	}

	fn check_symbol(
		&mut self,
		name: Name,
		symbol_span: Span,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.get(&name) else {
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

					ops.push(Op::FuncCall(symbol.unique_name));
				}
			},
			// Variable load
			SymbolSignature::Var(sig) => {
				self.ws.push((sig.typ.clone(), symbol_span));

				let mut mode = TypedIntrMode::ABS_BYTE_ADDR;
				if sig.typ.is_short() {
					mode |= TypedIntrMode::SHORT;
				}
				ops.push(Op::AbsByteAddrOf(symbol.unique_name));
				ops.push(Op::Intrinsic(Intrinsic::Load, mode));
			}
			// Constant use
			SymbolSignature::Const(sig) => {
				self.ws.push((sig.typ.clone(), symbol_span));
				ops.push(Op::ConstUse(symbol.unique_name));
			}
			// Data load
			SymbolSignature::Data => {
				self.ws.push((Type::Byte, symbol_span));

				ops.push(Op::AbsShortAddrOf(symbol.unique_name));
				ops.push(Op::Intrinsic(
					Intrinsic::Load,
					TypedIntrMode::ABS_SHORT_ADDR,
				));
			}
		};

		Ok(())
	}
	fn check_ptr_to(
		&mut self,
		name: Name,
		symbol_span: Span,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.get(&name) else {
			return Err(ErrorKind::UnknownSymbol.err(symbol_span));
		};

		match &symbol.signature {
			SymbolSignature::Func(sig) => {
				let typ = Type::FuncPtr(sig.clone());
				self.ws.push((typ, symbol_span));

				ops.push(Op::AbsShortAddrOf(symbol.unique_name));
			}
			SymbolSignature::Var(sig) => {
				let typ = Type::BytePtr(sig.typ.clone().into());
				self.ws.push((typ, symbol_span));

				ops.push(Op::AbsByteAddrOf(symbol.unique_name));
			}
			SymbolSignature::Data => {
				let typ = Type::ShortPtr(Type::Byte.into());
				self.ws.push((typ, symbol_span));

				ops.push(Op::AbsShortAddrOf(symbol.unique_name));
			}

			SymbolSignature::Const(_) => {
				// TODO: hint to the definition of this constant
				return Err(ErrorKind::IllegalPtrToConst.err(symbol_span));
			}
		};

		Ok(())
	}

	pub fn check_def(&mut self, def: Def, def_span: Span, depth: Depth) -> error::Result<()> {
		if depth != Depth::TopLevel {
			return Err(ErrorKind::NoLocalDefsYet.err(def_span));
		}

		let symbol = self.get_or_define_symbol(def.name(), || def.to_signature());
		let unique_name = symbol.unique_name;

		match def {
			Def::Var(def) => {
				self.program.vars.insert(
					unique_name,
					Variable {
						size: def.typ.x.size(),
					},
				);
			}

			Def::Func(def) => {
				self.reset();

				// Push function inputs onto the stack
				if let FuncArgs::Proc { inputs, .. } = &def.args {
					for input in inputs.iter() {
						self.ws.push((input.x.clone(), input.span));
					}
				}

				// Check function body
				let mut ops = Vec::with_capacity(64);
				self.check_nodes(def.body, Depth::Level(0), &mut ops)?;

				// Compare body output stack with expected function outputs
				match &def.args {
					FuncArgs::Vector => {
						if !self.ws.is_empty() {
							// TODO: hint to the expressions that caused this error
							return Err(ErrorKind::VectorNonEmptyStack.err(def_span));
						}
					}
					FuncArgs::Proc { outputs, .. } => {
						let iter = outputs.iter().map(|t| &t.x);
						self.ws.compare(iter, StackMatch::Exact, false, def_span)?;
					}
				}

				let func = Function {
					is_vector: matches!(def.args, FuncArgs::Vector),
					body: ops.into(),
				};
				if def.name.as_ref() == "on-reset" {
					self.program.reset_func = Some((unique_name, func));
				} else {
					self.program.funcs.insert(unique_name, func);
				}
			}

			Def::Const(def) => {
				self.reset();

				let mut ops = Vec::with_capacity(32);
				self.check_nodes(def.body, Depth::Level(0), &mut ops)?;

				self.ws.compare(
					std::iter::once(&def.typ.x),
					StackMatch::Exact,
					false,
					def_span,
				)?;

				let cnst = Constant { body: ops.into() };
				self.program.consts.insert(unique_name, cnst);
			}

			Def::Data(def) => {
				let mut bytes = Vec::with_capacity(64);

				for node in def.body {
					match node.x {
						Node::Expr(Expr::Byte(b)) => {
							bytes.push(b);
						}
						Node::Expr(Expr::Short(s)) => {
							let a = ((s & 0xFF00) >> 8) as u8;
							let b = (s & 0x00FF) as u8;
							bytes.push(a);
							bytes.push(b);
						}
						Node::Expr(Expr::String(b)) => {
							bytes.extend(b.as_bytes());
						}
						Node::Expr(Expr::Padding(p)) => {
							bytes.extend(std::iter::repeat_n(0, p as usize));
						}
						_ => return Err(ErrorKind::NoDataCodeEvaluationYet.err(node.span)),
					}
				}

				let data = Data { body: bytes.into() };
				self.program.datas.insert(unique_name, data);
			}
		}

		Ok(())
	}

	// ==============================
	// Intrinsic typechecking
	// ==============================

	pub fn check_intrinsic(
		&mut self,
		intr: Intrinsic,
		mode: IntrMode,
		intr_span: Span,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let keep = mode.contains(IntrMode::KEEP);
		let mut typed_mode = TypedIntrMode::from(mode);

		match intr {
			Intrinsic::Add | Intrinsic::Sub | Intrinsic::Mul | Intrinsic::Div => {
				// ( a b -- a+b )
				typed_mode |= self.check_arithmetic_intr(mode, intr_span)?;
			}

			Intrinsic::Inc => {
				// ( a -- a+1 )
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() {
					typed_mode |= TypedIntrMode::SHORT;
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
						self.ws.push((Type::Short, intr_span));
						typed_mode |= TypedIntrMode::SHORT;
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
					typed_mode |= TypedIntrMode::SHORT;
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
					typed_mode |= TypedIntrMode::SHORT;
				}

				self.ws.push((Type::Byte, intr_span));
			}

			Intrinsic::Pop => {
				// ( a b -- a )
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() {
					typed_mode |= TypedIntrMode::SHORT;
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
					typed_mode |= TypedIntrMode::SHORT;
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
					typed_mode |= TypedIntrMode::SHORT;
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
					typed_mode |= TypedIntrMode::SHORT;
				}
				self.ws.push(b);
				self.ws.push(c);
				self.ws.push(a);
			}
			Intrinsic::Dup => {
				// ( a -- a a )
				let a = self.ws.pop_err(keep, intr_span)?;
				if a.typ.is_short() {
					typed_mode |= TypedIntrMode::SHORT;
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
					typed_mode |= TypedIntrMode::SHORT;
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
						typed_mode |= TypedIntrMode::ABS_BYTE_ADDR;
						*t
					}
					Type::ShortPtr(t) => {
						typed_mode |= TypedIntrMode::ABS_SHORT_ADDR;
						*t
					}
					_ => {
						// TODO: hint expected type
						return Err(ErrorKind::InvalidStackSignature.err(intr_span));
					}
				};
				if output.is_short() {
					typed_mode |= TypedIntrMode::SHORT;
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
							typed_mode |= TypedIntrMode::ABS_BYTE_ADDR;
						} else {
							// TODO: hint expected type
							return Err(ErrorKind::InvalidStackSignature.err(intr_span));
						}
					}
					Type::ShortPtr(t) => {
						if *t == value.typ {
							typed_mode |= TypedIntrMode::ABS_SHORT_ADDR;
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
					typed_mode |= TypedIntrMode::SHORT;
				}
			}

			Intrinsic::Input | Intrinsic::Input2 => {
				// ( device8 -- value )
				let device8 = self.ws.pop_err(keep, intr_span)?;
				if device8.typ != Type::Byte {
					// TODO: hint expected type
					return Err(ErrorKind::InvalidStackSignature.err(intr_span));
				}

				if intr == Intrinsic::Input2 {
					self.ws.push((Type::Short, intr_span));
					typed_mode |= TypedIntrMode::SHORT;
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
					typed_mode |= TypedIntrMode::SHORT;
				}
			}
		}

		ops.push(Op::Intrinsic(intr, typed_mode));

		Ok(())
	}
	fn check_arithmetic_intr(
		&mut self,
		mode: IntrMode,
		intr_span: Span,
	) -> error::Result<TypedIntrMode> {
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
		let is_short = output.is_short();

		self.ws.push((output, intr_span));

		if is_short {
			Ok(TypedIntrMode::SHORT)
		} else {
			Ok(TypedIntrMode::NONE)
		}
	}

	// ==============================
	// Helper functions
	// ==============================

	/// Reset all stacks
	fn reset(&mut self) {
		self.ws.reset();
	}

	#[must_use]
	fn begin_block(&mut self) -> CurrentSnapshot {
		self.ws.take_snapshot()
	}
	fn end_block(&mut self, snapshot: CurrentSnapshot, span: Span) -> error::Result<()> {
		self.ws.compare_snapshot(snapshot, span)
	}
}
