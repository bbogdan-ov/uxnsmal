mod consumer;
mod stack;

pub use consumer::*;
pub use stack::*;

use crate::{
	ast::{Ast, Def, Expr, FuncArgs, Node},
	error::{self, Error},
	lexer::{Span, Spanned},
	program::{Constant, Data, Function, IntrMode, Intrinsic, Op, Program, Variable},
	symbols::{FuncSignature, Name, SymbolSignature, SymbolsTable, Type},
};

/// Current scope
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
	TopLevel,
	Block {
		/// Whether the following operations in the current scope will never be executed.
		/// For example any operations after `jump` or `return` (which set this flag to true) will
		/// never be executed.
		is_dead_code: bool,
	},
}
impl Scope {
	pub fn block() -> Self {
		Self::Block {
			is_dead_code: false,
		}
	}
}

/// Typechecker
/// Performs type-checking of the specified AST and generates an intermediate representation
pub struct Typechecker {
	pub symbols: SymbolsTable,

	program: Program,

	/// Working stack
	pub ws: Stack,
	/// Returns stack
	pub rs: Stack,
}
impl Default for Typechecker {
	fn default() -> Self {
		Self {
			symbols: SymbolsTable::default(),

			program: Program::default(),

			ws: Stack::default(),
			rs: Stack::default(),
		}
	}
}
impl Typechecker {
	pub fn check(ast: &Ast) -> error::Result<Program> {
		let mut checker = Self::default();
		checker.symbols.collect(ast)?;
		checker.check_nodes(&ast.nodes, &mut Scope::TopLevel, &mut vec![])?;

		Ok(checker.program)
	}

	fn check_nodes(
		&mut self,
		nodes: &[Spanned<Node>],
		scope: &mut Scope,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		for node in nodes.iter() {
			self.check_node(&node.x, node.span, scope, ops)?;
		}
		Ok(())
	}
	fn check_node(
		&mut self,
		node: &Node,
		node_span: Span,
		scope: &mut Scope,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		match node {
			Node::Expr(expr) => self.check_expr(expr, node_span, scope, ops),
			Node::Def(def) => self.check_def(def, node_span, *scope),
		}
	}
	pub fn check_expr(
		&mut self,
		expr: &Expr,
		expr_span: Span,
		scope: &mut Scope,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Scope::Block { is_dead_code } = scope else {
			return Err(Error::IllegalTopLevelExpr(expr_span));
		};

		if *is_dead_code {
			// TODO: issue a warning instead of printing into the console
			println!("Dead code at {expr_span}");
			return Ok(());
		}

		match expr {
			Expr::Byte(b) => {
				self.ws.push((Type::Byte, expr_span));
				ops.push(Op::Byte(*b));
			}
			Expr::Short(s) => {
				self.ws.push((Type::Short, expr_span));
				ops.push(Op::Short(*s));
			}
			Expr::String(s) => {
				self.ws.push((Type::ShortPtr(Type::Byte.into()), expr_span));

				// Generate IR
				// Insert an unique data for each string literal even if strings contents are the same
				let unique_name = self.symbols.new_unique_name();
				let body = s.as_bytes().into();
				self.program.datas.insert(unique_name, Data { body });

				ops.push(Op::AbsShortAddrOf(unique_name));
			}
			Expr::Padding(_) => {
				todo!("`Expr::Padding` outside 'data' blocks should error before typecheck stage");
			}

			Expr::Intrinsic(intr, mode) => {
				let mut mode = *mode;
				mode |= self.check_intrinsic(*intr, mode, expr_span)?;

				// Generate IR
				ops.push(Op::Intrinsic(*intr, mode))
			}
			Expr::Symbol(name) => self.check_symbol(name, expr_span, ops)?,
			Expr::PtrTo(name) => self.check_ptr_to(name, expr_span, ops)?,

			Expr::Block {
				looping: _,
				label,
				body,
			} => {
				let snapshot_idx = self.take_stacks_snapshot();

				let name = label.x.clone();
				let unique_name = self.symbols.define_label(name, snapshot_idx, label.span)?;

				let mut body_scope = Scope::block();
				self.check_nodes(body, &mut body_scope, ops)?;
				ops.push(Op::Label(unique_name));

				self.symbols.undefine_label(&label.x);

				self.compare_stacks_snapshots(expr_span)?;
			}

			Expr::Jump { label, conditional } => {
				let Some(block_label) = self.symbols.labels.get(&label.x).cloned() else {
					return Err(Error::UnknownLabel(label.span));
				};

				// FIXME: it is better not to clone the snapshot
				let snapshot = self.ws.snapshots[block_label.snapshot_idx].clone();
				self.ws
					.consumer_keep(expr_span)
					.compare(&snapshot, StackMatch::Exact)?;

				if *conditional {
					let bool8 = self.ws.pop_one(false, expr_span)?;
					if bool8.typ != Type::Byte {
						return Err(Error::InvalidIfInput(expr_span));
					}

					ops.push(Op::JumpIf(block_label.unique_name));
				} else {
					*is_dead_code = true;
					ops.push(Op::Jump(block_label.unique_name));
				}
			}

			Expr::If { if_body, else_body } => {
				// Check input condition
				let bool8 = self.ws.pop_one(false, expr_span)?;
				if bool8.typ != Type::Byte {
					return Err(Error::InvalidIfInput(expr_span));
				}

				if let Some(else_body) = else_body {
					// If-else chain
					// Code below may be a bit confusing

					let if_begin_label = self.symbols.new_unique_name();
					let end_label = self.symbols.new_unique_name();

					// Take snapshot before the `else` block
					self.take_stacks_snapshot();

					ops.push(Op::JumpIf(if_begin_label));

					// `else` block
					let mut else_scope = Scope::block();
					self.check_nodes(else_body, &mut else_scope, ops)?;
					ops.push(Op::Jump(end_label));

					let before_else_ws = self.ws.pop_snapshot();
					let before_else_rs = self.rs.pop_snapshot();

					// Take snapshot of the stacks at the end of the `else` block
					self.take_stacks_snapshot();

					// Restore the stacks to the state before the `else` block
					self.ws.items = before_else_ws;
					self.rs.items = before_else_rs;

					// `if` block
					ops.push(Op::Label(if_begin_label));
					let mut if_scope = Scope::block();
					self.check_nodes(if_body, &mut if_scope, ops)?;
					ops.push(Op::Label(end_label));

					// Compare stacks at the end of the `if` and `else` blocks to be equal
					self.compare_stacks_snapshots(expr_span)?;
				} else {
					// Single `if`
					let if_begin_label = self.symbols.new_unique_name();
					let end_label = self.symbols.new_unique_name();

					self.take_stacks_snapshot();

					ops.push(Op::JumpIf(if_begin_label));
					ops.push(Op::Jump(end_label));
					ops.push(Op::Label(if_begin_label));

					let mut if_scope = Scope::block();
					self.check_nodes(if_body, &mut if_scope, ops)?;

					ops.push(Op::Label(end_label));

					self.compare_stacks_snapshots(expr_span)?;
				}
			}

			Expr::While { condition, body } => {
				let again_label = self.symbols.new_unique_name();
				let continue_label = self.symbols.new_unique_name();
				let end_label = self.symbols.new_unique_name();

				self.take_stacks_snapshot();

				ops.push(Op::Label(again_label));

				{
					// Condition
					// TODO: check condition to NOT consume items outside itself
					let mut cond_scope = Scope::block();
					self.check_nodes(condition, &mut cond_scope, ops)?;
					let a = self.ws.pop_one(false, expr_span)?;
					if a.typ != Type::Byte {
						return Err(Error::InvalidWhileConditionOutput(expr_span));
					}

					ops.push(Op::JumpIf(continue_label));
					ops.push(Op::Jump(end_label));
					ops.push(Op::Label(continue_label));
				}

				// Body
				let mut body_scope = Scope::block();
				self.check_nodes(body, &mut body_scope, ops)?;

				ops.push(Op::Jump(again_label));
				ops.push(Op::Label(end_label));

				self.compare_stacks_snapshots(expr_span)?;
			}
		}

		Ok(())
	}

	fn check_symbol(
		&mut self,
		name: &Name,
		symbol_span: Span,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.table.get(name) else {
			return Err(Error::UnknownSymbol(symbol_span));
		};

		match &symbol.signature {
			SymbolSignature::Func(sig) => match sig {
				FuncSignature::Vector => {
					return Err(Error::IllegalVectorCall {
						defined_at: symbol.span,
						span: symbol_span,
					});
				}
				FuncSignature::Proc { inputs, outputs } => {
					// Check function inputs
					self.ws
						.consumer(symbol_span)
						.compare(inputs, StackMatch::Tail)?;

					// Push function outputs
					for output in outputs.iter() {
						self.ws.push((output.clone(), symbol_span));
					}

					// Generate IR
					ops.push(Op::FuncCall(symbol.unique_name));
				}
			},

			SymbolSignature::Var(sig) => {
				// Type check
				self.ws.push((sig.typ.clone(), symbol_span));

				// Generate IR
				let mut mode = IntrMode::ABS_BYTE_ADDR;
				if sig.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
				ops.push(Op::AbsByteAddrOf(symbol.unique_name));
				ops.push(Op::Intrinsic(Intrinsic::Load, mode));
			}
			SymbolSignature::Const(sig) => {
				// Type check
				self.ws.push((sig.typ.clone(), symbol_span));

				// Generate IR
				ops.push(Op::ConstUse(symbol.unique_name));
			}
			SymbolSignature::Data => {
				// Type check
				self.ws.push((Type::Byte, symbol_span));

				// Generate IR
				ops.push(Op::AbsShortAddrOf(symbol.unique_name));
				ops.push(Op::Intrinsic(Intrinsic::Load, IntrMode::ABS_SHORT_ADDR));
			}
		};

		Ok(())
	}
	fn check_ptr_to(
		&mut self,
		name: &Name,
		symbol_span: Span,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.table.get(name) else {
			return Err(Error::UnknownSymbol(symbol_span));
		};

		match &symbol.signature {
			SymbolSignature::Func(sig) => {
				// Type check
				let typ = Type::FuncPtr(sig.clone());
				self.ws.push((typ, symbol_span));

				// Generate IR
				ops.push(Op::AbsShortAddrOf(symbol.unique_name));
			}
			SymbolSignature::Var(sig) => {
				// Type check
				let typ = Type::BytePtr(sig.typ.clone().into());
				self.ws.push((typ, symbol_span));

				// Generate IR
				ops.push(Op::AbsByteAddrOf(symbol.unique_name));
			}
			SymbolSignature::Data => {
				// Type check
				let typ = Type::ShortPtr(Type::Byte.into());
				self.ws.push((typ, symbol_span));

				// Generate IR
				ops.push(Op::AbsShortAddrOf(symbol.unique_name));
			}

			SymbolSignature::Const(_) => {
				return Err(Error::IllegalPtrToConst {
					defined_at: symbol_span,
					span: symbol_span,
				});
			}
		};

		Ok(())
	}

	pub fn check_def(&mut self, def: &Def, def_span: Span, scope: Scope) -> error::Result<()> {
		if scope != Scope::TopLevel {
			return Err(Error::NoLocalDefsYet(def_span));
		}

		self.reset_stacks();

		let symbol = self
			.symbols
			.get_or_define_symbol(def.name(), || def.to_signature(), def_span);
		let unique_name = symbol.unique_name;

		match def {
			Def::Func(def) => {
				// Push function inputs onto the stack
				if let FuncArgs::Proc { inputs, .. } = &def.args {
					for input in inputs.iter() {
						self.ws.push((input.x.clone(), input.span));
					}
				}

				// Check function body
				let mut ops = Vec::with_capacity(64);
				let mut body_scope = Scope::block();
				self.check_nodes(&def.body, &mut body_scope, &mut ops)?;

				// Compare body output stack with expected function outputs
				match &def.args {
					FuncArgs::Vector => {
						if !self.ws.is_empty() {
							return Err(Error::NonEmptyStackInVecFunc {
								caused_by: self.ws.too_many_items(0),
								span: def_span,
							});
						}
					}
					FuncArgs::Proc { outputs, .. } => {
						self.ws
							.consumer(def_span)
							.compare(outputs, StackMatch::Exact)?;
					}
				}

				// Generate IR
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

			Def::Var(def) => {
				// Generate IR
				let var = Variable {
					size: def.typ.x.size(),
				};
				self.program.vars.insert(unique_name, var);
			}

			Def::Const(def) => {
				// Type check
				let mut ops = Vec::with_capacity(32);
				let mut body_scope = Scope::block();
				self.check_nodes(&def.body, &mut body_scope, &mut ops)?;

				self.ws
					.consumer(def_span)
					.compare(std::slice::from_ref(&def.typ.x), StackMatch::Exact)?;

				// Generate IR
				let cnst = Constant { body: ops.into() };
				self.program.consts.insert(unique_name, cnst);
			}

			Def::Data(def) => {
				// Generate IR
				let mut bytes = Vec::with_capacity(64);

				for node in def.body.iter() {
					match &node.x {
						Node::Expr(Expr::Byte(b)) => {
							bytes.push(*b);
						}
						Node::Expr(Expr::Short(s)) => {
							let a = ((*s & 0xFF00) >> 8) as u8;
							let b = (*s & 0x00FF) as u8;
							bytes.push(a);
							bytes.push(b);
						}
						Node::Expr(Expr::String(b)) => {
							bytes.extend(b.as_bytes());
						}
						Node::Expr(Expr::Padding(p)) => {
							bytes.extend(std::iter::repeat_n(0, *p as usize));
						}
						e => panic!(
							"unexpected expression inside data block {e:?} at {}",
							node.span
						),
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

	#[must_use]
	pub fn check_intrinsic(
		&mut self,
		intr: Intrinsic,
		mut mode: IntrMode,
		intr_span: Span,
	) -> error::Result<IntrMode> {
		let keep = mode.contains(IntrMode::KEEP);

		let (primary_stack, secondary_stack) = if mode.contains(IntrMode::RETURN) {
			(&mut self.rs, &mut self.ws)
		} else {
			(&mut self.ws, &mut self.rs)
		};

		match intr {
			Intrinsic::Add | Intrinsic::Sub | Intrinsic::Mul | Intrinsic::Div => {
				// ( a b -- a+b )
				mode |= self.check_arithmetic_intr(mode, intr_span)?;
			}

			Intrinsic::Inc => {
				// ( a -- a+1 )
				let a = primary_stack.pop_one(keep, intr_span)?;
				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
				primary_stack.push((a.typ, intr_span));
			}

			Intrinsic::Shift => {
				// ( a shift8 -- c )
				let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
				let shift8 = consumer.pop()?;
				let a = consumer.pop()?;

				if shift8.typ != Type::Byte {
					return Err(Error::InvalidShiftInput(intr_span));
				}

				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}

				primary_stack.push((a.typ, intr_span));
			}
			Intrinsic::And | Intrinsic::Or | Intrinsic::Xor => {
				// ( a b -- c )
				let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
				let b = consumer.pop()?;
				let a = consumer.pop()?;

				let output = match (a.typ, b.typ) {
					(Type::Byte, Type::Byte) => Type::Byte,
					(Type::Short, Type::Short) => Type::Short,
					_ => {
						// TODO: hint expected types
						return Err(Error::UnmatchedInputs { span: intr_span });
					}
				};
				if output.is_short() {
					mode |= IntrMode::SHORT;
				}

				primary_stack.push((output, intr_span));
			}

			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				// ( a b -- bool8 )
				let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
				let b = consumer.pop()?;
				let a = consumer.pop()?;
				let short = match (a.typ, b.typ) {
					(Type::Byte, Type::Byte) => false,
					(Type::Short, Type::Short) => true,
					// NOTE: we don't care what inner types are
					(Type::BytePtr(_), Type::BytePtr(_)) => false,
					(Type::ShortPtr(_), Type::ShortPtr(_)) => true,
					(Type::FuncPtr(_), Type::FuncPtr(_)) => true,
					_ => {
						// TODO: hint expected types
						return Err(Error::UnmatchedInputs { span: intr_span });
					}
				};

				if short {
					mode |= IntrMode::SHORT;
				}

				primary_stack.push((Type::Byte, intr_span));
			}

			Intrinsic::Pop => {
				// ( a b -- a )
				let a = primary_stack.pop_one(keep, intr_span)?;
				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
			}
			Intrinsic::Swap => {
				// ( a b -- b a )
				let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
				let b = consumer.pop()?;
				let a = consumer.pop()?;
				if a.typ.is_short() != b.typ.is_short() {
					// TODO: hint expected sizes
					return Err(Error::UnmatchedInputSizes { span: intr_span });
				}
				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
				primary_stack.push(b);
				primary_stack.push(a);
			}
			Intrinsic::Nip => {
				// ( a b -- b )
				let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
				let b = consumer.pop()?;
				let a = consumer.pop()?;
				if a.typ.is_short() != b.typ.is_short() {
					// TODO: hint expected sizes
					return Err(Error::UnmatchedInputSizes { span: intr_span });
				}
				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
				primary_stack.push(b);
			}
			Intrinsic::Rot => {
				// ( a b c -- b c a )
				let mut consumer = primary_stack.consumer_n(3, keep, intr_span);
				let c = consumer.pop()?;
				let b = consumer.pop()?;
				let a = consumer.pop()?;
				if a.typ.is_short() != b.typ.is_short() || b.typ.is_short() != c.typ.is_short() {
					// TODO: hint expected sizes
					return Err(Error::UnmatchedInputSizes { span: intr_span });
				}
				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
				primary_stack.push(b);
				primary_stack.push(c);
				primary_stack.push(a);
			}
			Intrinsic::Dup => {
				// ( a -- a a )
				let a = primary_stack.pop_one(keep, intr_span)?;
				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
				primary_stack.push(a.clone());
				primary_stack.push((a.typ, intr_span));
			}
			Intrinsic::Over => {
				// ( a b -- a b a )
				let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
				let b = consumer.pop()?;
				let a = consumer.pop()?;
				if a.typ.is_short() != b.typ.is_short() {
					// TODO: hint expected sizes
					return Err(Error::UnmatchedInputSizes { span: intr_span });
				}
				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
				primary_stack.push(a.clone());
				primary_stack.push(b);
				primary_stack.push((a.typ, intr_span));
			}
			Intrinsic::Sth => {
				let a = primary_stack.pop_one(keep, intr_span)?;
				if a.typ.size() > 2 {
					return Err(Error::InputsSizeIsTooLarge { span: intr_span });
				}
				if a.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
				secondary_stack.push(a);
			}

			Intrinsic::Load => {
				// ( addr -- value )
				let addr = primary_stack.pop_one(keep, intr_span)?;
				let output = match addr.typ {
					Type::BytePtr(t) => {
						mode |= IntrMode::ABS_BYTE_ADDR;
						*t
					}
					Type::ShortPtr(t) => {
						mode |= IntrMode::ABS_SHORT_ADDR;
						*t
					}
					_ => return Err(Error::InvalidAddrInputType(intr_span)),
				};
				if output.is_short() {
					mode |= IntrMode::SHORT;
				}

				primary_stack.push((output, intr_span));
			}
			Intrinsic::Store => {
				// ( value addr -- )
				let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
				let addr = consumer.pop()?;
				let value = consumer.pop()?;
				match addr.typ {
					Type::BytePtr(t) => {
						if *t == value.typ {
							mode |= IntrMode::ABS_BYTE_ADDR;
						} else {
							return Err(Error::UnmatchedInputs { span: intr_span });
						}
					}
					Type::ShortPtr(t) => {
						if *t == value.typ {
							mode |= IntrMode::ABS_SHORT_ADDR;
						} else {
							return Err(Error::UnmatchedInputs { span: intr_span });
						}
					}
					_ => return Err(Error::InvalidAddrInputType(intr_span)),
				}

				if value.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
			}

			Intrinsic::Input | Intrinsic::Input2 => {
				// ( device8 -- value )
				let device8 = primary_stack.pop_one(keep, intr_span)?;
				if device8.typ != Type::Byte {
					return Err(Error::InvalidDeviceInputType(intr_span));
				}

				if intr == Intrinsic::Input2 {
					primary_stack.push((Type::Short, intr_span));
					mode |= IntrMode::SHORT;
				} else {
					primary_stack.push((Type::Byte, intr_span));
				}
			}
			Intrinsic::Output => {
				// ( val device8 -- )
				let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
				let device8 = consumer.pop()?;
				let val = consumer.pop()?;
				if device8.typ != Type::Byte {
					return Err(Error::InvalidDeviceInputType(intr_span));
				}

				if val.typ.is_short() {
					mode |= IntrMode::SHORT;
				}
			}
		}

		Ok(mode)
	}
	#[must_use]
	fn check_arithmetic_intr(
		&mut self,
		mode: IntrMode,
		intr_span: Span,
	) -> error::Result<IntrMode> {
		let primary_stack = if mode.contains(IntrMode::RETURN) {
			&mut self.rs
		} else {
			&mut self.ws
		};

		let keep = mode.contains(IntrMode::KEEP);
		let mut consumer = primary_stack.consumer_n(2, keep, intr_span);
		let b = consumer.pop()?;
		let a = consumer.pop()?;

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
					return Err(Error::UnmatchedInputs { span: intr_span });
				}
			}
			(Type::ShortPtr(a), Type::ShortPtr(b)) => {
				if a == b {
					Type::ShortPtr(a)
				} else {
					// TODO: hint expected types
					return Err(Error::UnmatchedInputs { span: intr_span });
				}
			}
			(Type::FuncPtr(a), Type::FuncPtr(b)) => {
				if a == b {
					Type::FuncPtr(a)
				} else {
					// TODO: hint expected types
					return Err(Error::UnmatchedInputs { span: intr_span });
				}
			}

			_ => {
				return Err(Error::InvalidArithmeticInputTypes(intr_span));
			}
		};
		let is_short = output.is_short();

		primary_stack.push((output, intr_span));

		if is_short {
			Ok(mode | IntrMode::SHORT)
		} else {
			Ok(mode)
		}
	}

	// ==============================
	// Helper functions
	// ==============================

	pub fn reset_stacks(&mut self) {
		self.ws.reset();
		self.rs.reset();
	}

	pub fn take_stacks_snapshot(&mut self) -> usize {
		let ws_idx = self.ws.take_snapshot();
		let rs_idx = self.rs.take_snapshot();
		assert_eq!(ws_idx, rs_idx);
		ws_idx
	}
	pub fn compare_stacks_snapshots(&mut self, span: Span) -> error::Result<()> {
		self.ws.compare_snapshot(span)?;
		self.rs.compare_snapshot(span)
	}
}
