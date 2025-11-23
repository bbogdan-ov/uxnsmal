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

/// Block scope
/// I can also refer to it just as "block"
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope {
	/// Whether the following operations in this scope will never be executed.
	/// For example any operations after `jump` or `return` will never be executed.
	pub finished: bool,
	/// Whether the block scope can branch.
	// Branching blocks are blocks that can exit early.
	/// For example `if` and `while` block are branching blocks.
	pub branching: bool,

	/// Expected working stack at the end of the scope
	pub expected_ws: Vec<StackItem>,
	/// Expected return stack at the end of the scope
	pub expected_rs: Vec<StackItem>,
}
impl Scope {
	pub fn new(expected_ws: Vec<StackItem>, expected_rs: Vec<StackItem>) -> Self {
		Self {
			finished: false,
			branching: false,

			expected_ws,
			expected_rs,
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

	pub scopes: Vec<Scope>,
}
impl Default for Typechecker {
	fn default() -> Self {
		Self {
			symbols: SymbolsTable::default(),

			program: Program::default(),

			ws: Stack::default(),
			rs: Stack::default(),

			scopes: Vec::with_capacity(8),
		}
	}
}
impl Typechecker {
	pub fn check(ast: &Ast) -> error::Result<Program> {
		let mut checker = Self::default();
		checker.symbols.collect(ast)?;

		checker.check_nodes(&ast.nodes, None, &mut vec![])?;

		Ok(checker.program)
	}

	fn check_nodes(
		&mut self,
		nodes: &[Spanned<Node>],
		scope_idx: Option<usize>,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		for node in nodes.iter() {
			self.check_node(&node.x, node.span, scope_idx, ops)?;
		}
		Ok(())
	}
	fn check_node(
		&mut self,
		node: &Node,
		node_span: Span,
		scope_idx: Option<usize>,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		match node {
			Node::Expr(expr) => {
				let Some(scope_idx) = scope_idx else {
					return Err(Error::IllegalTopLevelExpr(node_span));
				};

				self.check_expr(expr, node_span, scope_idx, ops)
			}
			Node::Def(def) => self.check_def(def, node_span),
		}
	}
	pub fn check_expr(
		&mut self,
		expr: &Expr,
		expr_span: Span,
		cur_scope_idx: usize,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		if self.scopes[cur_scope_idx].finished {
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

			Expr::Block { label, body, .. } => {
				let scope_idx = self.begin_scope(false);

				let name = label.x.clone();
				let unique_name = self.symbols.define_label(name, scope_idx, label.span)?;

				self.check_nodes(body, Some(scope_idx), ops)?;
				ops.push(Op::Label(unique_name));

				self.end_scope(expr_span)?;
				self.symbols.undefine_label(&label.x);
			}

			Expr::Jump { label } => {
				let Some(block_label) = self.symbols.labels.get(&label.x).cloned() else {
					return Err(Error::UnknownLabel(label.span));
				};

				let jump_to_idx = block_label.scope_idx;
				let cur_scope = &mut self.scopes[cur_scope_idx];

				if cur_scope.branching {
					// Any ops below this `jump` and inside this scope will never be executed.
					// We don't mark pareting blocks as "finished" because this block may not
					// execute due being a branching block.
					cur_scope.finished = true;

					// Jumping from a branching block makes blocks from the current one to
					// `jump_to_idx`'th block branching as well
					self.scopes_propagate(jump_to_idx, |s| s.branching = true);
				} else {
					// `jump` in normal blocks will always execute, therefore making all ops below
					// it and inside `jump_to_idx`'th scope never execute
					self.scopes_propagate(jump_to_idx, |s| s.finished = true);
				}

				if self.scopes[jump_to_idx].branching {
					// Ensure that the current stack signature is equal to the expected one
					// of `jump_to_idx`'th block to prevent unexpected items on the stack if this
					// block exists early
					let block_scope = &self.scopes[jump_to_idx];
					self.ws
						.consumer_keep(expr_span)
						.compare(&block_scope.expected_ws, StackMatch::Exact)?;
					self.rs
						.consumer_keep(expr_span)
						.compare(&block_scope.expected_rs, StackMatch::Exact)?;
				}

				// Generate IR
				ops.push(Op::Jump(block_label.unique_name));
			}

			Expr::Return => {
				let cur_scope = &mut self.scopes[cur_scope_idx];

				if cur_scope.branching {
					cur_scope.finished = true;
				} else {
					self.scopes_propagate(0, |s| s.finished = true);
				}

				// Generate IR
				ops.push(Op::Return);

				if self.scopes[cur_scope_idx].branching {
					self.scopes_propagate(0, |s| s.branching = true);

					let block_scope = &self.scopes[0];
					self.ws
						.consumer_keep(expr_span)
						.compare(&block_scope.expected_ws, StackMatch::Exact)?;
					self.rs
						.consumer_keep(expr_span)
						.compare(&block_scope.expected_rs, StackMatch::Exact)?;
				}
			}

			Expr::If { if_body, else_body } => {
				// Check input condition
				let mut consumer = self.ws.consumer(expr_span);
				match consumer.pop() {
					Some(bool8) if bool8.typ == Type::Byte => (/* ok */),
					_ => {
						return Err(Error::InvalidConditionType {
							stack: consumer.stack_error(),
							span: expr_span,
						});
					}
				}

				if let Some(else_body) = else_body {
					// If-else chain
					// Code below may be a bit confusing

					let if_begin_label = self.symbols.new_unique_name();
					let end_label = self.symbols.new_unique_name();

					// Take snapshot before the `else` block
					let else_idx = self.begin_scope(true);

					ops.push(Op::JumpIf(if_begin_label));

					// `else` block
					self.check_nodes(else_body, Some(else_idx), ops)?;
					ops.push(Op::Jump(end_label));

					let before_else = self.pop_scope(expr_span);

					// Take snapshot of the stacks at the end of the `else` block
					let if_idx = self.begin_scope(true);

					// Restore the stacks to the state before the `else` block
					self.ws.items = before_else.expected_ws;
					self.rs.items = before_else.expected_rs;

					// `if` block
					ops.push(Op::Label(if_begin_label));
					self.check_nodes(if_body, Some(if_idx), ops)?;
					ops.push(Op::Label(end_label));

					// Compare stacks at the end of the `if` and `else` blocks to be equal
					self.end_scope(expr_span)?;
				} else {
					// Single `if`
					let if_begin_label = self.symbols.new_unique_name();
					let end_label = self.symbols.new_unique_name();

					let if_idx = self.begin_scope(true);

					ops.push(Op::JumpIf(if_begin_label));
					ops.push(Op::Jump(end_label));
					ops.push(Op::Label(if_begin_label));

					self.check_nodes(if_body, Some(if_idx), ops)?;

					ops.push(Op::Label(end_label));

					self.end_scope(expr_span)?;
				}
			}

			Expr::While { condition, body } => {
				let again_label = self.symbols.new_unique_name();
				let continue_label = self.symbols.new_unique_name();
				let end_label = self.symbols.new_unique_name();

				ops.push(Op::Label(again_label));

				{
					let cond_idx = self.begin_scope(false);

					// Condition
					// TODO: check condition to NOT consume items outside itself
					self.check_nodes(condition, Some(cond_idx), ops)?;

					let mut consumer = self.ws.consumer(expr_span);
					match consumer.pop() {
						Some(bool8) if bool8.typ == Type::Byte => (/* ok */),
						_ => {
							return Err(Error::InvalidConditionType {
								stack: consumer.stack_error(),
								span: expr_span,
							});
						}
					}

					ops.push(Op::JumpIf(continue_label));
					ops.push(Op::Jump(end_label));
					ops.push(Op::Label(continue_label));

					self.end_scope(expr_span)?;
				}

				let body_idx = self.begin_scope(true);

				// Body
				self.check_nodes(body, Some(body_idx), ops)?;

				ops.push(Op::Jump(again_label));
				ops.push(Op::Label(end_label));

				self.end_scope(expr_span)?;
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

	pub fn check_def(&mut self, def: &Def, def_span: Span) -> error::Result<()> {
		if self.scopes.len() > 0 {
			return Err(Error::NoLocalDefsYet(def_span));
		}

		self.reset_stacks();

		let symbol = self
			.symbols
			.get_or_define_symbol(def.name(), || def.to_signature(), def_span);
		let unique_name = symbol.unique_name;

		match def {
			Def::Func(def) => {
				let scope: Scope;

				match &def.args {
					FuncArgs::Vector => {
						scope = Scope::new(Vec::default(), Vec::default());
					}
					FuncArgs::Proc { inputs, outputs } => {
						let ws = outputs
							.iter()
							.map(|t| StackItem::new(t.x.clone(), t.span))
							.collect();

						scope = Scope::new(ws, Vec::default());

						// Push function inputs onto the stack
						for input in inputs.iter() {
							self.ws.push((input.x.clone(), input.span));
						}
					}
				}

				self.scopes.push(scope);

				// Check function body
				let mut ops = Vec::with_capacity(64);
				self.check_nodes(&def.body, Some(0), &mut ops)?;

				self.end_scope(def_span)?;

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
				let size = def.typ.x.size();
				if size > u8::MAX as u16 {
					// TODO: also error when out of memeory
					todo!("'var is too large' error");
				}

				let var = Variable { size: size as u8 };
				self.program.vars.insert(unique_name, var);
			}

			Def::Const(def) => {
				// Type check
				let mut ops = Vec::with_capacity(32);
				{
					let body_idx = self.begin_scope(false);
					self.check_nodes(&def.body, Some(body_idx), &mut ops)?;

					self.ws
						.consumer(def_span)
						.compare(std::slice::from_ref(&def.typ.x), StackMatch::Exact)?;

					self.end_scope(def_span)?;
				}

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
		use error::TypeMatch::*;

		let keep = mode.contains(IntrMode::KEEP);

		let (primary_stack, secondary_stack) = if mode.contains(IntrMode::RETURN) {
			(&mut self.rs, &mut self.ws)
		} else {
			(&mut self.ws, &mut self.rs)
		};

		let mut consumer = primary_stack.consumer(intr_span).with_keep(keep);

		macro_rules! err_invalid_stack {
			($($typ:expr),*$(,)?) => {
				Err(Error::InvalidIntrStack {
					expected: vec![$($typ, )*],
					stack: consumer.stack_error(),
					span: intr_span,
				})
			};
		}

		match intr {
			Intrinsic::Add | Intrinsic::Sub | Intrinsic::Mul | Intrinsic::Div => {
				// ( a b -- a+b )
				mode |= self.check_arithmetic_intr(mode, intr_span)?;
				Ok(mode)
			}

			// ( a -- a+1 )
			Intrinsic::Inc => match consumer.pop() {
				Some(a) => {
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					primary_stack.push((a.typ, intr_span));
					Ok(mode)
				}

				_ => err_invalid_stack![AnyOperand],
			},

			// ( a shift8 -- c )
			Intrinsic::Shift => match (consumer.pop(), consumer.pop()) {
				(Some(shift8), Some(a)) if shift8.typ == Type::Byte => {
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					primary_stack.push((a.typ, intr_span));
					Ok(mode)
				}

				_ => err_invalid_stack![AnyNumber, Exact(Type::Byte)],
			},

			// ( a b -- c )
			Intrinsic::And | Intrinsic::Or | Intrinsic::Xor => {
				let output = match (consumer.pop(), consumer.pop()) {
					(Some(b), Some(a)) => match (a.typ, b.typ) {
						(Type::Byte, Type::Byte) => Some(Type::Byte),
						(Type::Short, Type::Short) => Some(Type::Short),
						_ => None,
					},
					_ => None,
				};

				let Some(output) = output else {
					return err_invalid_stack![AnyNumber, AnyNumber];
				};

				if output.is_short() {
					mode |= IntrMode::SHORT;
				}

				primary_stack.push((output, intr_span));
				Ok(mode)
			}

			// ( a b -- bool8 )
			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				match (consumer.pop(), consumer.pop()) {
					(Some(b), Some(a)) => {
						let is_short = match (a.typ, b.typ) {
							(Type::Byte, Type::Byte) => false,
							(Type::Short, Type::Short) => true,
							// NOTE: we don't care what inner types are
							(Type::BytePtr(_), Type::BytePtr(_)) => false,
							(Type::ShortPtr(_), Type::ShortPtr(_)) => true,
							(Type::FuncPtr(_), Type::FuncPtr(_)) => true,
							_ => {
								return Err(Error::UnmatchedInputsTypes {
									found: consumer.found(),
									span: intr_span,
								});
							}
						};

						if is_short {
							mode |= IntrMode::SHORT;
						}

						primary_stack.push((Type::Byte, intr_span));
						Ok(mode)
					}

					_ => err_invalid_stack![AnyOperand, AnyOperand],
				}
			}

			// ( a -- )
			Intrinsic::Pop => match consumer.pop() {
				Some(a) => {
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					Ok(mode)
				}

				_ => err_invalid_stack![AnyOperand],
			},

			// ( a b -- b a )
			Intrinsic::Swap => match (consumer.pop(), consumer.pop()) {
				(Some(b), Some(a)) => {
					if a.typ.is_short() != b.typ.is_short() {
						return Err(Error::UnmatchedInputsSizes {
							found: consumer.found_sizes(),
							span: intr_span,
						});
					}
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					primary_stack.push(b);
					primary_stack.push(a);
					Ok(mode)
				}

				_ => err_invalid_stack![AnyOperand, AnyOperand],
			},

			// ( a b -- b )
			Intrinsic::Nip => match (consumer.pop(), consumer.pop()) {
				(Some(b), Some(a)) => {
					if a.typ.is_short() != b.typ.is_short() {
						return Err(Error::UnmatchedInputsSizes {
							found: consumer.found_sizes(),
							span: intr_span,
						});
					}
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					primary_stack.push(b);
					Ok(mode)
				}

				_ => err_invalid_stack![AnyOperand, AnyOperand],
			},

			// ( a b c -- b c a )
			Intrinsic::Rot => match (consumer.pop(), consumer.pop(), consumer.pop()) {
				(Some(c), Some(b), Some(a)) => {
					if a.typ.is_short() != b.typ.is_short() || b.typ.is_short() != c.typ.is_short()
					{
						return Err(Error::UnmatchedInputsSizes {
							found: consumer.found_sizes(),
							span: intr_span,
						});
					}
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					primary_stack.push(b);
					primary_stack.push(c);
					primary_stack.push(a);
					Ok(mode)
				}

				_ => err_invalid_stack![AnyOperand, AnyOperand, AnyOperand],
			},

			// ( a -- a a )
			Intrinsic::Dup => match consumer.pop() {
				Some(a) => {
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					primary_stack.push(a.clone());
					primary_stack.push((a.typ, intr_span));
					Ok(mode)
				}

				_ => err_invalid_stack![AnyOperand],
			},

			// ( a b -- a b a )
			Intrinsic::Over => match (consumer.pop(), consumer.pop()) {
				(Some(b), Some(a)) => {
					if a.typ.is_short() != b.typ.is_short() {
						return Err(Error::UnmatchedInputsSizes {
							found: consumer.found_sizes(),
							span: intr_span,
						});
					}
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					primary_stack.push(a.clone());
					primary_stack.push(b);
					primary_stack.push((a.typ, intr_span));
					Ok(mode)
				}

				_ => err_invalid_stack![AnyOperand, AnyOperand],
			},

			// ( a -- | a )
			Intrinsic::Sth => match consumer.pop() {
				Some(a) => {
					if a.typ.is_short() {
						mode |= IntrMode::SHORT;
					}
					secondary_stack.push(a);
					Ok(mode)
				}

				_ => err_invalid_stack![AnyOperand],
			},

			// ( addr -- value )
			Intrinsic::Load => {
				let output = consumer.pop().and_then(|addr| match addr.typ {
					Type::BytePtr(t) => {
						mode |= IntrMode::ABS_BYTE_ADDR;
						Some(*t)
					}
					Type::ShortPtr(t) => {
						mode |= IntrMode::ABS_SHORT_ADDR;
						Some(*t)
					}
					_ => None,
				});

				let Some(output) = output else {
					return err_invalid_stack![AnyVarPtr];
				};

				if output.is_short() {
					mode |= IntrMode::SHORT;
				}

				primary_stack.push((output, intr_span));
				Ok(mode)
			}

			// ( value addr -- )
			Intrinsic::Store => match (consumer.pop(), consumer.pop()) {
				(Some(addr), Some(value)) => {
					match addr.typ {
						Type::BytePtr(t) if *t == value.typ => {
							mode |= IntrMode::ABS_BYTE_ADDR;
						}
						Type::ShortPtr(t) if *t == value.typ => {
							mode |= IntrMode::ABS_SHORT_ADDR;
						}
						Type::BytePtr(_) | Type::ShortPtr(_) => {
							return Err(Error::UnmatchedInputsTypes {
								found: consumer.found(),
								span: intr_span,
							});
						}
						_ => return err_invalid_stack![AnyOperand, AnyVarPtr],
					}

					if value.typ.is_short() {
						Ok(mode | IntrMode::SHORT)
					} else {
						Ok(mode)
					}
				}

				_ => err_invalid_stack![AnyOperand, AnyVarPtr],
			},

			// ( device8 -- value )
			Intrinsic::Input | Intrinsic::Input2 => match consumer.pop() {
				Some(device8) if device8.typ == Type::Byte => {
					if intr == Intrinsic::Input2 {
						primary_stack.push((Type::Short, intr_span));
						Ok(mode | IntrMode::SHORT)
					} else {
						primary_stack.push((Type::Byte, intr_span));
						Ok(mode)
					}
				}

				_ => err_invalid_stack![Exact(Type::Byte)],
			},

			// ( value device8 -- )
			Intrinsic::Output => match (consumer.pop(), consumer.pop()) {
				(Some(device8), Some(value)) if device8.typ == Type::Byte => {
					if value.typ.is_short() {
						Ok(mode | IntrMode::SHORT)
					} else {
						Ok(mode)
					}
				}

				_ => err_invalid_stack![AnyOperand, Exact(Type::Byte)],
			},
		}
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
		let mut consumer = primary_stack.consumer(intr_span).with_keep(keep);

		let (Some(b), Some(a)) = (consumer.pop(), consumer.pop()) else {
			return Err(Error::InvalidArithmeticStack {
				stack: consumer.stack_error(),
				span: intr_span,
			});
		};

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
					return Err(Error::UnmatchedInputsTypes {
						found: consumer.found(),
						span: intr_span,
					});
				}
			}
			(Type::ShortPtr(a), Type::ShortPtr(b)) => {
				if a == b {
					Type::ShortPtr(a)
				} else {
					return Err(Error::UnmatchedInputsTypes {
						found: consumer.found(),
						span: intr_span,
					});
				}
			}
			(Type::FuncPtr(a), Type::FuncPtr(b)) => {
				if a == b {
					Type::FuncPtr(a)
				} else {
					return Err(Error::UnmatchedInputsTypes {
						found: consumer.found(),
						span: intr_span,
					});
				}
			}

			_ => {
				return Err(Error::InvalidArithmeticStack {
					stack: consumer.stack_error(),
					span: intr_span,
				});
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

	/// Apply `f` to each scope from the top-most to `till_idx`
	fn scopes_propagate(&mut self, till_idx: usize, f: impl Fn(&mut Scope)) {
		assert!(till_idx < self.scopes.len());

		let len = self.scopes.len();
		let depth = len - till_idx;
		for i in 0..depth {
			f(&mut self.scopes[len - i - 1]);
		}
	}

	pub fn begin_scope(&mut self, branching: bool) -> usize {
		let mut scope = Scope::new(self.ws.items.clone(), self.rs.items.clone());
		scope.branching = branching;
		self.scopes.push(scope);
		self.scopes.len() - 1
	}
	pub fn end_scope(&mut self, span: Span) -> error::Result<()> {
		let scope = self.pop_scope(span);

		// Ensure that the signature of the stacks before this block
		// and after it are the same.
		if !scope.finished {
			self.ws
				.consumer_keep(span)
				.compare(&scope.expected_ws, StackMatch::Exact)?;
			self.rs
				.consumer_keep(span)
				.compare(&scope.expected_rs, StackMatch::Exact)?;
		}

		// Restore previous state of the stacks for branching blocks to pretend that
		// this block has never been executed.
		// Because it indeed may not execute, that's why it is a "branching" block.
		if scope.branching {
			self.ws.items = scope.expected_ws;
			self.rs.items = scope.expected_rs;
		}

		Ok(())
	}
	pub fn pop_scope(&mut self, span: Span) -> Scope {
		match self.scopes.pop() {
			Some(scope) => scope,
			None => panic!("unexpected non-existing scope when popping at {span}"),
		}
	}
}
