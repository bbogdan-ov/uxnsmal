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
pub struct Scope {
	pub top_level: bool,
	/// Whether the following operations in the current scope will never be executed.
	/// For example any operations after `jump` or `return` (which set this flag to true) will
	/// never be executed.
	pub dead_code_depth: u32,
	/// Whether the block can branch.
	/// For example `if` block or block with `jumpif` can branch.
	pub branching: bool,
}
impl Scope {
	pub fn new() -> Self {
		Self {
			top_level: false,
			dead_code_depth: 0,
			branching: false,
		}
	}
	pub fn top_level() -> Self {
		let mut this = Self::new();
		this.top_level = true;
		this
	}
	pub fn branching() -> Self {
		let mut this = Self::new();
		this.branching = true;
		this
	}
}

/// Block
#[derive(Debug, Clone)]
pub struct Block {
	pub expected_ws: Vec<StackItem>,
	pub expected_rs: Vec<StackItem>,
}
impl Block {
	pub fn new(ws: &Stack, rs: &Stack) -> Self {
		Self {
			expected_ws: ws.items.clone(),
			expected_rs: rs.items.clone(),
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

	blocks: Vec<Block>,
}
impl Default for Typechecker {
	fn default() -> Self {
		Self {
			symbols: SymbolsTable::default(),

			program: Program::default(),

			ws: Stack::default(),
			rs: Stack::default(),

			blocks: Vec::with_capacity(8),
		}
	}
}
impl Typechecker {
	pub fn check(ast: &Ast) -> error::Result<Program> {
		let mut checker = Self::default();
		checker.symbols.collect(ast)?;
		let mut scope = Scope::top_level();
		checker.check_nodes(&ast.nodes, &mut scope, &mut vec![])?;

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
		if scope.top_level {
			return Err(Error::IllegalTopLevelExpr(expr_span));
		};

		if scope.dead_code_depth > 0 {
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
				looping,
				label,
				body,
			} => {
				let block_idx = self.begin_block();

				let name = label.x.clone();
				let unique_name = self.symbols.define_label(name, block_idx, label.span)?;

				let mut body_scope = Scope::new();
				body_scope.branching = *looping;
				self.check_nodes(body, &mut body_scope, ops)?;
				ops.push(Op::Label(unique_name));

				self.symbols.undefine_label(&label.x);

				self.end_block(scope, body_scope, expr_span)?;
			}

			Expr::Jump { label, conditional } => {
				let Some(block_label) = self.symbols.labels.get(&label.x).cloned() else {
					return Err(Error::UnknownLabel(label.span));
				};

				if *conditional {
					let bool8 = self.ws.pop_one(false, expr_span)?;
					if bool8.typ != Type::Byte {
						return Err(Error::InvalidIfInput(expr_span));
					}
				}

				let Some(block) = self.blocks.get(block_label.block_idx) else {
					panic!(
						"unexpected non-existing block at index {} at jump {expr_span}",
						block_label.block_idx
					);
				};

				self.ws
					.consumer_keep(expr_span)
					.compare(&block.expected_ws, StackMatch::Exact)?;
				self.rs
					.consumer_keep(expr_span)
					.compare(&block.expected_rs, StackMatch::Exact)?;

				if *conditional {
					scope.branching = true;
					ops.push(Op::JumpIf(block_label.unique_name));
				} else {
					if scope.branching {
						scope.dead_code_depth = 1;
					} else {
						scope.dead_code_depth = (self.blocks.len() - block_label.block_idx) as u32;
					}
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
					self.begin_block();

					ops.push(Op::JumpIf(if_begin_label));

					// `else` block
					let mut else_scope = Scope::branching();
					self.check_nodes(else_body, &mut else_scope, ops)?;
					ops.push(Op::Jump(end_label));

					let before_else = self.pop_block(expr_span);

					// Take snapshot of the stacks at the end of the `else` block
					self.begin_block();

					// Restore the stacks to the state before the `else` block
					self.ws.items = before_else.expected_ws;
					self.rs.items = before_else.expected_rs;

					// `if` block
					ops.push(Op::Label(if_begin_label));
					let mut if_scope = Scope::branching();
					self.check_nodes(if_body, &mut if_scope, ops)?;
					ops.push(Op::Label(end_label));

					// Compare stacks at the end of the `if` and `else` blocks to be equal
					self.end_block(scope, if_scope, expr_span)?;
				} else {
					// Single `if`
					let if_begin_label = self.symbols.new_unique_name();
					let end_label = self.symbols.new_unique_name();

					self.begin_block();

					ops.push(Op::JumpIf(if_begin_label));
					ops.push(Op::Jump(end_label));
					ops.push(Op::Label(if_begin_label));

					let mut if_scope = Scope::branching();
					self.check_nodes(if_body, &mut if_scope, ops)?;

					ops.push(Op::Label(end_label));

					self.end_block(scope, if_scope, expr_span)?;
				}
			}

			Expr::While { condition, body } => {
				let again_label = self.symbols.new_unique_name();
				let continue_label = self.symbols.new_unique_name();
				let end_label = self.symbols.new_unique_name();

				self.begin_block();

				ops.push(Op::Label(again_label));

				{
					// Condition
					// TODO: check condition to NOT consume items outside itself
					let mut cond_scope = Scope::new();
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
				let mut body_scope = Scope::branching();
				self.check_nodes(body, &mut body_scope, ops)?;

				ops.push(Op::Jump(again_label));
				ops.push(Op::Label(end_label));

				self.end_block(scope, body_scope, expr_span)?;
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
		if !scope.top_level {
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
				let mut body_scope = Scope::new();
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
				let mut body_scope = Scope::new();
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

	pub fn begin_block(&mut self) -> usize {
		let block = Block::new(&self.ws, &self.rs);
		self.blocks.push(block);
		self.blocks.len() - 1
	}
	pub fn end_block(
		&mut self,
		scope: &mut Scope,
		body_scope: Scope,
		span: Span,
	) -> error::Result<()> {
		let block = self.pop_block(span);

		if body_scope.branching && body_scope.dead_code_depth == 0 {
			self.ws
				.consumer_keep(span)
				.compare(&block.expected_ws, StackMatch::Exact)?;
			self.rs
				.consumer_keep(span)
				.compare(&block.expected_rs, StackMatch::Exact)?;
		}

		if body_scope.dead_code_depth > 0 {
			scope.dead_code_depth = body_scope.dead_code_depth - 1;
			self.ws.items = block.expected_ws;
			self.rs.items = block.expected_rs;
		}

		Ok(())
	}
	pub fn pop_block(&mut self, span: Span) -> Block {
		match self.blocks.pop() {
			Some(block) => block,
			None => panic!("unexpected non-existing block when popping at {span}"),
		}
	}
}
