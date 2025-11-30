mod consumer;
mod stack;

pub use consumer::*;
pub use stack::*;
use vec1::{Vec1, vec1};

use crate::{
	ast::{Ast, Def, Expr, FuncArgs, Node},
	bug,
	error::{self, Error, TypeMatch},
	lexer::{Span, Spanned},
	problems::Problems,
	program::{Constant, Data, Function, IntrMode, Intrinsic, Op, Program, Variable},
	symbols::{FuncSignature, Name, SymbolSignature, SymbolsTable, Type},
	warn::Warn,
};

/// Block
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Block {
	Normal {
		/// Branching blocks are blocks that can exit early.
		/// For example `if` and `while` block are branching blocks.
		branching: bool,

		/// Expected items on the working stack at the end of this block
		expect_ws: Vec<StackItem>,
		/// Expected items on the return stack at the end of this block
		expect_rs: Vec<StackItem>,
	},
	/// Definition block (body of a function, constant, etc)
	Def {
		/// Expected types on the working stack at the end of this block
		expect_ws: Vec<Type>,
		/// Expected types on the return stack at the end of this block
		expect_rs: Vec<Type>,
	},
	/// Following operations in this block will never be executed.
	/// For example any operations after `jump` or `return` will never be executed.
	Finished,
}

/// Context
#[derive(Debug)]
pub struct Context {
	pub blocks: Vec1<Block>,
}
impl Context {
	/// The last block is always the current one
	pub fn cur_block(&mut self) -> &mut Block {
		self.blocks.last_mut()
	}

	pub fn push_block(&mut self, block: Block) -> usize {
		self.blocks.push(block);
		self.blocks.len() - 1
	}
	pub fn pop_block(&mut self, span: Span) -> Block {
		match self.blocks.pop() {
			Ok(block) => block,
			Err(vec1::Size0Error) => panic!("unexpected non-existing block when popping at {span}"),
		}
	}
}

/// Typechecker
/// Performs type-checking of the specified AST and generates
/// an intermediate representation (IR) program
pub struct Typechecker {
	pub symbols: SymbolsTable,

	program: Program,
	problems: Problems,

	/// Working stack
	pub ws: Stack,
	/// Return stack
	pub rs: Stack,
}
impl Default for Typechecker {
	fn default() -> Self {
		Self {
			symbols: SymbolsTable::default(),

			program: Program::default(),
			problems: Problems::default(),

			ws: Stack::default(),
			rs: Stack::default(),
		}
	}
}
impl Typechecker {
	pub fn check(ast: &Ast) -> Result<(Program, Problems), Problems> {
		let mut checker = Self::default();
		checker.symbols.collect(ast).map_err(Problems::one_err)?;

		let res = checker.check_nodes(&ast.nodes, None, &mut vec![]);
		checker.problems.err_or_ok(res);

		if checker.problems.errors.is_empty() {
			Ok((checker.program, checker.problems))
		} else {
			Err(checker.problems)
		}
	}

	fn check_nodes(
		&mut self,
		nodes: &[Spanned<Node>],
		mut ctx: Option<&mut Context>,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		for node in nodes.iter() {
			match &node.x {
				Node::Expr(expr) => {
					let Some(ctx) = &mut ctx else {
						return Err(Error::IllegalTopLevelExpr(node.span));
					};

					self.check_expr(expr, node.span, ctx, ops)?;
				}
				Node::Def(def) => {
					if ctx.is_some() {
						return Err(Error::NoLocalDefsYet(node.span));
					}

					let res = self.check_def(def, node.span);
					self.problems.err_or_ok(res);
				}
			}
		}
		Ok(())
	}
	pub fn check_expr(
		&mut self,
		expr: &Expr,
		expr_span: Span,
		ctx: &mut Context,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let cur_block = ctx.cur_block();

		if *cur_block == Block::Finished {
			self.problems.warn(Warn::DeadCode(expr_span));
			return Ok(());
		}

		match expr {
			Expr::Byte(b) => {
				self.ws.push(StackItem::new(Type::Byte, expr_span));
				ops.push(Op::Byte(*b));
			}
			Expr::Short(s) => {
				self.ws.push(StackItem::new(Type::Short, expr_span));
				ops.push(Op::Short(*s));
			}
			Expr::String(s) => {
				let item = StackItem::new(Type::ShortPtr(Type::Byte.into()), expr_span);
				self.ws.push(item);

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

			Expr::Store(name) => {
				let Some(symbol) = self.symbols.table.get(name) else {
					return Err(Error::UnknownSymbol(expr_span));
				};

				let mut mode = IntrMode::NONE;
				let mut consumer = self.ws.consumer(expr_span);

				let Some(value) = consumer.pop() else {
					return Err(Error::InvalidIntrStack {
						expected: vec![TypeMatch::AnyOperand],
						stack: consumer.stack_error(),
						span: expr_span,
					});
				};

				match &symbol.signature {
					SymbolSignature::Func(_) | SymbolSignature::Const(_) => {
						return Err(Error::InvalidStoreSymbol(expr_span));
					}

					SymbolSignature::Var(sig) => {
						if sig.typ != value.typ {
							return Err(Error::UnmatchedInputsTypes {
								found: consumer.found(),
								span: expr_span,
							});
						}

						mode |= IntrMode::ABS_BYTE_ADDR;
						if value.typ.is_short() {
							mode |= IntrMode::SHORT;
						}

						ops.push(Op::AbsByteAddrOf(symbol.unique_name));
					}
					SymbolSignature::Data => {
						if value.typ != Type::Byte {
							return Err(Error::UnmatchedInputsTypes {
								found: consumer.found(),
								span: expr_span,
							});
						}

						mode |= IntrMode::ABS_SHORT_ADDR;
						ops.push(Op::AbsShortAddrOf(symbol.unique_name));
					}
				};

				// Generate IR
				ops.push(Op::Intrinsic(Intrinsic::Store, mode));
			}

			// TODO: casting should also probaly work with the return stack?
			// Currently i don't know how to syntactically mark casting for return stack.
			Expr::Cast(types) => {
				let mut bytes_to_pop: u16 = types.iter().fold(0, |acc, t| acc + t.x.size());

				while bytes_to_pop > 0 {
					let Some(item) = self.ws.pop(expr_span) else {
						return Err(Error::CastingUnderflowsStack(expr_span));
					};

					if item.typ.size() > bytes_to_pop {
						return Err(Error::UnhandledCastingData {
							found: item.pushed_at,
							span: expr_span,
						});
					} else {
						bytes_to_pop -= item.typ.size();
					}
				}

				for typ in types.iter() {
					self.ws.push(StackItem::new(typ.x.clone(), typ.span));
				}
			}

			Expr::Bind(names) => {
				if names.len() > self.ws.len() {
					return Err(Error::TooManyBindings(expr_span));
				}

				for (i, name) in names.iter().rev().enumerate() {
					let len = self.ws.items.len();
					let item = &mut self.ws.items[len - 1 - i];

					if name.x.as_ref() == "_" {
						item.name = None;
					} else {
						item.name = Some(name.x.clone());
					}
				}
			}

			Expr::ExpectBind(names) => {
				if names.len() > self.ws.len() {
					return Err(Error::TooManyBindings(expr_span));
				}

				for (i, name) in names.iter().rev().enumerate() {
					let len = self.ws.items.len();
					let item = &self.ws.items[len - 1 - i];

					let has_match = if name.x.as_ref() == "_" {
						item.name == None
					} else {
						item.name.as_ref().is_some_and(|n| *n == name.x)
					};

					if !has_match {
						let found = self.ws.items[len - names.len()..]
							.iter()
							.map(|t| Spanned::new(t.name.clone(), t.pushed_at))
							.collect();
						let expected = names.iter().map(|n| n.x.clone()).collect();

						return Err(Error::UnmatchedNames {
							found,
							expected,
							span: expr_span,
						});
					}
				}
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
				let block_idx = self.begin_block(ctx, false);

				let name = label.x.clone();
				let unique_name = self.symbols.define_label(name, block_idx, label.span)?;

				self.check_nodes(body, Some(ctx), ops)?;
				ops.push(Op::Label(unique_name));

				self.end_block(ctx, expr_span)?;
				self.symbols.undefine_label(&label.x);
			}

			Expr::Jump { label } => {
				let Some(block_label) = self.symbols.labels.get(&label.x).cloned() else {
					return Err(Error::UnknownLabel(label.span));
				};

				self.jump_to_block(ctx, block_label.block_idx, expr_span)?;

				// Generate IR
				ops.push(Op::Jump(block_label.unique_name));
			}

			Expr::Return => {
				self.jump_to_block(ctx, 0, expr_span)?;

				// Generate IR
				ops.push(Op::Return);
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
					self.begin_block(ctx, true);
					{
						ops.push(Op::JumpIf(if_begin_label));

						// `else` block
						self.check_nodes(else_body, Some(ctx), ops)?;
						ops.push(Op::Jump(end_label));
					}
					let else_block = ctx.pop_block(expr_span);

					match else_block {
						Block::Normal {
							expect_ws,
							expect_rs,
							..
						} => {
							self.begin_block(ctx, true);

							// Restore the stacks to the state before the `else` block
							self.ws.items = expect_ws;
							self.rs.items = expect_rs;
						}
						Block::Finished => {
							self.begin_block(ctx, false);
						}

						Block::Def { .. } => bug!("else block cannot be a `Block::Def`, but it is"),
					}

					{
						// `if` block
						ops.push(Op::Label(if_begin_label));
						self.check_nodes(if_body, Some(ctx), ops)?;
						ops.push(Op::Label(end_label));
					}
					// Compare stacks at the end of the `if` and `else` blocks to be equal
					self.end_block(ctx, expr_span)?;
				} else {
					// Single `if`
					let if_begin_label = self.symbols.new_unique_name();
					let end_label = self.symbols.new_unique_name();

					self.begin_block(ctx, true);
					{
						ops.push(Op::JumpIf(if_begin_label));
						ops.push(Op::Jump(end_label));
						ops.push(Op::Label(if_begin_label));

						self.check_nodes(if_body, Some(ctx), ops)?;

						ops.push(Op::Label(end_label));
					}
					self.end_block(ctx, expr_span)?;
				}
			}

			Expr::While { condition, body } => {
				let again_label = self.symbols.new_unique_name();
				let continue_label = self.symbols.new_unique_name();
				let end_label = self.symbols.new_unique_name();

				ops.push(Op::Label(again_label));

				self.begin_block(ctx, false);
				{
					// Condition
					// TODO: check condition to NOT consume items outside itself
					self.check_nodes(condition, Some(ctx), ops)?;

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
				}
				self.end_block(ctx, expr_span)?;

				self.begin_block(ctx, true);
				{
					// Body
					self.check_nodes(body, Some(ctx), ops)?;

					ops.push(Op::Jump(again_label));
					ops.push(Op::Label(end_label));
				}
				self.end_block(ctx, expr_span)?;
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
						self.ws.push(StackItem::new(output.clone(), symbol_span));
					}

					// Generate IR
					ops.push(Op::FuncCall(symbol.unique_name));
				}
			},

			SymbolSignature::Var(sig) => {
				// Type check
				self.ws.push(StackItem::new(sig.typ.clone(), symbol_span));

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
				self.ws.push(StackItem::new(sig.typ.clone(), symbol_span));

				// Generate IR
				ops.push(Op::ConstUse(symbol.unique_name));
			}
			SymbolSignature::Data => {
				// Type check
				self.ws.push(StackItem::new(Type::Byte, symbol_span));

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
				self.ws.push(StackItem::new(typ, symbol_span));

				// Generate IR
				ops.push(Op::AbsShortAddrOf(symbol.unique_name));
			}
			SymbolSignature::Var(sig) => {
				// Type check
				let typ = Type::BytePtr(sig.typ.clone().into());
				self.ws.push(StackItem::new(typ, symbol_span));

				// Generate IR
				ops.push(Op::AbsByteAddrOf(symbol.unique_name));
			}
			SymbolSignature::Data => {
				// Type check
				let typ = Type::ShortPtr(Type::Byte.into());
				self.ws.push(StackItem::new(typ, symbol_span));

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
		self.reset_stacks();

		let symbol = self
			.symbols
			.get_or_define_symbol(def.name(), || def.to_signature(), def_span);
		let unique_name = symbol.unique_name;

		match def {
			Def::Func(def) => {
				let mut ctx: Context;

				match &def.args {
					FuncArgs::Vector => {
						ctx = Context {
							blocks: vec1![Block::Def {
								expect_ws: vec![],
								expect_rs: vec![]
							}],
						};
					}
					FuncArgs::Proc { inputs, outputs } => {
						ctx = Context {
							blocks: vec1![Block::Def {
								expect_ws: outputs.iter().map(|t| t.x.clone()).collect(),
								expect_rs: vec![]
							}],
						};

						// Push function inputs onto the stack
						for input in inputs.iter() {
							self.ws.push(StackItem::new(input.x.clone(), input.span));
						}
					}
				}

				// Check function body
				let mut ops = Vec::with_capacity(64);
				self.check_nodes(&def.body, Some(&mut ctx), &mut ops)?;

				self.compare_block(ctx.blocks.first(), def_span)?;

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
				let mut ctx = Context {
					blocks: vec1![Block::Def {
						expect_ws: vec![def.typ.x.clone()],
						expect_rs: vec![]
					}],
				};

				let mut ops = Vec::with_capacity(32);
				self.check_nodes(&def.body, Some(&mut ctx), &mut ops)?;

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
					primary_stack.push(StackItem::new(a.typ, intr_span));
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
					primary_stack.push(StackItem::new(a.typ, intr_span));
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

				primary_stack.push(StackItem::new(output, intr_span));
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

						primary_stack.push(StackItem::new(Type::Byte, intr_span));
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
					primary_stack.push(StackItem::named(a.typ, a.name.clone(), intr_span));
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
					primary_stack.push(StackItem::named(a.typ, a.name, intr_span));
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

				primary_stack.push(StackItem::new(output, intr_span));
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
						primary_stack.push(StackItem::new(Type::Short, intr_span));
						Ok(mode | IntrMode::SHORT)
					} else {
						primary_stack.push(StackItem::new(Type::Byte, intr_span));
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

		primary_stack.push(StackItem::new(output, intr_span));

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

	fn jump_to_block(
		&mut self,
		ctx: &mut Context,
		block_idx: usize,
		span: Span,
	) -> error::Result<()> {
		match ctx.cur_block() {
			Block::Normal { branching, .. } => {
				if *branching {
					self.blocks_propagate_branching(ctx, block_idx)?;
				} else {
					self.blocks_propagate_finished(ctx, block_idx)?;
				}
			}
			Block::Def { .. } | Block::Finished => (),
		}

		self.compare_block(&ctx.blocks[block_idx], span)?;
		self.finish_block(ctx.cur_block());

		Ok(())
	}

	/// Assign `Block::Finished` to each block from the top-most to `till_idx`
	pub fn blocks_propagate_finished(
		&mut self,
		ctx: &mut Context,
		till_idx: usize,
	) -> error::Result<()> {
		assert!(till_idx < ctx.blocks.len());

		let len = ctx.blocks.len();
		let depth = len - till_idx;
		for i in 0..depth {
			self.finish_block(&mut ctx.blocks[len - i - 1]);
		}
		Ok(())
	}
	/// Mark each block as branching from the top-most to `till_idx`
	pub fn blocks_propagate_branching(
		&mut self,
		ctx: &mut Context,
		till_idx: usize,
	) -> error::Result<()> {
		assert!(till_idx < ctx.blocks.len());

		let len = ctx.blocks.len();
		let depth = len - till_idx;
		for i in 0..depth {
			match &mut ctx.blocks[len - i - 1] {
				Block::Normal { branching, .. } => *branching = true,
				_ => (),
			}
		}
		Ok(())
	}

	pub fn begin_block(&mut self, ctx: &mut Context, branching: bool) -> usize {
		ctx.push_block(Block::Normal {
			branching,
			expect_ws: self.ws.items.clone(),
			expect_rs: self.rs.items.clone(),
		})
	}
	pub fn compare_block(&mut self, block: &Block, span: Span) -> error::Result<()> {
		match block {
			Block::Normal {
				branching: true,
				expect_ws,
				expect_rs,
			} => {
				// Ensure that the signature of the stacks before this block
				// and after it are the same.
				self.ws
					.consumer_keep(span)
					.compare(&expect_ws, StackMatch::Exact)?;
				self.rs
					.consumer_keep(span)
					.compare(&expect_rs, StackMatch::Exact)?;
			}
			Block::Def {
				expect_ws,
				expect_rs,
			} => {
				self.ws
					.consumer_keep(span)
					.compare(&expect_ws, StackMatch::Exact)?;
				self.rs
					.consumer_keep(span)
					.compare(&expect_rs, StackMatch::Exact)?;
			}

			_ => (),
		}

		Ok(())
	}
	pub fn finish_block(&mut self, block: &mut Block) {
		match block {
			Block::Normal {
				branching: true,
				expect_ws,
				expect_rs,
			} => {
				// Restore previous state of the stacks for branching blocks to pretend that
				// this block has never been executed.
				// Because it indeed may not execute, that's why it is a "branching" block.
				self.ws.items = expect_ws.clone();
				self.rs.items = expect_rs.clone();
			}

			_ => (),
		}

		*block = Block::Finished;
	}
	pub fn end_block(&mut self, ctx: &mut Context, span: Span) -> error::Result<()> {
		let mut block = ctx.pop_block(span);
		self.compare_block(&block, span)?;
		self.finish_block(&mut block);
		Ok(())
	}
}
