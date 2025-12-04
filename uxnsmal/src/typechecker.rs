mod consumer;
mod stack;

use std::collections::HashMap;

pub use consumer::*;
pub use stack::*;
use vec1::{Vec1, vec1};

use crate::{
	ast::{Ast, Def, ElseBlock, ElseIfBlock, Expr, FuncArgs, NamedType, Node},
	bug,
	error::{self, Error, ExpectedStack, SymbolError},
	lexer::{Span, Spanned},
	problems::Problems,
	program::{Constant, Data, Function, IntrMode, Intrinsic, Op, Program, Variable},
	symbols::{
		ConstSymbol, DataSymbol, FuncSignature, FuncSymbol, Name, Symbol, SymbolKind, SymbolsTable,
		Type, TypeSymbol, UniqueName, VarSymbol,
	},
	warn::Warn,
};

fn intr_mode_from_size(size: u16) -> error::Result<IntrMode> {
	match size {
		0 | 1 => Ok(IntrMode::NONE),
		2 => Ok(IntrMode::SHORT),
		3.. => todo!("handle type with size > 2"),
	}
}
fn intr_mode_from_type(typ: &Type) -> error::Result<IntrMode> {
	intr_mode_from_size(typ.size())
}

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

/// Block label
#[derive(Debug, Clone)]
pub struct Label {
	pub unique_name: UniqueName,
	pub block_idx: usize,
	/// Location at which this label is defined
	pub span: Span,
}
impl Label {
	pub fn new(unique_name: UniqueName, block_idx: usize, span: Span) -> Self {
		Self {
			unique_name,
			block_idx,
			span,
		}
	}
}

/// Context
#[derive(Debug)]
pub struct Context {
	pub ops: Vec<Op>,
	pub blocks: Vec1<Block>,

	/// Table of labels accessible in the current scope/block.
	/// It is a separate table from symbols because labels have a separate namespace.
	pub labels: HashMap<Name, Label>,
}
impl Context {
	pub fn new(expect_ws: Vec<Type>, expect_rs: Vec<Type>) -> Self {
		Self {
			ops: Vec::with_capacity(32),
			blocks: vec1![Block::Def {
				expect_ws,
				expect_rs
			}],

			labels: HashMap::default(),
		}
	}

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
			Err(vec1::Size0Error) => bug!("the last `Block::Def` was popped at {span}"),
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
		checker.collect(ast).map_err(Problems::one_err)?;

		let res = checker.check_nodes(&ast.nodes, None);
		checker.problems.err_or_ok(res);

		if checker.problems.errors.is_empty() {
			Ok((checker.program, checker.problems))
		} else {
			Err(checker.problems)
		}
	}

	/// Walk through AST and collect all top-level symbol definitions
	fn collect(&mut self, ast: &Ast) -> error::Result<()> {
		for node in ast.nodes.iter() {
			let Node::Def(def) = node else {
				continue;
			};

			let unique_name = self.symbols.new_unique_name();

			match def {
				Def::Type(def) => {
					let inherits = def.inherits.x.clone();
					let inherits = inherits.into_sized(&self.symbols, def.inherits.span)?;
					let symbol = Symbol::Type(TypeSymbol {
						inherits,
						defined_at: def.name.span,
					});
					self.symbols.define_symbol(def.name.x.clone(), symbol)?;
				}

				Def::Func(def) => {
					let symbol = Symbol::Func(FuncSymbol {
						unique_name,
						signature: def.args.clone().into_signature(&self.symbols)?,
						defined_at: def.name.span,
					});
					self.symbols.define_symbol(def.name.x.clone(), symbol)?;
				}
				Def::Var(def) => {
					let typ = def.typ.x.clone();
					let typ = typ.into_sized(&self.symbols, def.typ.span)?;
					let symbol = Symbol::Var(VarSymbol {
						unique_name,
						typ,
						defined_at: def.name.span,
					});
					self.symbols.define_symbol(def.name.x.clone(), symbol)?;
				}
				Def::Const(def) => {
					let typ = def.typ.x.clone();
					let typ = typ.into_sized(&self.symbols, def.typ.span)?;
					let symbol = Symbol::Const(ConstSymbol {
						unique_name,
						typ,
						defined_at: def.name.span,
					});
					self.symbols.define_symbol(def.name.x.clone(), symbol)?;
				}
				Def::Data(def) => {
					let symbol = Symbol::Data(DataSymbol {
						unique_name,
						defined_at: def.name.span,
					});
					self.symbols.define_symbol(def.name.x.clone(), symbol)?;
				}
			}
		}

		Ok(())
	}

	fn check_nodes(&mut self, nodes: &[Node], mut ctx: Option<&mut Context>) -> error::Result<()> {
		for node in nodes.iter() {
			match node {
				Node::Expr(expr) => {
					let Some(ctx) = &mut ctx else {
						return Err(Error::IllegalTopLevelExpr(expr.span()));
					};

					self.check_expr(expr, ctx)?;
				}
				Node::Def(def) => {
					if ctx.is_some() {
						return Err(Error::NoLocalDefsYet(def.span()));
					}

					let res = self.check_def(def, def.span());
					self.problems.err_or_ok(res);
				}
			}
		}
		Ok(())
	}
	pub fn check_expr(&mut self, expr: &Expr, ctx: &mut Context) -> error::Result<()> {
		let cur_block = ctx.cur_block();

		if *cur_block == Block::Finished {
			self.problems.warn(Warn::DeadCode(expr.span()));
			return Ok(());
		}

		match expr {
			Expr::Byte { value, span } => {
				self.ws.push(StackItem::new(Type::Byte, *span));
				ctx.ops.push(Op::Byte(*value));
			}
			Expr::Short { value, span } => {
				self.ws.push(StackItem::new(Type::Short, *span));
				ctx.ops.push(Op::Short(*value));
			}
			Expr::String { string, span } => {
				let item = StackItem::new(Type::ShortPtr(Type::Byte.into()), *span);
				self.ws.push(item);

				// Generate IR
				// Insert an unique data for each string literal even if strings contents are the same
				let unique_name = self.symbols.new_unique_name();
				let body = string.as_bytes().into();
				self.program.datas.insert(unique_name, Data { body });

				ctx.ops.push(Op::AbsShortAddrOf(unique_name));
			}
			Expr::Padding { .. } => {
				todo!("`Expr::Padding` outside 'data' blocks should error before typecheck stage");
			}

			Expr::Store { symbol, span } => self.check_store(symbol, ctx, *span)?,

			Expr::Cast { types, span } => self.check_cast(types.as_slice(), *span)?,

			Expr::Bind { names, span } => {
				if names.len() > self.ws.len() {
					return Err(Error::TooManyBindings(*span));
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

			Expr::ExpectBind { names, span } => {
				if names.len() > self.ws.len() {
					return Err(Error::TooManyBindings(*span));
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
							span: *span,
						});
					}
				}
			}

			Expr::Intrinsic { kind, mode, span } => {
				let mut mode = *mode;
				mode |= self.check_intrinsic(*kind, mode, *span)?;

				// Generate IR
				ctx.ops.push(Op::Intrinsic(*kind, mode))
			}
			Expr::Symbol { name, span } => self.check_symbol(name, *span, ctx)?,
			Expr::PtrTo { name, span } => self.check_ptr_to(name, *span, ctx)?,

			Expr::Block {
				label, body, span, ..
			} => {
				let block_idx = self.begin_block(ctx, false);

				let name = label.x.clone();
				let unique_name = self.define_label(ctx, name, block_idx, label.span)?;

				self.check_nodes(body, Some(ctx))?;
				ctx.ops.push(Op::Label(unique_name));

				self.end_block(ctx, *span)?;
				self.undefine_label(ctx, &label.x);
			}

			Expr::Jump { label, span } => {
				let Some(block_label) = ctx.labels.get(&label.x).cloned() else {
					return Err(Error::UnknownLabel(label.span));
				};

				self.jump_to_block(ctx, block_label.block_idx, *span)?;
				ctx.ops.push(Op::Jump(block_label.unique_name));
			}
			Expr::Return { span } => {
				self.jump_to_block(ctx, 0, *span)?;
				ctx.ops.push(Op::Return);
			}
			Expr::If {
				if_body,
				if_span,
				elif_blocks,
				else_block,
				span,
			} => self.check_if(if_body, *if_span, elif_blocks, else_block, ctx, *span)?,
			Expr::While {
				condition,
				body,
				span,
			} => {
				self.check_while(condition, body, ctx, *span)?;
			}
		}

		Ok(())
	}

	fn check_symbol(&mut self, name: &Name, span: Span, ctx: &mut Context) -> error::Result<()> {
		let Some(symbol) = self.symbols.table.get(name) else {
			return Err(Error::UnknownSymbol(span));
		};

		match symbol {
			Symbol::Type(typ) => {
				return Err(Error::InvalidSymbol {
					error: SymbolError::IllegalUse {
						found: SymbolKind::Type,
					},
					defined_at: typ.defined_at,
					span,
				});
			}

			Symbol::Func(func) => match &func.signature {
				FuncSignature::Vector => {
					return Err(Error::InvalidSymbol {
						error: SymbolError::IllegalVectorCall,
						defined_at: func.defined_at,
						span,
					});
				}
				FuncSignature::Proc { inputs, outputs } => {
					// Check function inputs
					self.ws.consumer(span).compare(inputs, StackMatch::Tail)?;

					// Push function outputs
					for output in outputs.iter() {
						self.ws.push(StackItem::new(output.clone(), span));
					}

					// Generate IR
					ctx.ops.push(Op::FuncCall(func.unique_name));
				}
			},

			Symbol::Var(var) => {
				// Type check
				self.ws.push(StackItem::new(var.typ.clone(), span));

				// Generate IR
				let mut mode = IntrMode::ABS_BYTE_ADDR;
				mode |= intr_mode_from_type(&var.typ)?;
				ctx.ops.push(Op::AbsByteAddrOf(var.unique_name));
				ctx.ops.push(Op::Intrinsic(Intrinsic::Load, mode));
			}
			Symbol::Const(cnst) => {
				// Type check
				self.ws.push(StackItem::new(cnst.typ.clone(), span));

				// Generate IR
				ctx.ops.push(Op::ConstUse(cnst.unique_name));
			}
			Symbol::Data(data) => {
				// Type check
				self.ws.push(StackItem::new(Type::Byte, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddrOf(data.unique_name));
				ctx.ops
					.push(Op::Intrinsic(Intrinsic::Load, IntrMode::ABS_SHORT_ADDR));
			}
		};

		Ok(())
	}

	fn check_ptr_to(
		&mut self,
		name: &Spanned<Name>,
		span: Span,
		ctx: &mut Context,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.table.get(&name.x) else {
			return Err(Error::UnknownSymbol(span));
		};

		match symbol {
			Symbol::Const(_) | Symbol::Type(_) => {
				return Err(Error::InvalidSymbol {
					error: SymbolError::IllegalPtr {
						found: symbol.kind(),
					},
					defined_at: symbol.defined_at(),
					span,
				});
			}

			Symbol::Func(func) => {
				// Type check
				let typ = Type::FuncPtr(func.signature.clone());
				self.ws.push(StackItem::new(typ, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddrOf(func.unique_name));
			}
			Symbol::Var(var) => {
				// Type check
				let typ = Type::BytePtr(var.typ.clone().into());
				self.ws.push(StackItem::new(typ, span));

				// Generate IR
				ctx.ops.push(Op::AbsByteAddrOf(var.unique_name));
			}
			Symbol::Data(data) => {
				// Type check
				let typ = Type::ShortPtr(Type::Byte.into());
				self.ws.push(StackItem::new(typ, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddrOf(data.unique_name));
			}
		};

		Ok(())
	}

	fn check_store(
		&mut self,
		name: &Spanned<Name>,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.table.get(&name.x) else {
			return Err(Error::UnknownSymbol(span));
		};

		let mut mode = IntrMode::NONE;

		let expect_typ: &Type = match symbol {
			Symbol::Func(_) | Symbol::Const(_) | Symbol::Type(_) => {
				return Err(Error::InvalidSymbol {
					error: SymbolError::IllegalStore {
						found: symbol.kind(),
					},
					defined_at: symbol.defined_at(),
					span,
				});
			}

			Symbol::Var(var) => {
				mode |= IntrMode::ABS_BYTE_ADDR;
				ctx.ops.push(Op::AbsByteAddrOf(var.unique_name));

				&var.typ
			}
			Symbol::Data(data) => {
				mode |= IntrMode::ABS_SHORT_ADDR;
				ctx.ops.push(Op::AbsShortAddrOf(data.unique_name));
				&Type::Byte
			}
		};

		let mut consumer = self.ws.consumer(span);
		match consumer.pop() {
			Some(value) if value.typ == *expect_typ => {
				mode |= intr_mode_from_type(&value.typ)?;
				ctx.ops.push(Op::Intrinsic(Intrinsic::Store, mode));
				Ok(())
			}
			_ => Err(Error::InvalidStack {
				expected: ExpectedStack::Store(expect_typ.clone()),
				found: consumer.found(),
				error: consumer.stack_error(),
				span,
			}),
		}
	}

	// TODO: casting should also probaly work with the return stack?
	// Currently i don't know how to syntactically mark casting for return stack.
	fn check_cast(&mut self, types: &[NamedType], span: Span) -> error::Result<()> {
		let items: Vec<StackItem> = types
			.iter()
			.cloned()
			.map(|t| {
				let typ = t.typ.x.into_sized(&self.symbols, t.typ.span)?;
				Ok(StackItem::named(typ, t.name.map(|n| n.x), t.typ.span))
			})
			.collect::<error::Result<Vec<StackItem>>>()?;

		let mut bytes_to_pop: u16 = items.iter().fold(0, |acc, t| acc + t.typ.size());

		while bytes_to_pop > 0 {
			let Some(item) = self.ws.pop(span) else {
				return Err(Error::CastingUnderflowsStack(span));
			};

			if item.typ.size() > bytes_to_pop {
				return Err(Error::UnhandledCastingData {
					found: item.pushed_at,
					span,
				});
			} else {
				bytes_to_pop -= item.typ.size();
			}
		}

		for item in items {
			self.ws.push(item);
		}

		Ok(())
	}

	fn check_if(
		&mut self,
		if_body: &[Node],
		if_span: Span,
		elif_blocks: &[ElseIfBlock],
		else_block: &Option<ElseBlock>,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		self.consume_condition(span)?;

		// TODO!: refactor this code, this is kinda mess

		if let Some(else_block) = else_block
			&& !elif_blocks.is_empty()
		{
			// `if {} elif {} else {}`
			let if_begin_label = self.symbols.new_unique_name();
			let else_begin_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();
			let mut next_label = self.symbols.new_unique_name();

			ctx.ops.push(Op::JumpIf(if_begin_label));
			ctx.ops.push(Op::Jump(next_label));

			let ws_before = self.ws.items.clone();
			let rs_before = self.rs.items.clone();

			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::Label(if_begin_label));
				self.check_nodes(if_body, Some(ctx))?;
				ctx.ops.push(Op::Jump(end_label));
			}

			let ws_to_expect = self.ws.items.clone();
			let rs_to_expect = self.rs.items.clone();

			let mut if_block = ctx.pop_block(if_span);
			self.finish_block(&mut if_block);

			for (i, elif) in elif_blocks.iter().enumerate() {
				ctx.ops.push(Op::Label(next_label));

				self.check_condition(&elif.condition, ctx, elif.span)?;

				let elseif_begin_label = self.symbols.new_unique_name();
				ctx.ops.push(Op::JumpIf(elseif_begin_label));

				if i < elif_blocks.len() - 1 {
					next_label = self.symbols.new_unique_name();
					ctx.ops.push(Op::Jump(next_label));
				} else {
					ctx.ops.push(Op::Jump(else_begin_label));
				}

				ctx.ops.push(Op::Label(elseif_begin_label));

				// Check `elif` body
				ctx.push_block(Block::Normal {
					branching: true,
					expect_ws: ws_to_expect.clone(),
					expect_rs: rs_to_expect.clone(),
				});
				self.check_nodes(&elif.body, Some(ctx))?;
				self.end_block(ctx, elif.span)?;

				self.ws.items = ws_before.clone();
				self.rs.items = rs_before.clone();

				ctx.ops.push(Op::Jump(end_label));
			}

			ctx.push_block(Block::Normal {
				branching: true,
				expect_ws: ws_to_expect.clone(),
				expect_rs: rs_to_expect.clone(),
			});
			{
				ctx.ops.push(Op::Label(else_begin_label));
				self.check_nodes(&else_block.body, Some(ctx))?;
			}
			self.end_block(ctx, else_block.span)?;

			ctx.ops.push(Op::Label(end_label));
		} else if !elif_blocks.is_empty() {
			// `if {} elif {}`
			let if_begin_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();
			let mut next_label = self.symbols.new_unique_name();

			ctx.ops.push(Op::JumpIf(if_begin_label));
			ctx.ops.push(Op::Jump(next_label));

			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::Label(if_begin_label));
				self.check_nodes(if_body, Some(ctx))?;
				ctx.ops.push(Op::Jump(end_label));
			}
			self.end_block(ctx, if_span)?;

			for (i, elif) in elif_blocks.iter().enumerate() {
				ctx.ops.push(Op::Label(next_label));

				self.check_condition(&elif.condition, ctx, elif.span)?;

				let elseif_begin_label = self.symbols.new_unique_name();
				ctx.ops.push(Op::JumpIf(elseif_begin_label));

				if i < elif_blocks.len() - 1 {
					next_label = self.symbols.new_unique_name();
					ctx.ops.push(Op::Jump(next_label));
				} else {
					ctx.ops.push(Op::Jump(end_label));
				}

				ctx.ops.push(Op::Label(elseif_begin_label));

				// Check `elif` body
				self.begin_block(ctx, true);
				self.check_nodes(&elif.body, Some(ctx))?;
				self.end_block(ctx, elif.span)?;

				ctx.ops.push(Op::Jump(end_label));
			}

			ctx.ops.push(Op::Label(end_label));
		} else if let Some(else_block) = else_block {
			// `if {} else {}`
			// Code below may be a bit confusing

			let if_begin_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();

			// Take snapshot before the `else` block
			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::JumpIf(if_begin_label));

				// `else` block
				self.check_nodes(&else_block.body, Some(ctx))?;
				ctx.ops.push(Op::Jump(end_label));
			}

			let else_block = ctx.pop_block(else_block.span);
			self.begin_chained_block(ctx, &else_block, true);
			{
				// `if` block
				ctx.ops.push(Op::Label(if_begin_label));
				self.check_nodes(if_body, Some(ctx))?;
				ctx.ops.push(Op::Label(end_label));
			}
			// Compare stacks at the end of the `if` and `else` blocks to be equal
			self.end_block(ctx, if_span)?;
		} else {
			// `if {}`
			let if_begin_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();

			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::JumpIf(if_begin_label));
				ctx.ops.push(Op::Jump(end_label));
				ctx.ops.push(Op::Label(if_begin_label));

				self.check_nodes(if_body, Some(ctx))?;

				ctx.ops.push(Op::Label(end_label));
			}
			self.end_block(ctx, if_span)?;
		}

		Ok(())
	}

	fn check_while(
		&mut self,
		condition: &Spanned<Vec<Node>>,
		body: &[Node],
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let again_label = self.symbols.new_unique_name();
		let continue_label = self.symbols.new_unique_name();
		let end_label = self.symbols.new_unique_name();

		ctx.ops.push(Op::Label(again_label));

		self.check_condition(condition, ctx, span)?;

		ctx.ops.push(Op::JumpIf(continue_label));
		ctx.ops.push(Op::Jump(end_label));
		ctx.ops.push(Op::Label(continue_label));

		self.begin_block(ctx, true);
		{
			// Body
			self.check_nodes(body, Some(ctx))?;

			ctx.ops.push(Op::Jump(again_label));
			ctx.ops.push(Op::Label(end_label));
		}
		self.end_block(ctx, span)?;

		Ok(())
	}

	fn consume_condition(&mut self, span: Span) -> error::Result<()> {
		let mut consumer = self.ws.consumer(span);
		match consumer.pop() {
			Some(bool8) if bool8.typ == Type::Byte => (/* ok */),
			_ => {
				return Err(Error::InvalidStack {
					expected: ExpectedStack::Condition,
					found: consumer.found(),
					error: consumer.stack_error(),
					span,
				});
			}
		}
		Ok(())
	}
	fn check_condition(
		&mut self,
		condition: &Spanned<Vec<Node>>,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		self.begin_block(ctx, true);

		self.check_nodes(&condition.x, Some(ctx))?;
		self.consume_condition(span)?;

		self.end_block(ctx, span)?;
		Ok(())
	}

	pub fn check_def(&mut self, def: &Def, def_span: Span) -> error::Result<()> {
		self.reset_stacks();

		match def {
			Def::Func(def) => {
				let symbol = self
					.symbols
					.get_func(&def.name.x, def.name.span)
					.unwrap_or_else(|e| bug!("unexpected symbol error: {e:#?}"));
				let unique_name = symbol.unique_name;

				let expect_ws: Vec<Type> = match &symbol.signature {
					FuncSignature::Vector => {
						vec![]
					}
					FuncSignature::Proc { inputs, outputs } => {
						let FuncArgs::Proc { inputs: args, .. } = &def.args else {
							todo!()
						};

						// Push function inputs onto the stack
						for (idx, input) in inputs.iter().enumerate() {
							let arg = &args[idx];
							let item = StackItem::named(
								input.clone(),
								arg.name.clone().map(|n| n.x),
								arg.typ.span,
							);
							self.ws.push(item);
						}

						outputs.clone()
					}
				};

				// Check function body
				let mut ctx = Context::new(expect_ws, vec![]);
				self.check_nodes(&def.body, Some(&mut ctx))?;

				self.compare_block(ctx.blocks.first(), def_span)?;

				// Generate IR
				let func = Function {
					is_vector: matches!(def.args, FuncArgs::Vector { .. }),
					body: ctx.ops.into(),
				};

				if def.name.x.as_ref() == "on-reset" {
					self.program.reset_func = Some((unique_name, func));
				} else {
					self.program.funcs.insert(unique_name, func);
				}
			}

			Def::Var(def) => {
				let symbol = self
					.symbols
					.get_var(&def.name.x, def.name.span)
					.unwrap_or_else(|e| bug!("unexpected symbol error: {e:#?}"));

				// Generate IR
				let size = self.symbols.type_size(&def.typ.x, def.typ.span)?;
				if size > u8::MAX as u16 {
					// TODO: also error when out of memeory
					todo!("'var is too large' error");
				}

				let var = Variable { size: size as u8 };
				self.program.vars.insert(symbol.unique_name, var);
			}

			Def::Const(def) => {
				let symbol = self
					.symbols
					.get_const(&def.name.x, def.name.span)
					.unwrap_or_else(|e| bug!("unexpected symbol error: {e:#?}"));
				let unique_name = symbol.unique_name;

				// Type check
				let mut ctx = Context::new(vec![symbol.typ.clone()], vec![]);
				self.check_nodes(&def.body, Some(&mut ctx))?;
				self.compare_block(ctx.blocks.first(), def_span)?;

				// Generate IR
				let cnst = Constant {
					body: ctx.ops.into(),
				};
				self.program.consts.insert(unique_name, cnst);
			}

			Def::Data(def) => {
				let symbol = self
					.symbols
					.get_data(&def.name.x, def.name.span)
					.unwrap_or_else(|e| bug!("unexpected symbol error: {e:#?}"));

				// Generate IR
				let mut bytes = Vec::with_capacity(64);

				for node in def.body.iter() {
					match node {
						Node::Expr(Expr::Byte { value, .. }) => {
							bytes.push(*value);
						}
						Node::Expr(Expr::Short { value, .. }) => {
							let a = ((*value & 0xFF00) >> 8) as u8;
							let b = (*value & 0x00FF) as u8;
							bytes.push(a);
							bytes.push(b);
						}
						Node::Expr(Expr::String { string, .. }) => {
							bytes.extend(string.as_bytes());
						}
						Node::Expr(Expr::Padding { value, .. }) => {
							bytes.extend(std::iter::repeat_n(0, *value as usize));
						}
						_ => return Err(Error::NoCodeInDataYet(node.span())),
					}
				}

				let data = Data { body: bytes.into() };
				self.program.datas.insert(symbol.unique_name, data);
			}

			Def::Type(_) => (/* do nothing */),
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

		let mut consumer = primary_stack.consumer(intr_span).with_keep(keep);

		macro_rules! err_invalid_stack {
			($expected:expr) => {
				Err(Error::InvalidStack {
					expected: $expected,
					found: consumer.found(),
					error: consumer.stack_error(),
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
					mode |= intr_mode_from_type(&a.typ)?;
					primary_stack.push(a);
					Ok(mode)
				}

				_ => err_invalid_stack!(ExpectedStack::IntrInc),
			},

			// ( a shift8 -- c )
			Intrinsic::Shift => match (consumer.pop(), consumer.pop()) {
				(Some(shift8), Some(a)) if shift8.typ == Type::Byte => {
					mode |= intr_mode_from_type(&a.typ)?;
					primary_stack.push(StackItem::new(a.typ, intr_span));
					Ok(mode)
				}

				_ => err_invalid_stack!(ExpectedStack::IntrShift),
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
					return err_invalid_stack!(ExpectedStack::Logic);
				};

				mode |= intr_mode_from_type(&output)?;

				primary_stack.push(StackItem::new(output, intr_span));
				Ok(mode)
			}

			// ( a b -- bool8 )
			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				let (Some(b), Some(a)) = (consumer.pop(), consumer.pop()) else {
					return err_invalid_stack!(ExpectedStack::Comparison);
				};

				mode |= intr_mode_from_type(&a.typ)?;

				if !a.typ.same_as(&b.typ) {
					return Err(Error::UnmatchedInputsTypes {
						found: consumer.found(),
						span: intr_span,
					});
				}

				primary_stack.push(StackItem::new(Type::Byte, intr_span));
				Ok(mode)
			}

			// ( a -- )
			Intrinsic::Pop => {
				let Some(a) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::Manipulation(1));
				};

				mode |= intr_mode_from_type(&a.typ)?;
				Ok(mode)
			}

			// ( a b -- b a )
			Intrinsic::Swap => {
				let (Some(b), Some(a)) = (consumer.pop(), consumer.pop()) else {
					return err_invalid_stack!(ExpectedStack::Manipulation(2));
				};

				if a.typ.size() != b.typ.size() {
					return Err(Error::UnmatchedInputsSizes {
						found: consumer.found_sizes(),
						span: intr_span,
					});
				}
				mode |= intr_mode_from_type(&a.typ)?;
				primary_stack.push(b);
				primary_stack.push(a);
				Ok(mode)
			}

			// ( a b -- b )
			Intrinsic::Nip => {
				let (Some(b), Some(a)) = (consumer.pop(), consumer.pop()) else {
					return err_invalid_stack!(ExpectedStack::Manipulation(2));
				};

				if a.typ.size() != b.typ.size() {
					return Err(Error::UnmatchedInputsSizes {
						found: consumer.found_sizes(),
						span: intr_span,
					});
				}
				mode |= intr_mode_from_type(&a.typ)?;
				primary_stack.push(b);
				Ok(mode)
			}

			// ( a b c -- b c a )
			Intrinsic::Rot => {
				let (Some(c), Some(b), Some(a)) = (consumer.pop(), consumer.pop(), consumer.pop())
				else {
					return err_invalid_stack!(ExpectedStack::Manipulation(3));
				};

				if a.typ.size() != b.typ.size() || b.typ.size() != c.typ.size() {
					return Err(Error::UnmatchedInputsSizes {
						found: consumer.found_sizes(),
						span: intr_span,
					});
				}
				mode |= intr_mode_from_type(&a.typ)?;
				primary_stack.push(b);
				primary_stack.push(c);
				primary_stack.push(a);
				Ok(mode)
			}

			// ( a -- a a )
			Intrinsic::Dup => {
				let Some(a) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::Manipulation(1));
				};

				mode |= intr_mode_from_type(&a.typ)?;
				primary_stack.push(a.clone());
				primary_stack.push(StackItem::named(a.typ, a.name.clone(), intr_span));
				Ok(mode)
			}

			// ( a b -- a b a )
			Intrinsic::Over => {
				let (Some(b), Some(a)) = (consumer.pop(), consumer.pop()) else {
					return err_invalid_stack!(ExpectedStack::Manipulation(2));
				};

				if a.typ.size() != b.typ.size() {
					return Err(Error::UnmatchedInputsSizes {
						found: consumer.found_sizes(),
						span: intr_span,
					});
				}
				mode |= intr_mode_from_type(&a.typ)?;
				primary_stack.push(a.clone());
				primary_stack.push(b);
				primary_stack.push(StackItem::named(a.typ, a.name, intr_span));
				Ok(mode)
			}

			// ( a -- | a )
			Intrinsic::Sth => {
				let Some(a) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::Manipulation(1));
				};

				mode |= intr_mode_from_type(&a.typ)?;
				secondary_stack.push(a);
				Ok(mode)
			}

			// ( addr -- value )
			Intrinsic::Load => {
				let Some(addr) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::IntrLoad);
				};

				let output = match addr.typ {
					Type::BytePtr(t) => {
						mode |= IntrMode::ABS_BYTE_ADDR;
						*t
					}
					Type::ShortPtr(t) => {
						mode |= IntrMode::ABS_SHORT_ADDR;
						*t
					}
					_ => return err_invalid_stack!(ExpectedStack::IntrLoad),
				};

				mode |= intr_mode_from_type(&output)?;

				primary_stack.push(StackItem::new(output, intr_span));
				Ok(mode)
			}

			// ( value addr -- )
			Intrinsic::Store => {
				let (Some(addr), Some(value)) = (consumer.pop(), consumer.pop()) else {
					return err_invalid_stack!(ExpectedStack::IntrStore);
				};

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
					_ => return err_invalid_stack!(ExpectedStack::IntrStore),
				}

				mode |= intr_mode_from_type(&value.typ)?;
				Ok(mode)
			}

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

				_ => err_invalid_stack!(ExpectedStack::IntrInput),
			},

			// ( value device8 -- )
			Intrinsic::Output => match (consumer.pop(), consumer.pop()) {
				(Some(device8), Some(value)) if device8.typ == Type::Byte => {
					mode |= intr_mode_from_type(&value.typ)?;
					Ok(mode)
				}

				_ => err_invalid_stack!(ExpectedStack::IntrOutput),
			},
		}
	}
	#[must_use]
	fn check_arithmetic_intr(
		&mut self,
		mut mode: IntrMode,
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
			return Err(Error::InvalidStack {
				expected: ExpectedStack::Arithmetic,
				found: consumer.found(),
				error: consumer.stack_error(),
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
				return Err(Error::InvalidStack {
					expected: ExpectedStack::Arithmetic,
					found: consumer.found(),
					error: consumer.stack_error(),
					span: intr_span,
				});
			}
		};
		mode |= intr_mode_from_type(&output)?;

		primary_stack.push(StackItem::new(output, intr_span));

		Ok(mode)
	}

	// ==============================
	// Helper functions
	// ==============================

	pub fn reset_stacks(&mut self) {
		self.ws.reset();
		self.rs.reset();
	}

	pub fn define_label(
		&mut self,
		ctx: &mut Context,
		name: Name,
		block_idx: usize,
		span: Span,
	) -> error::Result<UniqueName> {
		let unique_name = self.symbols.new_unique_name();
		let label = Label::new(unique_name, block_idx, span);
		let prev = ctx.labels.insert(name, label);
		if let Some(prev) = prev {
			Err(Error::InvalidSymbol {
				error: SymbolError::LabelRedefinition,
				defined_at: prev.span,
				span,
			})
		} else {
			Ok(unique_name)
		}
	}
	pub fn undefine_label(&mut self, ctx: &mut Context, name: &Name) {
		let prev = ctx.labels.remove(name);
		if prev.is_none() {
			bug!("unexpected non-existing label {name:?}");
		}
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

	pub fn begin_chained_block(
		&mut self,
		ctx: &mut Context,
		prev_block: &Block,
		branching: bool,
	) -> usize {
		match prev_block {
			Block::Normal {
				expect_ws,
				expect_rs,
				..
			} => {
				let idx = self.begin_block(ctx, branching && true);

				// Restore the stacks to the state before the `else` block
				self.ws.items = expect_ws.clone();
				self.rs.items = expect_rs.clone();

				idx
			}
			Block::Finished => self.begin_block(ctx, branching && false),

			Block::Def { .. } => bug!("else block cannot be a `Block::Def`, but it is"),
		}
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
