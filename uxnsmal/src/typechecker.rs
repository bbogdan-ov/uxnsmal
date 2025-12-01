mod consumer;
mod stack;

use std::collections::HashMap;

pub use consumer::*;
pub use stack::*;
use vec1::{Vec1, vec1};

use crate::{
	ast::{Ast, Def, ElseIf, Expr, FuncArgs, Node, TypeName},
	bug,
	error::{self, Error, ExpectedStack},
	lexer::{Span, Spanned},
	problems::Problems,
	program::{Constant, Data, Function, IntrMode, Intrinsic, Op, Program, Variable},
	symbols::{FuncSignature, Name, SymbolSignature, SymbolsTable, Type, UniqueName},
	warn::Warn,
};

fn intr_mode_from_type(typ: &Type) -> IntrMode {
	match typ.size() {
		0 | 1 => IntrMode::NONE,
		2 => IntrMode::SHORT,
		3.. => todo!("handle type with size > 2"),
	}
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
		checker.symbols.collect(ast).map_err(Problems::one_err)?;

		let res = checker.check_nodes(&ast.nodes, None);
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
	) -> error::Result<()> {
		for node in nodes.iter() {
			match &node.x {
				Node::Expr(expr) => {
					let Some(ctx) = &mut ctx else {
						return Err(Error::IllegalTopLevelExpr(node.span));
					};

					self.check_expr(expr, node.span, ctx)?;
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
	) -> error::Result<()> {
		let cur_block = ctx.cur_block();

		if *cur_block == Block::Finished {
			self.problems.warn(Warn::DeadCode(expr_span));
			return Ok(());
		}

		match expr {
			Expr::Byte(b) => {
				self.ws.push(StackItem::new(Type::Byte, expr_span));
				ctx.ops.push(Op::Byte(*b));
			}
			Expr::Short(s) => {
				self.ws.push(StackItem::new(Type::Short, expr_span));
				ctx.ops.push(Op::Short(*s));
			}
			Expr::String(s) => {
				let item = StackItem::new(Type::ShortPtr(Type::Byte.into()), expr_span);
				self.ws.push(item);

				// Generate IR
				// Insert an unique data for each string literal even if strings contents are the same
				let unique_name = self.symbols.new_unique_name();
				let body = s.as_bytes().into();
				self.program.datas.insert(unique_name, Data { body });

				ctx.ops.push(Op::AbsShortAddrOf(unique_name));
			}
			Expr::Padding(_) => {
				todo!("`Expr::Padding` outside 'data' blocks should error before typecheck stage");
			}

			Expr::Store(name) => self.check_store(name, ctx, expr_span)?,

			Expr::Cast(types) => self.check_cast(types, expr_span)?,

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
				ctx.ops.push(Op::Intrinsic(*intr, mode))
			}
			Expr::Symbol(name) => self.check_symbol(name, expr_span, ctx)?,
			Expr::PtrTo(name) => self.check_ptr_to(name, expr_span, ctx)?,

			Expr::Block { label, body, .. } => {
				let block_idx = self.begin_block(ctx, false);

				let name = label.x.clone();
				let unique_name = self.define_label(ctx, name, block_idx, label.span)?;

				self.check_nodes(body, Some(ctx))?;
				ctx.ops.push(Op::Label(unique_name));

				self.end_block(ctx, expr_span)?;
				self.undefine_label(ctx, &label.x);
			}

			Expr::Jump { label } => {
				let Some(block_label) = ctx.labels.get(&label.x).cloned() else {
					return Err(Error::UnknownLabel(label.span));
				};

				self.jump_to_block(ctx, block_label.block_idx, expr_span)?;
				ctx.ops.push(Op::Jump(block_label.unique_name));
			}
			Expr::Return => {
				self.jump_to_block(ctx, 0, expr_span)?;
				ctx.ops.push(Op::Return);
			}
			Expr::If {
				if_body,
				elseifs,
				else_body,
			} => self.check_if(if_body, elseifs, else_body, ctx, expr_span)?,
			Expr::While { condition, body } => {
				self.check_while(condition, body, ctx, expr_span)?;
			}
		}

		Ok(())
	}

	fn check_symbol(
		&mut self,
		name: &Name,
		symbol_span: Span,
		ctx: &mut Context,
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
					ctx.ops.push(Op::FuncCall(symbol.unique_name));
				}
			},

			SymbolSignature::Var(sig) => {
				// Type check
				self.ws.push(StackItem::new(sig.typ.clone(), symbol_span));

				// Generate IR
				let mut mode = IntrMode::ABS_BYTE_ADDR;
				mode |= intr_mode_from_type(&sig.typ);
				ctx.ops.push(Op::AbsByteAddrOf(symbol.unique_name));
				ctx.ops.push(Op::Intrinsic(Intrinsic::Load, mode));
			}
			SymbolSignature::Const(sig) => {
				// Type check
				self.ws.push(StackItem::new(sig.typ.clone(), symbol_span));

				// Generate IR
				ctx.ops.push(Op::ConstUse(symbol.unique_name));
			}
			SymbolSignature::Data => {
				// Type check
				self.ws.push(StackItem::new(Type::Byte, symbol_span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddrOf(symbol.unique_name));
				ctx.ops
					.push(Op::Intrinsic(Intrinsic::Load, IntrMode::ABS_SHORT_ADDR));
			}

			SymbolSignature::Type(_) => {
				return Err(Error::IllegalUseOfType {
					defined_at: symbol.span,
					span: symbol_span,
				});
			}
		};

		Ok(())
	}

	fn check_ptr_to(
		&mut self,
		name: &Name,
		symbol_span: Span,
		ctx: &mut Context,
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
				ctx.ops.push(Op::AbsShortAddrOf(symbol.unique_name));
			}
			SymbolSignature::Var(sig) => {
				// Type check
				let typ = Type::BytePtr(sig.typ.clone().into());
				self.ws.push(StackItem::new(typ, symbol_span));

				// Generate IR
				ctx.ops.push(Op::AbsByteAddrOf(symbol.unique_name));
			}
			SymbolSignature::Data => {
				// Type check
				let typ = Type::ShortPtr(Type::Byte.into());
				self.ws.push(StackItem::new(typ, symbol_span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddrOf(symbol.unique_name));
			}

			SymbolSignature::Const(_) => {
				return Err(Error::IllegalPtrToConst {
					defined_at: symbol_span,
					span: symbol_span,
				});
			}

			SymbolSignature::Type(_) => {
				return Err(Error::IllegalUseOfType {
					defined_at: symbol.span,
					span: symbol_span,
				});
			}
		};

		Ok(())
	}

	fn check_store(
		&mut self,
		name: &Name,
		ctx: &mut Context,
		expr_span: Span,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.table.get(name) else {
			return Err(Error::UnknownSymbol(expr_span));
		};

		let mut mode = IntrMode::NONE;

		let expect_typ: &Type = match &symbol.signature {
			SymbolSignature::Func(_) | SymbolSignature::Const(_) | SymbolSignature::Type(_) => {
				return Err(Error::InvalidStoreSymbol {
					defined_at: symbol.span,
					span: expr_span,
				});
			}

			SymbolSignature::Var(sig) => {
				mode |= IntrMode::ABS_BYTE_ADDR;
				ctx.ops.push(Op::AbsByteAddrOf(symbol.unique_name));

				&sig.typ
			}
			SymbolSignature::Data => {
				mode |= IntrMode::ABS_SHORT_ADDR;
				ctx.ops.push(Op::AbsShortAddrOf(symbol.unique_name));
				&Type::Byte
			}
		};

		let mut consumer = self.ws.consumer(expr_span);
		match consumer.pop() {
			Some(value) if value.typ == *expect_typ => {
				mode |= intr_mode_from_type(&value.typ);
				ctx.ops.push(Op::Intrinsic(Intrinsic::Store, mode));
				Ok(())
			}
			_ => Err(Error::InvalidStack {
				expected: ExpectedStack::Store(expect_typ.clone()),
				found: consumer.found(),
				stack: consumer.stack_error(),
				span: expr_span,
			}),
		}
	}

	// TODO: casting should also probaly work with the return stack?
	// Currently i don't know how to syntactically mark casting for return stack.
	fn check_cast(
		&mut self,
		types: &Box<[Spanned<TypeName>]>,
		expr_span: Span,
	) -> error::Result<()> {
		let types = types
			.iter()
			.cloned()
			.map(|t| Ok(Spanned::new(t.x.to_type(&self.symbols, t.span)?, t.span)))
			.collect::<error::Result<Vec<Spanned<Type>>>>()?;

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

		Ok(())
	}

	fn check_if(
		&mut self,
		if_body: &Box<[Spanned<Node>]>,
		elseifs: &Box<[ElseIf]>,
		else_body: &Option<Box<[Spanned<Node>]>>,
		ctx: &mut Context,
		expr_span: Span,
	) -> error::Result<()> {
		self.consume_condition(expr_span)?;

		// TODO!: refactor this code, this is kinda mess

		if let Some(else_body) = else_body
			&& !elseifs.is_empty()
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

			let mut if_block = ctx.pop_block(expr_span);
			self.finish_block(&mut if_block);

			for (i, elseif) in elseifs.iter().enumerate() {
				ctx.ops.push(Op::Label(next_label));

				self.check_condition(&elseif.condition, ctx, expr_span)?;

				let elseif_begin_label = self.symbols.new_unique_name();
				ctx.ops.push(Op::JumpIf(elseif_begin_label));

				if i < elseifs.len() - 1 {
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
				self.check_nodes(&elseif.body, Some(ctx))?;
				self.end_block(ctx, expr_span)?;

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
				self.check_nodes(else_body, Some(ctx))?;
			}
			self.end_block(ctx, expr_span)?;

			ctx.ops.push(Op::Label(end_label));
		} else if !elseifs.is_empty() {
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
			self.end_block(ctx, expr_span)?;

			for (i, elseif) in elseifs.iter().enumerate() {
				ctx.ops.push(Op::Label(next_label));

				self.check_condition(&elseif.condition, ctx, expr_span)?;

				let elseif_begin_label = self.symbols.new_unique_name();
				ctx.ops.push(Op::JumpIf(elseif_begin_label));

				if i < elseifs.len() - 1 {
					next_label = self.symbols.new_unique_name();
					ctx.ops.push(Op::Jump(next_label));
				} else {
					ctx.ops.push(Op::Jump(end_label));
				}

				ctx.ops.push(Op::Label(elseif_begin_label));

				// Check `elif` body
				self.begin_block(ctx, true);
				self.check_nodes(&elseif.body, Some(ctx))?;
				self.end_block(ctx, expr_span)?;

				ctx.ops.push(Op::Jump(end_label));
			}

			ctx.ops.push(Op::Label(end_label));
		} else if let Some(else_body) = else_body {
			// `if {} else {}`
			// Code below may be a bit confusing

			let if_begin_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();

			// Take snapshot before the `else` block
			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::JumpIf(if_begin_label));

				// `else` block
				self.check_nodes(else_body, Some(ctx))?;
				ctx.ops.push(Op::Jump(end_label));
			}

			let else_block = ctx.pop_block(expr_span);
			self.begin_chained_block(ctx, &else_block, true);
			{
				// `if` block
				ctx.ops.push(Op::Label(if_begin_label));
				self.check_nodes(if_body, Some(ctx))?;
				ctx.ops.push(Op::Label(end_label));
			}
			// Compare stacks at the end of the `if` and `else` blocks to be equal
			self.end_block(ctx, expr_span)?;
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
			self.end_block(ctx, expr_span)?;
		}

		Ok(())
	}

	fn check_while(
		&mut self,
		condition: &Box<[Spanned<Node>]>,
		body: &Box<[Spanned<Node>]>,
		ctx: &mut Context,
		expr_span: Span,
	) -> error::Result<()> {
		let again_label = self.symbols.new_unique_name();
		let continue_label = self.symbols.new_unique_name();
		let end_label = self.symbols.new_unique_name();

		ctx.ops.push(Op::Label(again_label));

		self.check_condition(condition, ctx, expr_span)?;

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
		self.end_block(ctx, expr_span)?;

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
					stack: consumer.stack_error(),
					span,
				});
			}
		}
		Ok(())
	}
	fn check_condition(
		&mut self,
		condition: &Box<[Spanned<Node>]>,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		self.begin_block(ctx, true);

		self.check_nodes(condition, Some(ctx))?;
		self.consume_condition(span)?;

		self.end_block(ctx, span)?;
		Ok(())
	}

	pub fn check_def(&mut self, def: &Def, def_span: Span) -> error::Result<()> {
		self.reset_stacks();

		let symbol = match self.symbols.table.get(def.name()) {
			Some(symbol) => symbol,
			None => {
				let name = def.name().clone();
				let sig = def.to_signature(&self.symbols, def_span)?;
				// NOTE: ignore returning Result because `define_symbol` returns an error only when
				// symbol is being redifined
				let _ = self.symbols.define_symbol(name, sig, def_span);
				&self.symbols.table[def.name()]
			}
		};
		let unique_name = symbol.unique_name;

		match def {
			Def::Func(def) => {
				let expect_ws: Vec<Type> = match &def.args {
					FuncArgs::Vector => {
						vec![]
					}
					FuncArgs::Proc { inputs, outputs } => {
						// Push function inputs onto the stack
						for input in inputs.iter() {
							let typ = input.typ.clone().to_type(&self.symbols, input.span)?;
							let name = input.name.clone();
							self.ws.push(StackItem::named(typ, name, input.span));
						}

						outputs
							.iter()
							.map(|t| t.typ.clone().to_type(&self.symbols, t.span))
							.collect::<error::Result<Vec<Type>>>()?
					}
				};

				// Check function body
				let mut ctx = Context::new(expect_ws, vec![]);
				self.check_nodes(&def.body, Some(&mut ctx))?;

				self.compare_block(ctx.blocks.first(), def_span)?;

				// Generate IR
				let func = Function {
					is_vector: matches!(def.args, FuncArgs::Vector),
					body: ctx.ops.into(),
				};

				if def.name.as_ref() == "on-reset" {
					self.program.reset_func = Some((unique_name, func));
				} else {
					self.program.funcs.insert(unique_name, func);
				}
			}

			Def::Var(def) => {
				// Generate IR
				let typ = def.typ.x.clone().to_type(&self.symbols, def.typ.span)?;
				let size = typ.size();
				if size > u8::MAX as u16 {
					// TODO: also error when out of memeory
					todo!("'var is too large' error");
				}

				let var = Variable { size: size as u8 };
				self.program.vars.insert(unique_name, var);
			}

			Def::Const(def) => {
				// Type check
				let typ = def.typ.x.clone().to_type(&self.symbols, def.typ.span)?;
				let mut ctx = Context::new(vec![typ], vec![]);
				self.check_nodes(&def.body, Some(&mut ctx))?;
				self.compare_block(ctx.blocks.first(), def_span)?;

				// Generate IR
				let cnst = Constant {
					body: ctx.ops.into(),
				};
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
						_ => return Err(Error::NoCodeInDataYet(node.span)),
					}
				}

				let data = Data { body: bytes.into() };
				self.program.datas.insert(unique_name, data);
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
					mode |= intr_mode_from_type(&a.typ);
					primary_stack.push(StackItem::new(a.typ, intr_span));
					Ok(mode)
				}

				_ => err_invalid_stack!(ExpectedStack::IntrInc),
			},

			// ( a shift8 -- c )
			Intrinsic::Shift => match (consumer.pop(), consumer.pop()) {
				(Some(shift8), Some(a)) if shift8.typ == Type::Byte => {
					mode |= intr_mode_from_type(&a.typ);
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

				mode |= intr_mode_from_type(&output);

				primary_stack.push(StackItem::new(output, intr_span));
				Ok(mode)
			}

			// ( a b -- bool8 )
			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				let (Some(b), Some(a)) = (consumer.pop(), consumer.pop()) else {
					return err_invalid_stack!(ExpectedStack::Comparison);
				};

				mode |= intr_mode_from_type(&a.typ);

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

				mode |= intr_mode_from_type(&a.typ);
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
				mode |= intr_mode_from_type(&a.typ);
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
				mode |= intr_mode_from_type(&a.typ);
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
				mode |= intr_mode_from_type(&a.typ);
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

				mode |= intr_mode_from_type(&a.typ);
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
				mode |= intr_mode_from_type(&a.typ);
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

				mode |= intr_mode_from_type(&a.typ);
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

				mode |= intr_mode_from_type(&output);

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

				mode |= intr_mode_from_type(&value.typ);
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
					mode |= intr_mode_from_type(&value.typ);
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
				return Err(Error::InvalidStack {
					expected: ExpectedStack::Arithmetic,
					found: consumer.found(),
					stack: consumer.stack_error(),
					span: intr_span,
				});
			}
		};
		mode |= intr_mode_from_type(&output);

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
			Err(Error::LabelRedefinition {
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
			unreachable!("unexpected unexisting label {name:?}");
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
