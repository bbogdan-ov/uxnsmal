mod consumer;
mod stack;

use std::{collections::HashMap, rc::Rc};

pub use consumer::*;
pub use stack::*;
use vec1::{Vec1, vec1};

use crate::{
	ast::{Ast, Def, ElseBlock, ElseIfBlock, Expr, Node},
	bug,
	error::{self, Error, ExpectedStack, SymbolError},
	lexer::{Span, Spanned},
	problems::Problems,
	program::{Constant, Data, Function, IntrMode, Intrinsic, Op, Program, Variable},
	symbols::{
		ConstSymbol, ConstSymbolKind, DataSymbol, EnumSymbolVariant, FuncSignature, FuncSymbol,
		Name, NamedType, Symbol, SymbolKind, SymbolsTable, Type, TypeSymbol, UniqueName,
		UnsizedType, VarSymbol,
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
			program: Program::default(),
			problems: Problems::default(),

			ws: Stack::default(),
			rs: Stack::default(),
		}
	}
}
impl Typechecker {
	pub fn check(ast: &mut Ast) -> Result<(Program, Problems), Problems> {
		let mut symbols = SymbolsTable::default();
		let mut checker = Self::default();
		checker
			.collect(ast, &mut symbols)
			.map_err(Problems::one_err)?;

		let res = checker.check_nodes(&ast.nodes, &mut symbols, None);
		checker.problems.err_or_ok(res);

		if checker.problems.errors.is_empty() {
			Ok((checker.program, checker.problems))
		} else {
			Err(checker.problems)
		}
	}

	/// Walk through AST and collect all top-level symbol definitions
	fn collect(&mut self, ast: &mut Ast, symbols: &mut SymbolsTable) -> error::Result<()> {
		for node in ast.nodes.iter_mut() {
			let Node::Def(def) = node else {
				continue;
			};

			match def {
				Def::Type(def) => {
					let inherits = def.inherits.x.clone();
					let inherits = inherits.into_sized(symbols, def.inherits.span)?;
					let symbol = Symbol::Type(Rc::new(TypeSymbol::Normal {
						inherits,
						defined_at: def.name.span,
					}));
					symbols.define_symbol(def.name.x.clone(), symbol)?;
				}

				Def::Enum(def) => {
					match def.inherits.x {
						UnsizedType::Byte | UnsizedType::Short => (/* ok */),
						_ => return Err(Error::InvalidEnumType(def.inherits.span)),
					}

					let inherits = def.inherits.x.clone();
					let inherits = inherits.into_sized(&symbols, def.inherits.span)?;
					let enum_typ = Type::Custom {
						name: def.name.x.clone(),
						size: inherits.size(),
					};

					// Collect enum variants
					let mut variants = HashMap::default();
					for vari in def.variants.iter() {
						let unique_name = symbols.new_unique_name();
						let symbol = Rc::new(ConstSymbol {
							kind: ConstSymbolKind::EnumVariant,
							unique_name,
							typ: enum_typ.clone(),
							defined_at: vari.name.span,
						});

						variants.insert(
							vari.name.x.clone(),
							EnumSymbolVariant {
								symbol: Rc::clone(&symbol),
							},
						);

						let name = Name::new(&format!("{}.{}", def.name.x, vari.name.x));
						symbols.define_symbol(name, Symbol::Const(symbol))?;
					}

					// Define enum type
					let symbol = Rc::new(TypeSymbol::Enum {
						typ: enum_typ,
						inherits,
						variants,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));
					symbols.define_symbol(def.name.x.clone(), Symbol::Type(symbol))?;
				}

				Def::Func(def) => {
					let symbol = Rc::new(FuncSymbol {
						unique_name: symbols.new_unique_name(),
						signature: def.signature.x.clone().into_sized(&symbols)?,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));
					symbols.define_symbol(def.name.x.clone(), Symbol::Func(symbol))?;
				}
				Def::Var(def) => {
					let typ = def.typ.x.clone();
					let typ = typ.into_sized(&symbols, def.typ.span)?;
					let symbol = Rc::new(VarSymbol {
						unique_name: symbols.new_unique_name(),
						typ,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));
					symbols.define_symbol(def.name.x.clone(), Symbol::Var(symbol))?;
				}
				Def::Const(def) => {
					let typ = def.typ.x.clone();
					let typ = typ.into_sized(&symbols, def.typ.span)?;
					let symbol = Rc::new(ConstSymbol {
						kind: ConstSymbolKind::Normal,
						unique_name: symbols.new_unique_name(),
						typ,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));
					symbols.define_symbol(def.name.x.clone(), Symbol::Const(symbol))?;
				}
				Def::Data(def) => {
					let symbol = Rc::new(DataSymbol {
						unique_name: symbols.new_unique_name(),
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));
					symbols.define_symbol(def.name.x.clone(), Symbol::Data(symbol))?;
				}
			}
		}

		Ok(())
	}

	fn check_nodes(
		&mut self,
		nodes: &[Node],
		symbols: &mut SymbolsTable,
		mut ctx: Option<&mut Context>,
	) -> error::Result<()> {
		for node in nodes.iter() {
			match node {
				Node::Expr(expr) => {
					let Some(ctx) = &mut ctx else {
						return Err(Error::IllegalTopLevelExpr(expr.span()));
					};

					self.check_expr(expr, symbols, ctx)?;
				}
				Node::Def(def) => {
					if ctx.is_some() {
						return Err(Error::NoLocalDefsYet(def.span()));
					}

					let res = self.check_def(def, symbols, def.span());
					self.problems.err_or_ok(res);
				}
			}
		}
		Ok(())
	}
	pub fn check_expr(
		&mut self,
		expr: &Expr,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
	) -> error::Result<()> {
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
				let unique_name = symbols.new_unique_name();
				let body = string.as_bytes().into();
				self.program.datas.insert(unique_name, Data { body });

				ctx.ops.push(Op::AbsShortAddrOf(unique_name));
			}
			Expr::Padding { .. } => {
				todo!("`Expr::Padding` outside 'data' blocks should error before typecheck stage");
			}

			Expr::Store { symbol, span } => self.check_store(symbol, symbols, ctx, *span)?,

			Expr::Cast { types, span } => self.check_cast(types.as_slice(), symbols, *span)?,

			Expr::Bind { names, span } => {
				if names.len() > self.ws.len() {
					return Err(Error::TooManyBindings(*span));
				}

				for (i, name) in names.iter().rev().enumerate() {
					let len = self.ws.items.len();
					let item = &mut self.ws.items[len - 1 - i];

					if name.x.as_ref() == "_" {
						item.name = None;
						item.renamed_at = Some(name.span);
					} else {
						item.name = Some(name.x.clone());
						item.renamed_at = Some(name.span);
					}
				}
			}

			Expr::ExpectBind { names, span } => {
				self.ws
					.consumer_keep(*span)
					.compare_names(names.iter().map(|n| match n.x.as_ref() {
						"_" => None,
						_ => Some(&n.x),
					}))?;
			}

			Expr::Intrinsic { kind, mode, span } => {
				let mut mode = *mode;
				mode |= self.check_intrinsic(*kind, mode, *span)?;

				// Generate IR
				ctx.ops.push(Op::Intrinsic(*kind, mode))
			}
			Expr::Symbol { name, span } => self.check_symbol(name, symbols, ctx, *span)?,
			Expr::PtrTo { name, span } => self.check_ptr_to(name, symbols, ctx, *span)?,

			Expr::Block {
				label, body, span, ..
			} => {
				let block_idx = self.begin_block(ctx, false);

				let name = label.x.clone();
				let unique_name = self.define_label(symbols, ctx, name, block_idx, label.span)?;

				self.check_nodes(body, symbols, Some(ctx))?;
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
			} => self.check_if(
				if_body,
				*if_span,
				elif_blocks,
				else_block,
				symbols,
				ctx,
				*span,
			)?,
			Expr::While {
				condition,
				body,
				span,
			} => {
				self.check_while(condition, body, symbols, ctx, *span)?;
			}
		}

		Ok(())
	}

	fn check_symbol(
		&mut self,
		name: &Name,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let Some(symbol) = symbols.table.get(name) else {
			return Err(Error::UnknownSymbol(span));
		};

		match symbol {
			Symbol::Type(typ) => {
				return Err(Error::InvalidSymbol {
					error: SymbolError::IllegalUse {
						found: SymbolKind::Type,
					},
					defined_at: typ.defined_at(),
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
					self.ws
						.consumer(span)
						.compare(inputs.iter().map(|t| &t.typ.x), StackMatch::Tail)?;

					// Push function outputs
					for output in outputs.iter() {
						self.ws.push(StackItem::new(output.typ.x.clone(), span));
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
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let Some(symbol) = symbols.table.get(&name.x) else {
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
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let Some(symbol) = symbols.table.get(&name.x) else {
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
	fn check_cast(
		&mut self,
		types: &[NamedType<UnsizedType>],
		symbols: &mut SymbolsTable,
		span: Span,
	) -> error::Result<()> {
		let items: Vec<StackItem> = types
			.iter()
			.cloned()
			.map(|t| {
				let typ = t.typ.x.into_sized(&symbols, t.typ.span)?;
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
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		self.consume_condition(span)?;

		// TODO!: refactor this code, this is kinda mess

		if let Some(else_block) = else_block
			&& !elif_blocks.is_empty()
		{
			// `if {} elif {} else {}`
			let if_begin_label = symbols.new_unique_name();
			let else_begin_label = symbols.new_unique_name();
			let end_label = symbols.new_unique_name();
			let mut next_label = symbols.new_unique_name();

			ctx.ops.push(Op::JumpIf(if_begin_label));
			ctx.ops.push(Op::Jump(next_label));

			let ws_before = self.ws.items.clone();
			let rs_before = self.rs.items.clone();

			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::Label(if_begin_label));
				self.check_nodes(if_body, symbols, Some(ctx))?;
				ctx.ops.push(Op::Jump(end_label));
			}

			let ws_to_expect = self.ws.items.clone();
			let rs_to_expect = self.rs.items.clone();

			let mut if_block = ctx.pop_block(if_span);
			self.finish_block(&mut if_block);

			for (i, elif) in elif_blocks.iter().enumerate() {
				ctx.ops.push(Op::Label(next_label));

				self.check_condition(&elif.condition, symbols, ctx, elif.span)?;

				let elseif_begin_label = symbols.new_unique_name();
				ctx.ops.push(Op::JumpIf(elseif_begin_label));

				if i < elif_blocks.len() - 1 {
					next_label = symbols.new_unique_name();
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
				self.check_nodes(&elif.body, symbols, Some(ctx))?;
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
				self.check_nodes(&else_block.body, symbols, Some(ctx))?;
			}
			self.end_block(ctx, else_block.span)?;

			ctx.ops.push(Op::Label(end_label));
		} else if !elif_blocks.is_empty() {
			// `if {} elif {}`
			let if_begin_label = symbols.new_unique_name();
			let end_label = symbols.new_unique_name();
			let mut next_label = symbols.new_unique_name();

			ctx.ops.push(Op::JumpIf(if_begin_label));
			ctx.ops.push(Op::Jump(next_label));

			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::Label(if_begin_label));
				self.check_nodes(if_body, symbols, Some(ctx))?;
				ctx.ops.push(Op::Jump(end_label));
			}
			self.end_block(ctx, if_span)?;

			for (i, elif) in elif_blocks.iter().enumerate() {
				ctx.ops.push(Op::Label(next_label));

				self.check_condition(&elif.condition, symbols, ctx, elif.span)?;

				let elseif_begin_label = symbols.new_unique_name();
				ctx.ops.push(Op::JumpIf(elseif_begin_label));

				if i < elif_blocks.len() - 1 {
					next_label = symbols.new_unique_name();
					ctx.ops.push(Op::Jump(next_label));
				} else {
					ctx.ops.push(Op::Jump(end_label));
				}

				ctx.ops.push(Op::Label(elseif_begin_label));

				// Check `elif` body
				self.begin_block(ctx, true);
				self.check_nodes(&elif.body, symbols, Some(ctx))?;
				self.end_block(ctx, elif.span)?;

				ctx.ops.push(Op::Jump(end_label));
			}

			ctx.ops.push(Op::Label(end_label));
		} else if let Some(else_block) = else_block {
			// `if {} else {}`
			// Code below may be a bit confusing

			let if_begin_label = symbols.new_unique_name();
			let end_label = symbols.new_unique_name();

			// Take snapshot before the `else` block
			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::JumpIf(if_begin_label));

				// `else` block
				self.check_nodes(&else_block.body, symbols, Some(ctx))?;
				ctx.ops.push(Op::Jump(end_label));
			}

			let else_block = ctx.pop_block(else_block.span);
			self.begin_chained_block(ctx, &else_block, true);
			{
				// `if` block
				ctx.ops.push(Op::Label(if_begin_label));
				self.check_nodes(if_body, symbols, Some(ctx))?;
				ctx.ops.push(Op::Label(end_label));
			}
			// Compare stacks at the end of the `if` and `else` blocks to be equal
			self.end_block(ctx, if_span)?;
		} else {
			// `if {}`
			let if_begin_label = symbols.new_unique_name();
			let end_label = symbols.new_unique_name();

			self.begin_block(ctx, true);
			{
				ctx.ops.push(Op::JumpIf(if_begin_label));
				ctx.ops.push(Op::Jump(end_label));
				ctx.ops.push(Op::Label(if_begin_label));

				self.check_nodes(if_body, symbols, Some(ctx))?;

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
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let again_label = symbols.new_unique_name();
		let continue_label = symbols.new_unique_name();
		let end_label = symbols.new_unique_name();

		ctx.ops.push(Op::Label(again_label));

		self.check_condition(condition, symbols, ctx, span)?;

		ctx.ops.push(Op::JumpIf(continue_label));
		ctx.ops.push(Op::Jump(end_label));
		ctx.ops.push(Op::Label(continue_label));

		self.begin_block(ctx, true);
		{
			// Body
			self.check_nodes(body, symbols, Some(ctx))?;

			ctx.ops.push(Op::Jump(again_label));
			ctx.ops.push(Op::Label(end_label));
		}
		self.end_block(ctx, span)?;

		Ok(())
	}

	fn consume_condition(&mut self, span: Span) -> error::Result<()> {
		let mut consumer = self.ws.consumer(span);
		match consumer.pop() {
			Some(bool8) if bool8.typ == Type::Byte => Ok(()),
			_ => Err(Error::InvalidStack {
				expected: ExpectedStack::Condition,
				found: consumer.found(),
				error: consumer.stack_error(),
				span,
			}),
		}
	}
	fn check_condition(
		&mut self,
		condition: &Spanned<Vec<Node>>,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		self.begin_block(ctx, true);

		self.check_nodes(&condition.x, symbols, Some(ctx))?;
		self.consume_condition(span)?;

		self.end_block(ctx, span)?;
		Ok(())
	}

	pub fn check_def(
		&mut self,
		def: &Def,
		symbols: &mut SymbolsTable,
		def_span: Span,
	) -> error::Result<()> {
		self.reset_stacks();

		macro_rules! s {
			($symbol:expr, $span:expr) => {
				$symbol
					.as_ref()
					.unwrap_or_else(|| bug!("unexpected `None` symbol {}", $span))
			};
		}

		match def {
			Def::Type(_) => (/* do nothing */),

			Def::Func(def) => {
				let symbol = s!(def.symbol, def.span);

				let expect_ws: Vec<Type> = match &symbol.signature {
					FuncSignature::Vector => {
						vec![]
					}
					FuncSignature::Proc { inputs, outputs } => {
						// Push function inputs onto the stack
						for input in inputs.iter() {
							let item = StackItem::named(
								input.typ.x.clone(),
								input.name.clone().map(|n| n.x),
								input.typ.span,
							);
							self.ws.push(item);
						}

						outputs.iter().map(|t| t.typ.x.clone()).collect()
					}
				};

				// Check function body
				let mut ctx = Context::new(expect_ws, vec![]);
				self.check_nodes(&def.body, symbols, Some(&mut ctx))?;

				self.compare_block(ctx.blocks.first(), def_span)?;

				// Generate IR
				let func = Function {
					is_vector: matches!(def.signature.x, FuncSignature::Vector),
					body: ctx.ops.into(),
				};

				if def.name.x.as_ref() == "on-reset" {
					self.program.reset_func = Some((symbol.unique_name, func));
				} else {
					self.program.funcs.insert(symbol.unique_name, func);
				}
			}

			Def::Var(def) => {
				let symbol = s!(def.symbol, def.span);

				// Generate IR
				let size = symbol.typ.size();
				if size > u8::MAX as u16 {
					// TODO: also error when out of memeory
					todo!("'var is too large' error");
				}

				let var = Variable { size: size as u8 };
				self.program.vars.insert(symbol.unique_name, var);
			}

			Def::Const(def) => {
				let symbol = s!(def.symbol, def.span);

				// Type check
				let mut ctx = Context::new(vec![symbol.typ.clone()], vec![]);
				self.check_nodes(&def.body, symbols, Some(&mut ctx))?;
				self.compare_block(ctx.blocks.first(), def_span)?;

				// Generate IR
				let cnst = Constant {
					body: ctx.ops.into(),
				};
				self.program.consts.insert(symbol.unique_name, cnst);
			}

			Def::Data(def) => {
				let symbol = s!(def.symbol, def.span);

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

			Def::Enum(def) => {
				let symbol = s!(def.symbol, def.span);
				let TypeSymbol::Enum { typ, variants, .. } = symbol.as_ref() else {
					bug!("unexpected non-enum type at {}", def.span);
				};

				let mut prev_vari_name: Option<UniqueName> = None;
				let is_short = symbol.inherits().size() == 2;

				for vari in def.variants.iter() {
					self.reset_stacks();

					let Some(vari_symbol) = variants.get(&vari.name.x) else {
						bug!(
							"unexpected non-existing enum variant symbol at {}",
							vari.name.span
						);
					};
					let unique_name = vari_symbol.symbol.unique_name;

					let ops: Vec<Op>;
					if let Some(body) = &vari.body {
						// Type check variant body
						let mut ctx = Context::new(vec![typ.clone()], vec![]);
						self.check_nodes(body, symbols, Some(&mut ctx))?;
						self.compare_block(ctx.blocks.first(), vari.name.span)?;
						ops = ctx.ops;
					} else {
						match prev_vari_name {
							Some(prev) if is_short => {
								ops = vec![
									Op::ConstUse(prev),
									Op::Byte(1),
									Op::Intrinsic(Intrinsic::Add, IntrMode::NONE),
								]
							}
							None if is_short => ops = vec![Op::Short(0)],

							Some(prev) => {
								ops = vec![
									Op::ConstUse(prev),
									Op::Short(1),
									Op::Intrinsic(Intrinsic::Add, IntrMode::SHORT),
								]
							}
							None => ops = vec![Op::Byte(0)],
						}
					}

					// Generate IR
					let cnst = Constant { body: ops };
					self.program.consts.insert(unique_name, cnst);
					prev_vari_name = Some(unique_name);
				}
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
				let Some(addr) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::IntrStoreEmpty);
				};
				let Some(value) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::IntrStore(addr.typ));
				};

				match addr.typ {
					Type::BytePtr(t) if *t == value.typ => {
						mode |= IntrMode::ABS_BYTE_ADDR;
					}
					Type::ShortPtr(t) if *t == value.typ => {
						mode |= IntrMode::ABS_SHORT_ADDR;
					}
					Type::BytePtr(_) | Type::ShortPtr(_) => {
						return err_invalid_stack!(ExpectedStack::IntrStore(addr.typ));
					}
					_ => return err_invalid_stack!(ExpectedStack::IntrStoreEmpty),
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
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		name: Name,
		block_idx: usize,
		span: Span,
	) -> error::Result<UniqueName> {
		let unique_name = symbols.new_unique_name();
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
				let mut ws_consumer = self.ws.consumer_keep(span);
				ws_consumer.compare(expect_ws.iter(), StackMatch::Exact)?;
				ws_consumer.compare_names(expect_ws.iter().map(|t| t.name.as_ref()))?;

				let mut rs_consumer = self.rs.consumer_keep(span);
				rs_consumer.compare(expect_rs.iter(), StackMatch::Exact)?;
				rs_consumer.compare_names(expect_rs.iter().map(|t| t.name.as_ref()))?;
			}
			Block::Def {
				expect_ws,
				expect_rs,
			} => {
				self.ws
					.consumer_keep(span)
					.compare(expect_ws.iter(), StackMatch::Exact)?;
				self.rs
					.consumer_keep(span)
					.compare(expect_rs.iter(), StackMatch::Exact)?;
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
