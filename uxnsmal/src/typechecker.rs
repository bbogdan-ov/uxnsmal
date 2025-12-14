mod consumer;
mod context;
mod stack;

use std::{collections::HashMap, iter, rc::Rc};

pub use consumer::*;
pub use context::*;
pub use stack::*;

use crate::{
	ast::{Ast, Def, Expr, Node},
	bug,
	error::{self, CastError, Error, ExpectedStack, SymbolError},
	lexer::{Span, Spanned},
	problems::Problems,
	program::{
		AddrMode, Constant, Data, Function, IntrMode, Intrinsic, Op, Ops, Program, Variable,
	},
	symbols::{
		ConstSymbol, CustomTypeSymbol, DataSymbol, EnumTypeSymbol, EnumVariant, FuncSignature,
		FuncSymbol, NamedType, ResolvedAccess, StructField, StructTypeSymbol, Symbol, SymbolAccess,
		SymbolsTable, Type, TypeSymbol, UniqueName, UnsizedType, VarSymbol, enum_type,
	},
	warn::Warn,
};

// TODO!: i am not really happy with the current "assert-based" programming.
// I should utilize Rust's cool type system to guarantee symbols existance,
// proper scope ending and so on.

/// Typechecker
/// Performs type-checking of the specified AST and generates
/// an intermediate representation (IR) program
pub struct Typechecker {
	program: Program,
	problems: Problems,
}
impl Default for Typechecker {
	fn default() -> Self {
		Self {
			program: Program::default(),
			problems: Problems::default(),
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

		let res = checker.check_nodes_toplevel(&ast.nodes, &mut symbols);
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
					let symbol = TypeSymbol::Normal(Rc::new(CustomTypeSymbol {
						name: def.name.x.clone(),
						inherits,
						defined_at: def.name.span,
					}));
					symbols.define_symbol(def.name.x.clone(), Symbol::Type(symbol))?;
				}

				Def::Enum(def) => {
					match def.inherits.x {
						UnsizedType::Byte | UnsizedType::Short => (/* ok */),
						_ => return Err(Error::InvalidEnumType(def.inherits.span)),
					}

					let inherits = def.inherits.x.clone();
					let inherits = inherits.into_sized(&symbols, def.inherits.span)?;

					// Collect enum variants
					let mut variants = HashMap::default();
					for vari in def.variants.iter() {
						let unique_name = symbols.new_unique_name();
						let v = EnumVariant {
							name: vari.name.x.clone(),
							unique_name,
							defined_at: vari.name.span,
						};

						variants.insert(vari.name.x.clone(), v);
					}

					// Define enum type
					let symbol = Rc::new(EnumTypeSymbol {
						name: def.name.x.clone(),
						untyped: def.untyped,
						inherits,
						variants,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));
					symbols.define_symbol(
						def.name.x.clone(),
						Symbol::Type(TypeSymbol::Enum(symbol)),
					)?;
				}

				Def::Struct(def) => {
					let mut struct_size: u16 = 0;

					// Collect struct fields
					let mut fields = HashMap::default();
					for field in def.fields.iter() {
						let typ = field
							.typ
							.x
							.clone()
							.into_complex_sized(symbols, field.span)?;

						let struct_field = StructField {
							typ: Spanned::new(typ, field.typ.span),
							offset: struct_size,
							defined_at: field.name.span,
						};
						struct_size += struct_field.typ.x.size(struct_field.typ.span)?;
						fields.insert(field.name.x.clone(), struct_field);
					}

					// Define struct type
					let symbol = Rc::new(StructTypeSymbol {
						name: def.name.x.clone(),
						fields,
						size: struct_size,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));
					symbols.define_symbol(
						def.name.x.clone(),
						Symbol::Type(TypeSymbol::Struct(symbol)),
					)?;
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
					let typ = typ.into_complex_sized(&symbols, def.typ.span)?;
					let symbol = Rc::new(VarSymbol {
						unique_name: symbols.new_unique_name(),
						in_rom: def.in_rom,
						typ: Spanned::new(typ, def.typ.span),
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));
					symbols.define_symbol(def.name.x.clone(), Symbol::Var(symbol))?;
				}
				Def::Const(def) => {
					let typ = def.typ.x.clone();
					let typ = typ.into_sized(&symbols, def.typ.span)?;
					let symbol = Rc::new(ConstSymbol {
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

	fn check_nodes_toplevel(
		&mut self,
		nodes: &[Node],
		symbols: &mut SymbolsTable,
	) -> error::Result<()> {
		for node in nodes.iter() {
			match node {
				Node::Expr(expr) => return Err(Error::IllegalTopLevelExpr(expr.span())),
				Node::Def(def) => {
					let res = self.check_def(def, symbols);
					self.problems.err_or_ok(res);
				}
			}
		}
		Ok(())
	}
	fn check_nodes(
		&mut self,
		nodes: &[Node],
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		block: &mut Block,
	) -> error::Result<()> {
		for node in nodes.iter() {
			match node {
				Node::Expr(expr) => self.check_expr(expr, symbols, ctx, block)?,
				Node::Def(def) => return Err(Error::NoLocalDefsYet(def.span())),
			}
		}
		Ok(())
	}
	pub fn check_expr(
		&mut self,
		expr: &Expr,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		block: &mut Block,
	) -> error::Result<()> {
		if block.state == BlockState::Finished {
			self.problems.warn(Warn::DeadCode(expr.span()));
			return Ok(());
		};

		match expr {
			Expr::Byte { value, span } => {
				ctx.ws.push(StackItem::new(Type::Byte, *span));
				ctx.ops.push(Op::Byte(*value));
			}
			Expr::Short { value, span } => {
				ctx.ws.push(StackItem::new(Type::Short, *span));
				ctx.ops.push(Op::Short(*value));
			}
			Expr::String { string, span } => {
				let item = StackItem::new(Type::short_ptr(Type::Byte), *span);
				ctx.ws.push(item);

				// Generate IR
				// Insert an unique data for each string literal even if strings contents are the same
				let unique_name = symbols.new_unique_name();
				let body = string.as_bytes().into();
				self.program.datas.insert(unique_name, Data { body });

				ctx.ops.push(Op::AbsShortAddr {
					name: unique_name,
					offset: 0,
				});
			}
			Expr::Padding { .. } => {
				todo!("`Expr::Padding` outside 'data' blocks should error before typecheck stage");
			}

			Expr::Store { access, span } => self.check_store(access, symbols, ctx, *span)?,

			Expr::Cast { types, span } => self.check_cast(types.as_slice(), symbols, ctx, *span)?,

			Expr::Bind { names, span } => {
				if names.len() > ctx.ws.len() {
					return Err(Error::TooManyBindings(*span));
				}

				for (i, name) in names.iter().rev().enumerate() {
					let len = ctx.ws.items.len();
					let item = &mut ctx.ws.items[len - 1 - i];

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
				ctx.ws.consumer_keep(*span).compare_names(names.iter().map(
					|n| match n.x.as_ref() {
						"_" => None,
						_ => Some(&n.x),
					},
				))?;
			}

			Expr::Intrinsic { kind, mode, span } => {
				let (kind, mode) = self.check_intrinsic(*kind, *mode, ctx, *span)?;

				// Generate IR
				ctx.ops.push(Op::Intrinsic(kind, mode))
			}
			Expr::Symbol { access, span } => self.check_symbol(access, symbols, ctx, *span)?,
			Expr::PtrTo { access, span } => self.check_ptr_to(access, symbols, ctx, *span)?,

			Expr::Block {
				label, body, span, ..
			} => {
				let mut bblock = Block::new(ctx, block, false);
				{
					let name = label.x.clone();
					let unique_name = ctx.define_label(name, bblock.index, symbols, label.span)?;

					self.check_nodes(body, symbols, ctx, &mut bblock)?;
					ctx.ops.push(Op::Label(unique_name));
				}
				bblock.end(ctx, block, *span)?;
				ctx.undefine_label(&label.x);
			}

			Expr::Jump { label, span } => {
				let Some(block_label) = ctx.labels.get(&label.x) else {
					return Err(Error::UnknownLabel(label.span));
				};
				let label_name = block_label.unique_name;

				self.jump_to_block(ctx, block, block_label.block_idx, *span);
				ctx.ops.push(Op::Jump(label_name));
			}
			Expr::Return { span } => {
				self.jump_to_block(ctx, block, 0, *span);
				ctx.ops.push(Op::Return);
			}
			Expr::If {
				if_body,
				if_span,
				elif_blocks,
				else_block,
				..
			} => {
				self.consume_condition(ctx, *if_span)?;

				// TODO!: refactor this code, this is kinda mess

				if let Some(ast_else_block) = else_block
					&& !elif_blocks.is_empty()
				{
					// `if {} elif {} else {}`
					let if_begin_label = symbols.new_unique_name();
					let else_begin_label = symbols.new_unique_name();
					let end_label = symbols.new_unique_name();
					let mut next_label = symbols.new_unique_name();

					ctx.ops.push(Op::JumpIf(if_begin_label));
					ctx.ops.push(Op::Jump(next_label));

					let stacks_before = ctx.take_snapshot();

					let mut if_block = Block::new(ctx, block, true);
					{
						ctx.ops.push(Op::Label(if_begin_label));
						self.check_nodes(if_body, symbols, ctx, &mut if_block)?;
						ctx.ops.push(Op::Jump(end_label));
					}

					let stacks_to_expect = ctx.take_snapshot();

					if_block.finish(ctx);

					for (i, elif) in elif_blocks.iter().enumerate() {
						ctx.ops.push(Op::Label(next_label));

						self.check_condition(&elif.condition, symbols, ctx, block, elif.span)?;

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
						let mut elif_block = Block::new_with(block, true, stacks_to_expect.clone());
						{
							self.check_nodes(&elif.body, symbols, ctx, &mut elif_block)?;
						}
						elif_block.end(ctx, block, elif.span)?;

						ctx.apply_snapshot(stacks_before.clone());

						ctx.ops.push(Op::Jump(end_label));
					}

					let mut else_block = Block::new_with(block, true, stacks_to_expect.clone());
					{
						ctx.ops.push(Op::Label(else_begin_label));
						self.check_nodes(&ast_else_block.body, symbols, ctx, &mut else_block)?;
					}
					else_block.end(ctx, block, ast_else_block.span)?;

					ctx.ops.push(Op::Label(end_label));
				} else if !elif_blocks.is_empty() {
					// `if {} elif {}`
					let if_begin_label = symbols.new_unique_name();
					let end_label = symbols.new_unique_name();
					let mut next_label = symbols.new_unique_name();

					ctx.ops.push(Op::JumpIf(if_begin_label));
					ctx.ops.push(Op::Jump(next_label));

					let mut if_block = Block::new(ctx, block, true);
					{
						ctx.ops.push(Op::Label(if_begin_label));
						self.check_nodes(if_body, symbols, ctx, &mut if_block)?;
						ctx.ops.push(Op::Jump(end_label));
					}
					if_block.end(ctx, block, *if_span)?;

					for (i, elif) in elif_blocks.iter().enumerate() {
						ctx.ops.push(Op::Label(next_label));

						self.check_condition(&elif.condition, symbols, ctx, block, elif.span)?;

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
						let mut elif_block = Block::new(ctx, block, true);
						{
							self.check_nodes(&elif.body, symbols, ctx, &mut elif_block)?;
						}
						elif_block.end(ctx, block, elif.span)?;

						ctx.ops.push(Op::Jump(end_label));
					}

					ctx.ops.push(Op::Label(end_label));
				} else if let Some(ast_else_block) = else_block {
					// `if {} else {}`
					// Code below may be a bit confusing

					let if_begin_label = symbols.new_unique_name();
					let end_label = symbols.new_unique_name();

					let mut else_block = Block::new(ctx, block, true);
					{
						ctx.ops.push(Op::JumpIf(if_begin_label));

						// `else` block
						self.check_nodes(&ast_else_block.body, symbols, ctx, &mut else_block)?;
						ctx.ops.push(Op::Jump(end_label));
					}

					let mut if_block = match else_block.state {
						BlockState::Finished => Block::new(ctx, block, false),
						_ => {
							let block = Block::new(ctx, block, true);
							ctx.apply_snapshot(else_block.snapshot.clone());
							block
						}
					};
					{
						// `if` block
						ctx.ops.push(Op::Label(if_begin_label));
						self.check_nodes(if_body, symbols, ctx, &mut if_block)?;
						ctx.ops.push(Op::Label(end_label));
					}
					if_block.end(ctx, block, *if_span)?;
				} else {
					// `if {}`
					let if_begin_label = symbols.new_unique_name();
					let end_label = symbols.new_unique_name();

					let mut if_block = Block::new(ctx, block, true);
					{
						ctx.ops.push(Op::JumpIf(if_begin_label));
						ctx.ops.push(Op::Jump(end_label));
						ctx.ops.push(Op::Label(if_begin_label));

						self.check_nodes(if_body, symbols, ctx, &mut if_block)?;

						ctx.ops.push(Op::Label(end_label));
					}
					if_block.end(ctx, block, *if_span)?;
				}
			}
			Expr::While {
				condition,
				body,
				span,
			} => {
				self.check_while(condition, body, symbols, ctx, block, *span)?;
			}
		}

		Ok(())
	}

	fn check_symbol(
		&mut self,
		access: &SymbolAccess,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let resolved = symbols.resolve_access(access, span)?;

		match resolved {
			ResolvedAccess::Type(_) | ResolvedAccess::Struct(_) => {
				return Err(Error::InvalidSymbol {
					error: SymbolError::IllegalUse {
						found: resolved.kind(),
					},
					defined_at: resolved.defined_at(),
					span,
				});
			}

			ResolvedAccess::Var {
				var,
				field_type,
				field_offset,
				indexing_type,
			} => {
				let typ = field_type.x.primitive(span)?;
				let stride = match &indexing_type {
					Some(t) => t.x.size(t.span)?,
					None => 0,
				};

				// Type check
				if indexing_type.is_some() {
					self.consume_index(ctx, var.in_rom, span)?;
				}
				ctx.ws.push(StackItem::new(typ.clone(), span));

				// Generate IR
				let name = var.unique_name;
				let short = var.in_rom;
				ctx.ops.push_addr(name, field_offset, short, stride);

				let intr = if var.in_rom {
					Intrinsic::Load(AddrMode::AbsShort)
				} else {
					Intrinsic::Load(AddrMode::AbsByte)
				};
				let mode = IntrMode::from_type(typ);
				ctx.ops.push(intr.op_mode(mode));
			}

			ResolvedAccess::Enum { enm, variant } => {
				// Type check
				ctx.ws.push(StackItem::new(enum_type(enm), span));

				// Generate IR
				ctx.ops.push(Op::ConstUse(variant.unique_name));
			}

			ResolvedAccess::Func(func) => match &func.signature {
				FuncSignature::Vector => {
					return Err(Error::InvalidSymbol {
						error: SymbolError::IllegalVectorCall,
						defined_at: func.defined_at,
						span,
					});
				}
				FuncSignature::Proc { inputs, outputs } => {
					// Check function inputs
					ctx.ws
						.consumer(span)
						.compare(inputs.iter().map(|t| &t.typ.x), StackMatch::Tail)?;

					// Push function outputs
					for output in outputs.iter() {
						ctx.ws.push(StackItem::new(output.typ.x.clone(), span));
					}

					// Generate IR
					ctx.ops.push(Op::FuncCall(func.unique_name));
				}
			},

			ResolvedAccess::Const(cnst) => {
				// Type check
				ctx.ws.push(StackItem::new(cnst.typ.clone(), span));

				// Generate IR
				ctx.ops.push(Op::ConstUse(cnst.unique_name));
			}
			ResolvedAccess::Data(data) => {
				// Type check
				ctx.ws.push(StackItem::new(Type::Byte, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddr {
					name: data.unique_name,
					offset: 0,
				});
				ctx.ops.push(Intrinsic::Load(AddrMode::AbsShort).op());
			}
		};

		Ok(())
	}

	fn check_ptr_to(
		&mut self,
		access: &Spanned<SymbolAccess>,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let resovled = symbols.resolve_access(&access.x, access.span)?;

		match resovled {
			ResolvedAccess::Const(_)
			| ResolvedAccess::Type(_)
			| ResolvedAccess::Enum { .. }
			| ResolvedAccess::Struct(_) => {
				return Err(Error::InvalidSymbol {
					error: SymbolError::IllegalPtr {
						found: resovled.kind(),
					},
					defined_at: resovled.defined_at(),
					span: access.span,
				});
			}

			ResolvedAccess::Var {
				var,
				field_type,
				field_offset,
				indexing_type,
			} => {
				let typ = match var.in_rom {
					true => Type::ShortPtr(field_type.x.clone().into()),
					false => Type::BytePtr(field_type.x.clone().into()),
				};
				let stride = match &indexing_type {
					Some(t) => t.x.size(t.span)?,
					None => 0,
				};

				// Type check
				if indexing_type.is_some() {
					self.consume_index(ctx, var.in_rom, span)?;
				}

				ctx.ws.push(StackItem::new(typ, span));

				// Generate IR
				let name = var.unique_name;
				let short = var.in_rom;
				ctx.ops.push_addr(name, field_offset, short, stride);
			}

			ResolvedAccess::Func(func) => {
				// Type check
				let typ = Type::FuncPtr(func.signature.clone());
				ctx.ws.push(StackItem::new(typ, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddr {
					name: func.unique_name,
					offset: 0,
				});
			}
			ResolvedAccess::Data(data) => {
				// Type check
				let typ = Type::short_ptr(Type::Byte);
				ctx.ws.push(StackItem::new(typ, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddr {
					name: data.unique_name,
					offset: 0,
				});
			}
		};

		Ok(())
	}

	fn check_store(
		&mut self,
		access: &Spanned<SymbolAccess>,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let symbol_span = access.x.symbol().span;
		let resolved = symbols.resolve_access(&access.x, access.span)?;

		match resolved {
			ResolvedAccess::Func(_)
			| ResolvedAccess::Const(_)
			| ResolvedAccess::Type(_)
			| ResolvedAccess::Enum { .. }
			| ResolvedAccess::Struct(_) => {
				return Err(Error::InvalidSymbol {
					error: SymbolError::IllegalStore {
						found: resolved.kind(),
					},
					defined_at: resolved.defined_at(),
					span: access.span,
				});
			}

			ResolvedAccess::Var {
				var,
				field_type,
				field_offset,
				indexing_type,
			} => {
				// Type check
				let expect = field_type.x.primitive(symbol_span)?;

				if indexing_type.is_some() {
					self.consume_index(ctx, var.in_rom, span)?;
				}

				let mut consumer = ctx.ws.consumer(span);
				match consumer.pop() {
					Some(value) if value.typ == *expect => (/* ok */),
					_ => {
						return Err(Error::InvalidStack {
							expected: ExpectedStack::Store(expect.clone()),
							found: consumer.found(),
							error: consumer.stack_error(),
							span,
						});
					}
				}

				// Generate IR
				let stride = match &indexing_type {
					Some(t) => t.x.size(t.span)?,
					None => 0,
				};

				let name = var.unique_name;
				let short = var.in_rom;
				ctx.ops.push_addr(name, field_offset, short, stride);

				let intr = if var.in_rom {
					Intrinsic::Store(AddrMode::AbsShort)
				} else {
					Intrinsic::Store(AddrMode::AbsByte)
				};
				let mode = IntrMode::from_type(expect);
				ctx.ops.push(intr.op_mode(mode));
			}

			ResolvedAccess::Data(data) => {
				ctx.ops.push(Op::AbsShortAddr {
					name: data.unique_name,
					offset: 0,
				});
				ctx.ops.push(Intrinsic::Store(AddrMode::AbsShort).op());

				let mut consumer = ctx.ws.consumer(span);
				match consumer.pop() {
					Some(value) if value.typ == Type::Byte => (/* ok */),
					_ => {
						return Err(Error::InvalidStack {
							expected: ExpectedStack::Store(Type::Byte),
							found: consumer.found(),
							error: consumer.stack_error(),
							span,
						});
					}
				}
			}
		}

		Ok(())
	}

	// TODO: casting should also probaly work with the return stack?
	// Currently i don't know how to syntactically mark casting for return stack.
	fn check_cast(
		&mut self,
		types: &[NamedType<UnsizedType>],
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
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

		let bytes_to_pop: u16 = items.iter().fold(0, |acc, t| acc + t.typ.size());
		let stack_size: u16 = ctx.ws.items.iter().fold(0, |acc, t| acc + t.typ.size());

		let mut left_to_pop: u16 = bytes_to_pop;
		let mut found_size: u16 = 0;

		while left_to_pop > 0 {
			let Some(item) = ctx.ws.pop(span) else {
				return Err(Error::InvalidCasting {
					error: CastError::Underflow,
					expected: bytes_to_pop,
					found: stack_size,
					span,
				});
			};

			let size = item.typ.size();
			found_size += size;
			if size > left_to_pop {
				return Err(Error::InvalidCasting {
					error: CastError::UnhandledBytes {
						size,
						left: size - left_to_pop,
						at: item.pushed_at,
					},
					expected: bytes_to_pop,
					found: found_size,
					span,
				});
			} else {
				left_to_pop -= size;
			}
		}

		for item in items {
			ctx.ws.push(item);
		}

		Ok(())
	}

	fn check_while(
		&mut self,
		condition: &Spanned<Vec<Node>>,
		body: &[Node],
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		block: &mut Block,
		span: Span,
	) -> error::Result<()> {
		let again_label = symbols.new_unique_name();
		let continue_label = symbols.new_unique_name();
		let end_label = symbols.new_unique_name();

		ctx.ops.push(Op::Label(again_label));

		self.check_condition(condition, symbols, ctx, block, span)?;

		ctx.ops.push(Op::JumpIf(continue_label));
		ctx.ops.push(Op::Jump(end_label));
		ctx.ops.push(Op::Label(continue_label));

		let mut while_block = Block::new(ctx, block, true);
		{
			// Body
			self.check_nodes(body, symbols, ctx, &mut while_block)?;

			ctx.ops.push(Op::Jump(again_label));
			ctx.ops.push(Op::Label(end_label));
		}
		while_block.end(ctx, block, span)?;

		Ok(())
	}

	fn check_condition(
		&mut self,
		condition: &Spanned<Vec<Node>>,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		block: &mut Block,
		span: Span,
	) -> error::Result<()> {
		let mut cond_block = Block::new(ctx, block, true);
		{
			self.check_nodes(&condition.x, symbols, ctx, &mut cond_block)?;
			self.consume_condition(ctx, span)?;
		}
		cond_block.end(ctx, block, span)?;
		Ok(())
	}

	fn consume_condition(&mut self, ctx: &mut Context, span: Span) -> error::Result<()> {
		let mut consumer = ctx.ws.consumer(span);
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
	fn consume_index(&mut self, ctx: &mut Context, short: bool, span: Span) -> error::Result<()> {
		let typ = if short { Type::Short } else { Type::Byte };

		let mut consumer = ctx.ws.consumer(span);
		match consumer.pop() {
			Some(value) if value.typ == typ => Ok(()),
			_ => Err(Error::InvalidStack {
				expected: ExpectedStack::Index(typ),
				found: consumer.found(),
				error: consumer.stack_error(),
				span,
			}),
		}
	}

	pub fn check_def(&mut self, def: &Def, symbols: &mut SymbolsTable) -> error::Result<()> {
		macro_rules! s {
			($symbol:expr, $span:expr) => {
				$symbol
					.as_ref()
					.unwrap_or_else(|| bug!("unexpected `None` symbol {}", $span))
			};
		}

		match def {
			Def::Type(_) => (/* do nothing */),
			Def::Struct(_) => (/* do nothing */),

			Def::Func(def) => {
				let symbol = s!(def.symbol, def.span);
				let mut ctx = Context::default();

				match &symbol.signature {
					FuncSignature::Vector => (),
					FuncSignature::Proc { inputs, .. } => {
						// Push function inputs onto the stack
						for input in inputs.iter() {
							let item = StackItem::named(
								input.typ.x.clone(),
								input.name.clone().map(|n| n.x),
								input.typ.span,
							);
							ctx.ws.push(item);
						}
					}
				}

				// Check function body
				let mut block = Block::new_root(&ctx);
				{
					self.check_nodes(&def.body, symbols, &mut ctx, &mut block)?;
				}

				match &symbol.signature {
					FuncSignature::Vector => {
						ctx.compare_def_stacks(empty_stack(), def.name.span)?;
					}
					FuncSignature::Proc { outputs, .. } => {
						let ws = outputs.iter().map(|t| &t.typ.x);
						ctx.compare_def_stacks(ws, def.name.span)?;
					}
				}
				ctx.rs
					.consumer_keep(def.name.span)
					.compare(std::iter::empty::<&Type>(), StackMatch::Exact)?;

				// Generate IR
				let func = Function {
					is_vector: matches!(def.signature.x, FuncSignature::Vector),
					body: ctx.ops,
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
				let size = symbol.typ.x.size(symbol.typ.span)?;
				let var = Variable {
					size,
					in_rom: symbol.in_rom,
				};
				self.program.vars.insert(symbol.unique_name, var);
			}

			Def::Const(def) => {
				let symbol = s!(def.symbol, def.span);

				// Type check
				let mut ctx = Context::default();
				let mut block = Block::new_root(&ctx);
				{
					self.check_nodes(&def.body, symbols, &mut ctx, &mut block)?;
				}

				ctx.compare_def_stacks(iter::once(&symbol.typ), def.name.span)?;

				// Generate IR
				let cnst = Constant { body: ctx.ops };
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

				let typ = enum_type(symbol);
				let mut prev_vari_name: Option<UniqueName> = None;
				let is_short = symbol.inherits.size() == 2;

				for vari in def.variants.iter() {
					let Some(vari_symbol) = symbol.variants.get(&vari.name.x) else {
						bug!(
							"unexpected non-existing enum variant symbol at {}",
							vari.name.span
						);
					};
					let unique_name = vari_symbol.unique_name;

					let ops: Ops;
					if let Some(body) = &vari.body {
						// Type check variant body
						let mut ctx = Context::default();
						let mut block = Block::new_root(&ctx);
						{
							self.check_nodes(body, symbols, &mut ctx, &mut block)?;
						}
						ctx.compare_def_stacks(iter::once(&typ), vari.name.span)?;
						ops = ctx.ops;
					} else {
						ops = match prev_vari_name {
							Some(prev) if is_short => Ops::new(vec![
								Op::ConstUse(prev),
								Op::Short(1),
								Op::Intrinsic(Intrinsic::Add, IntrMode::SHORT),
							]),
							None if is_short => Ops::new(vec![Op::Short(0)]),

							Some(prev) => Ops::new(vec![
								Op::ConstUse(prev),
								Op::Byte(1),
								Op::Intrinsic(Intrinsic::Add, IntrMode::NONE),
							]),
							None => Ops::new(vec![Op::Byte(0)]),
						};
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
		mut intr: Intrinsic,
		mut mode: IntrMode,
		ctx: &mut Context,
		intr_span: Span,
	) -> error::Result<(Intrinsic, IntrMode)> {
		let keep = mode.contains(IntrMode::KEEP);

		let (primary_stack, secondary_stack) = if mode.contains(IntrMode::RETURN) {
			(&mut ctx.rs, &mut ctx.ws)
		} else {
			(&mut ctx.ws, &mut ctx.rs)
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
				mode |= self.check_arithmetic_intr(mode, ctx, intr_span)?;
				Ok((intr, mode))
			}

			// ( a -- a+1 )
			Intrinsic::Inc => match consumer.pop() {
				Some(a) => {
					mode |= IntrMode::from_type(&a.typ);
					primary_stack.push(a);
					Ok((intr, mode))
				}

				_ => err_invalid_stack!(ExpectedStack::IntrInc),
			},

			// ( a shift8 -- c )
			Intrinsic::Shift => match (consumer.pop(), consumer.pop()) {
				(Some(shift8), Some(a)) if shift8.typ == Type::Byte => {
					mode |= IntrMode::from_type(&a.typ);
					primary_stack.push(StackItem::new(a.typ, intr_span));
					Ok((intr, mode))
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

				mode |= IntrMode::from_type(&output);

				primary_stack.push(StackItem::new(output, intr_span));
				Ok((intr, mode))
			}

			// ( a b -- bool8 )
			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				let (Some(b), Some(a)) = (consumer.pop(), consumer.pop()) else {
					return err_invalid_stack!(ExpectedStack::Comparison);
				};

				mode |= IntrMode::from_type(&a.typ);

				if !a.typ.same_as(&b.typ) {
					return Err(Error::UnmatchedInputsTypes {
						found: consumer.found(),
						span: intr_span,
					});
				}

				primary_stack.push(StackItem::new(Type::Byte, intr_span));
				Ok((intr, mode))
			}

			// ( a -- )
			Intrinsic::Pop => {
				let Some(a) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::Manipulation(1));
				};

				mode |= IntrMode::from_type(&a.typ);
				Ok((intr, mode))
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
				mode |= IntrMode::from_type(&a.typ);
				primary_stack.push(b);
				primary_stack.push(a);
				Ok((intr, mode))
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
				mode |= IntrMode::from_type(&a.typ);
				primary_stack.push(b);
				Ok((intr, mode))
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
				mode |= IntrMode::from_type(&a.typ);
				primary_stack.push(b);
				primary_stack.push(c);
				primary_stack.push(a);
				Ok((intr, mode))
			}

			// ( a -- a a )
			Intrinsic::Dup => {
				let Some(a) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::Manipulation(1));
				};

				mode |= IntrMode::from_type(&a.typ);
				primary_stack.push(a.clone());
				primary_stack.push(StackItem::named(a.typ, a.name.clone(), intr_span));
				Ok((intr, mode))
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
				mode |= IntrMode::from_type(&a.typ);
				primary_stack.push(a.clone());
				primary_stack.push(b);
				primary_stack.push(StackItem::named(a.typ, a.name, intr_span));
				Ok((intr, mode))
			}

			// ( a -- | a )
			Intrinsic::Sth => {
				let Some(a) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::Manipulation(1));
				};

				mode |= IntrMode::from_type(&a.typ);
				secondary_stack.push(a);
				Ok((intr, mode))
			}

			// ( addr -- value )
			Intrinsic::Load(AddrMode::Unknown) => {
				let Some(addr) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::IntrLoad);
				};

				let output = match addr.typ {
					Type::BytePtr(t) => {
						intr = Intrinsic::Load(AddrMode::AbsByte);
						t.primitive(intr_span)?.clone()
					}
					Type::ShortPtr(t) => {
						intr = Intrinsic::Load(AddrMode::AbsShort);
						t.primitive(intr_span)?.clone()
					}
					_ => return err_invalid_stack!(ExpectedStack::IntrLoad),
				};

				mode |= IntrMode::from_type(&output);

				primary_stack.push(StackItem::new(output, intr_span));
				Ok((intr, mode))
			}
			Intrinsic::Load(addr) => {
				bug!("address mode of `load` intrinsic cannot be `{addr:?}` at typecheck stage")
			}

			// ( value addr -- )
			Intrinsic::Store(AddrMode::Unknown) => {
				let Some(addr) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::IntrStoreEmpty);
				};
				let Some(value) = consumer.pop() else {
					return err_invalid_stack!(ExpectedStack::IntrStore(addr.typ));
				};

				match addr.typ {
					Type::BytePtr(t) if *t.primitive(intr_span)? == value.typ => {
						intr = Intrinsic::Store(AddrMode::AbsByte);
					}
					Type::ShortPtr(t) if *t.primitive(intr_span)? == value.typ => {
						intr = Intrinsic::Store(AddrMode::AbsShort);
					}
					Type::BytePtr(_) | Type::ShortPtr(_) => {
						return err_invalid_stack!(ExpectedStack::IntrStore(addr.typ));
					}
					_ => return err_invalid_stack!(ExpectedStack::IntrStoreEmpty),
				}

				mode |= IntrMode::from_type(&value.typ);
				Ok((intr, mode))
			}
			Intrinsic::Store(addr) => {
				bug!("address mode of `store` intrinsic cannot be `{addr:?}` at typecheck stage")
			}

			// ( device8 -- value )
			Intrinsic::Input | Intrinsic::Input2 => match consumer.pop() {
				Some(device8) if device8.typ == Type::Byte => {
					if intr == Intrinsic::Input2 {
						primary_stack.push(StackItem::new(Type::Short, intr_span));
						Ok((intr, mode | IntrMode::SHORT))
					} else {
						primary_stack.push(StackItem::new(Type::Byte, intr_span));
						Ok((intr, mode))
					}
				}

				_ => err_invalid_stack!(ExpectedStack::IntrInput),
			},

			// ( value device8 -- )
			Intrinsic::Output => match (consumer.pop(), consumer.pop()) {
				(Some(device8), Some(value)) if device8.typ == Type::Byte => {
					mode |= IntrMode::from_type(&value.typ);
					Ok((intr, mode))
				}

				_ => err_invalid_stack!(ExpectedStack::IntrOutput),
			},
		}
	}
	#[must_use]
	fn check_arithmetic_intr(
		&mut self,
		mut mode: IntrMode,
		ctx: &mut Context,
		intr_span: Span,
	) -> error::Result<IntrMode> {
		let primary_stack = if mode.contains(IntrMode::RETURN) {
			&mut ctx.rs
		} else {
			&mut ctx.ws
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
		mode |= IntrMode::from_type(&output);

		primary_stack.push(StackItem::new(output, intr_span));

		Ok(mode)
	}

	// ==============================
	// Helper functions
	// ==============================

	fn jump_to_block(
		&mut self,
		ctx: &mut Context,
		block: &mut Block,
		target_idx: usize,
		span: Span,
	) {
		let state = match block.state {
			BlockState::Branching => BlockState::Branching,
			_ => BlockState::Finished,
		};

		block.propagate(state, target_idx, span);
		block.finish(ctx);
	}
}
