mod consumer;
mod context;
mod stack;

use std::{collections::HashMap, rc::Rc};

pub use consumer::*;
pub use context::*;
pub use stack::*;

use crate::{
	ast::{Ast, Def, Expr, Node},
	bug,
	error::{self, CastError, Error, ExpectedStack, SymbolError},
	lexer::{Span, Spanned},
	problems::Problems,
	program::{AddrMode, Constant, Data, Function, IntrMode, Intrinsic, Op, Program, Variable},
	symbols::{
		ConstSymbol, ConstSymbolKind, DataSymbol, EnumSymbolVariant, FuncSignature, FuncSymbol,
		Name, NamedType, StructSymbolField, Symbol, SymbolAccess, SymbolKind, SymbolsTable, Type,
		TypeSymbol, UniqueName, UnsizedType, VarSymbol,
	},
	warn::Warn,
};

fn intr_mode_from_size(size: u16) -> Option<IntrMode> {
	match size {
		0 | 1 => Some(IntrMode::NONE),
		2 => Some(IntrMode::SHORT),
		3.. => None,
	}
}
fn intr_mode_from_type(typ: &Type) -> Option<IntrMode> {
	intr_mode_from_size(typ.size())
}

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
					let enum_typ = match def.untyped {
						true => inherits.clone(),
						false => Type::Custom {
							name: def.name.x.clone(),
							size: inherits.size(),
						},
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

				Def::Struct(def) => {
					let mut struct_size: u16 = 0;

					// Collect struct fields
					let mut fields = HashMap::default();
					for field in def.fields.iter() {
						let typ = field.typ.x.clone().into_sized(symbols, field.span)?;

						let struct_field = StructSymbolField {
							typ,
							offset: struct_size,
						};
						struct_size += struct_field.typ.size();
						fields.insert(field.name.x.clone(), struct_field);
					}

					// Define struct type
					let struct_typ = Type::Custom {
						name: def.name.x.clone(),
						size: struct_size,
					};
					let symbol = Rc::new(TypeSymbol::Struct {
						typ: struct_typ,
						fields,
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
				let item = StackItem::new(Type::ShortPtr(Type::Byte.into()), *span);
				ctx.ws.push(item);

				// Generate IR
				// Insert an unique data for each string literal even if strings contents are the same
				let unique_name = symbols.new_unique_name();
				let body = string.as_bytes().into();
				self.program.datas.insert(unique_name, Data { body });

				ctx.ops.push(Op::AbsShortAddrOf {
					name: unique_name,
					offset: 0,
				});
			}
			Expr::Padding { .. } => {
				todo!("`Expr::Padding` outside 'data' blocks should error before typecheck stage");
			}

			Expr::Store {
				symbol,
				access,
				span,
			} => self.check_store(symbol, access, symbols, ctx, *span)?,

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
			Expr::Symbol { name, access, span } => {
				self.check_symbol(name, access, symbols, ctx, *span)?
			}
			Expr::PtrTo { name, access, span } => {
				self.check_ptr_to(name, access, symbols, ctx, *span)?
			}

			Expr::Block {
				label, body, span, ..
			} => {
				let mut bblock = Block::new(ctx, block, false);
				{
					let name = label.x.clone();
					let unique_name =
						self.define_label(symbols, ctx, name, bblock.index, label.span)?;

					self.check_nodes(body, symbols, ctx, &mut bblock)?;
					ctx.ops.push(Op::Label(unique_name));
				}
				bblock.end(ctx, block, *span)?;
				self.undefine_label(ctx, &label.x);
			}

			Expr::Jump { label, span } => {
				let Some(block_label) = ctx.labels.get(&label.x).cloned() else {
					return Err(Error::UnknownLabel(label.span));
				};

				self.jump_to_block(ctx, block, block_label.block_idx, *span);
				ctx.ops.push(Op::Jump(block_label.unique_name));
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
		name: &Name,
		access: &SymbolAccess,
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
					if *access != SymbolAccess::Single {
						todo!("'functions are not structs' error");
					};

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

			Symbol::Var(var) => {
				// Type check
				let (typ, offset) = symbols.struct_field_or_single(&var.typ, access, span)?;
				ctx.ws.push(StackItem::new(typ.clone(), span));

				// Generate IR
				let mode = intr_mode_from_type(typ).ok_or_else(|| Error::CantLoadSymbol {
					size: Spanned::new(typ.size(), span),
					defined_at: var.defined_at,
					span,
				})?;
				let intr = Intrinsic::Load(AddrMode::AbsByte);
				ctx.ops.push(Op::AbsByteAddrOf {
					name: var.unique_name,
					offset,
				});
				ctx.ops.push(Op::Intrinsic(intr, mode));
			}
			Symbol::Const(cnst) => {
				if *access != SymbolAccess::Single {
					todo!("'constants are not structs' error");
				};

				// Type check
				ctx.ws.push(StackItem::new(cnst.typ.clone(), span));

				// Generate IR
				ctx.ops.push(Op::ConstUse(cnst.unique_name));
			}
			Symbol::Data(data) => {
				if *access != SymbolAccess::Single {
					todo!("'data blocks are not structs' error");
				};

				// Type check
				ctx.ws.push(StackItem::new(Type::Byte, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddrOf {
					name: data.unique_name,
					offset: 0,
				});
				ctx.ops.push(Op::Intrinsic(
					Intrinsic::Load(AddrMode::AbsShort),
					IntrMode::NONE,
				));
			}
		};

		Ok(())
	}

	fn check_ptr_to(
		&mut self,
		name: &Spanned<Name>,
		access: &SymbolAccess,
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
				if *access != SymbolAccess::Single {
					todo!("'functions are not structs' error");
				};

				// Type check
				let typ = Type::FuncPtr(func.signature.clone());
				ctx.ws.push(StackItem::new(typ, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddrOf {
					name: func.unique_name,
					offset: 0,
				});
			}
			Symbol::Var(var) => {
				// Type check
				let (typ, offset) = symbols.struct_field_or_single(&var.typ, access, span)?;

				let t = Type::BytePtr(typ.clone().into());
				ctx.ws.push(StackItem::new(t, span));

				// Generate IR
				ctx.ops.push(Op::AbsByteAddrOf {
					name: var.unique_name,
					offset,
				});
			}
			Symbol::Data(data) => {
				if *access != SymbolAccess::Single {
					todo!("'data blocks are not structs' error");
				};

				// Type check
				let typ = Type::ShortPtr(Type::Byte.into());
				ctx.ws.push(StackItem::new(typ, span));

				// Generate IR
				ctx.ops.push(Op::AbsShortAddrOf {
					name: data.unique_name,
					offset: 0,
				});
			}
		};

		Ok(())
	}

	fn check_store(
		&mut self,
		name: &Spanned<Name>,
		access: &SymbolAccess,
		symbols: &mut SymbolsTable,
		ctx: &mut Context,
		span: Span,
	) -> error::Result<()> {
		let Some(symbol) = symbols.table.get(&name.x) else {
			return Err(Error::UnknownSymbol(span));
		};

		let intr: Intrinsic;

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
				let (typ, offset) = symbols.struct_field_or_single(&var.typ, access, span)?;

				intr = Intrinsic::Store(AddrMode::AbsByte);
				ctx.ops.push(Op::AbsByteAddrOf {
					name: var.unique_name,
					offset,
				});

				typ
			}
			Symbol::Data(data) => {
				intr = Intrinsic::Store(AddrMode::AbsShort);
				ctx.ops.push(Op::AbsShortAddrOf {
					name: data.unique_name,
					offset: 0,
				});

				match access {
					SymbolAccess::Single => &Type::Byte,
					SymbolAccess::Fields(_) => todo!("'data blocks are not structs' error"),
				}
			}
		};

		let mut consumer = ctx.ws.consumer(span);
		match consumer.pop() {
			Some(value) if value.typ == *expect_typ => {
				let mode =
					intr_mode_from_type(&value.typ).ok_or_else(|| Error::CantStoreSymbol {
						size: Spanned::new(value.typ.size(), span),
						defined_at: symbol.defined_at(),
						span,
					})?;
				ctx.ops.push(Op::Intrinsic(intr, mode));
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
				let mut ctx = Context::new();

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
						ctx.ws
							.consumer_keep(def.name.span)
							.compare(std::iter::empty::<&Type>(), StackMatch::Exact)?;
					}
					FuncSignature::Proc { outputs, .. } => {
						ctx.ws
							.consumer_keep(def.name.span)
							.compare(outputs.iter().map(|t| &t.typ.x), StackMatch::Exact)?;
					}
				}
				ctx.rs
					.consumer_keep(def.name.span)
					.compare(std::iter::empty::<&Type>(), StackMatch::Exact)?;

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
				let mut ctx = Context::new();
				let mut block = Block::new_root(&ctx);
				{
					self.check_nodes(&def.body, symbols, &mut ctx, &mut block)?;
				}

				ctx.ws
					.consumer_keep(def.name.span)
					.compare(std::iter::once(&symbol.typ), StackMatch::Exact)?;
				ctx.rs
					.consumer_keep(def.name.span)
					.compare(std::iter::empty::<&Type>(), StackMatch::Exact)?;

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
				let is_short = symbol.typ().size() == 2;

				for vari in def.variants.iter() {
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
						let mut ctx = Context::new();
						let mut block = Block::new_root(&ctx);
						{
							self.check_nodes(body, symbols, &mut ctx, &mut block)?;
						}
						ctx.ws
							.consumer_keep(def.name.span)
							.compare(std::iter::once(&typ), StackMatch::Exact)?;
						ctx.rs
							.consumer_keep(def.name.span)
							.compare(std::iter::empty::<&Type>(), StackMatch::Exact)?;
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
		macro_rules! mode_from_type {
			($typ:expr) => {
				match intr_mode_from_type(&$typ) {
					Some(mode) => mode,
					None => {
						return Err(Error::CantUseSymbol {
							size: Spanned::new($typ.size(), intr_span),
							defined_at: Span::default(),
							span: intr_span,
						})
					}
				}
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
					mode |= mode_from_type!(a.typ);
					primary_stack.push(a);
					Ok((intr, mode))
				}

				_ => err_invalid_stack!(ExpectedStack::IntrInc),
			},

			// ( a shift8 -- c )
			Intrinsic::Shift => match (consumer.pop(), consumer.pop()) {
				(Some(shift8), Some(a)) if shift8.typ == Type::Byte => {
					mode |= mode_from_type!(a.typ);
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

				mode |= mode_from_type!(output);

				primary_stack.push(StackItem::new(output, intr_span));
				Ok((intr, mode))
			}

			// ( a b -- bool8 )
			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				let (Some(b), Some(a)) = (consumer.pop(), consumer.pop()) else {
					return err_invalid_stack!(ExpectedStack::Comparison);
				};

				mode |= mode_from_type!(a.typ);

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

				mode |= mode_from_type!(a.typ);
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
				mode |= mode_from_type!(a.typ);
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
				mode |= mode_from_type!(a.typ);
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
				mode |= mode_from_type!(a.typ);
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

				mode |= mode_from_type!(a.typ);
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
				mode |= mode_from_type!(a.typ);
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

				mode |= mode_from_type!(a.typ);
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
						*t
					}
					Type::ShortPtr(t) => {
						intr = Intrinsic::Load(AddrMode::AbsShort);
						*t
					}
					_ => return err_invalid_stack!(ExpectedStack::IntrLoad),
				};

				mode |= mode_from_type!(output);

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
					Type::BytePtr(t) if *t == value.typ => {
						intr = Intrinsic::Store(AddrMode::AbsByte);
					}
					Type::ShortPtr(t) if *t == value.typ => {
						intr = Intrinsic::Store(AddrMode::AbsShort);
					}
					Type::BytePtr(_) | Type::ShortPtr(_) => {
						return err_invalid_stack!(ExpectedStack::IntrStore(addr.typ));
					}
					_ => return err_invalid_stack!(ExpectedStack::IntrStoreEmpty),
				}

				mode |= mode_from_type!(value.typ);
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
					mode |= mode_from_type!(value.typ);
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
		mode |= intr_mode_from_type(&output).ok_or_else(|| Error::CantUseSymbol {
			size: Spanned::new(output.size(), intr_span),
			defined_at: Span::default(),
			span: intr_span,
		})?;

		primary_stack.push(StackItem::new(output, intr_span));

		Ok(mode)
	}

	// ==============================
	// Helper functions
	// ==============================

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
		cur_block: &mut Block,
		target_idx: usize,
		span: Span,
	) {
		let state = match cur_block.state {
			BlockState::Branching => BlockState::Branching,
			_ => BlockState::Finished,
		};

		cur_block.propagate_till(state, target_idx, span);
		cur_block.finish(ctx);
	}
}
