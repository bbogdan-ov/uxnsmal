mod scope;
mod stack;

pub use scope::*;
pub use stack::*;

use std::{
	collections::HashMap,
	fs,
	io::{self, Read},
	path::Path,
	rc::Rc,
};

use crate::{
	ast::{Ast, Body, Def, ElifBlock, Expr, IfBlock, Node, Pair, UnknownType},
	bug, err,
	ir::{self, AddrMode, Intr, IntrMode, Op, Ops},
	lexer::{Span, Spanned},
	note,
	problem::{self, FatalError, Note, Problem, Problems},
	symbol::{
		self, Access, ComplexType, EnumVariant, FuncSignature, Name, ResolvedAccess, StructField,
		Symbol, Type, UniqueName, option_name_str, type_of_enum, type_of_user_type,
	},
	warn,
};

// TODO!: i am not really happy with the current "assert-based" programming.
// I should utilize Rust's cool type system to guarantee symbols existance,
// proper scope ending and so on.

/// Typechecker.
/// Performs type-checking of the specified AST and generates
/// an intermediate representation (IR) program.
pub struct Typechecker<'p> {
	problems: &'p mut Problems,
	program: ir::Program,
	/// Symbols accessible from everywhere in the file.
	symbols: symbol::Table,
}
impl<'p> Typechecker<'p> {
	pub fn check(ast: &mut Ast, problems: &'p mut Problems) -> Result<ir::Program, FatalError> {
		let mut checker = Self {
			problems,
			program: ir::Program::default(),
			symbols: symbol::Table::default(),
		};

		match checker.check_impl(ast) {
			Ok(()) => Ok(checker.program),
			Err(e) => checker.problems.fatal(e),
		}
	}
	fn check_impl(&mut self, ast: &mut Ast) -> problem::Result<()> {
		self.collect(&mut ast.nodes)?;
		self.check_nodes_toplevel(&ast.nodes)?;
		Ok(())
	}

	/// Walk through AST and collect all top-level symbol definitions.
	fn collect(&mut self, nodes: &mut [Node]) -> problem::Result<()> {
		for node in nodes.iter_mut() {
			let Node::Def(def) = node else {
				continue;
			};

			match def {
				Def::Type(def) => {
					let inherits = def.inherits.x.clone();
					let inherits = self.resolve_type(inherits, def.inherits.span)?;

					let symbol = Rc::new(symbol::UserType {
						name: def.name.x.clone(),
						inherits,
						alias: def.alias,
						defined_at: def.name.span,
					});

					let symbol = Symbol::Type(symbol::AnyUserType::User(symbol));
					let name = def.name.x.clone();
					self.symbols.define_symbol(name, symbol)?;
				}

				Def::Enum(def) => {
					let inherits = def.inherits.x.clone();
					let inherits = match inherits {
						UnknownType::Byte => Type::Byte,
						UnknownType::Short => Type::Short,
						_ => {
							return Err(err!(
								def.inherits.span,
								"enums can only inherit from `byte` or `short` types"
							));
						}
					};

					// Collect enum variants.
					let mut variants = HashMap::default();
					for vari in def.variants.iter() {
						let unique_name = self.symbols.new_unique_name();
						let v = EnumVariant {
							name: vari.name.x.clone(),
							unique_name,
							defined_at: vari.name.span,
						};

						variants.insert(vari.name.x.clone(), v);
					}

					// Define enum type.
					let symbol = Rc::new(symbol::Enum {
						name: def.name.x.clone(),
						alias: def.alias,
						inherits,
						variants,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));

					let symbol = Symbol::Type(symbol::AnyUserType::Enum(symbol));
					let name = def.name.x.clone();
					self.symbols.define_symbol(name, symbol)?;
				}

				Def::Struct(def) => {
					let mut struct_size: u16 = 0;

					// Collect struct fields.
					let mut fields = HashMap::default();
					for field in def.fields.iter() {
						let type_span = field.typ.span;
						let typ = field.typ.x.clone();
						let typ = self.resolve_complex(typ, type_span)?;
						let size = typ.size();

						let struct_field = StructField {
							name: field.name.x.clone(),
							typ: Spanned::new(typ, type_span),
							offset: struct_size,
							defined_at: field.name.span,
						};
						fields.insert(field.name.x.clone(), struct_field);

						struct_size += size;
					}

					// Define struct type.
					let symbol = Rc::new(symbol::Struct {
						name: def.name.x.clone(),
						fields,
						size: struct_size,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));

					let symbol = Symbol::Type(symbol::AnyUserType::Struct(symbol));
					let name = def.name.x.clone();
					self.symbols.define_symbol(name, symbol)?;
				}

				Def::Func(def) => {
					let signature = def.signature.x.clone();
					let signature = self.resolve_signature(signature)?;

					let symbol = Rc::new(symbol::Func {
						name: def.name.x.clone(),
						unique_name: self.symbols.new_unique_name(),
						signature,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));

					let symbol = Symbol::Func(symbol);
					let name = def.name.x.clone();
					self.symbols.define_symbol(name, symbol)?;
				}
				Def::Var(def) => {
					let typ = def.typ.x.clone();
					let typ = self.resolve_complex(typ, def.typ.span)?;

					let symbol = Rc::new(symbol::Var {
						name: def.name.x.clone(),
						unique_name: self.symbols.new_unique_name(),
						in_rom: def.in_rom,
						typ: Spanned::new(typ, def.typ.span),
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));

					let symbol = Symbol::Var(symbol);
					let name = def.name.x.clone();
					self.symbols.define_symbol(name, symbol)?;
				}
				Def::Const(def) => {
					let typ = def.typ.x.clone();
					let typ = self.resolve_type(typ, def.typ.span)?;

					let symbol = Rc::new(symbol::Const {
						name: def.name.x.clone(),
						unique_name: self.symbols.new_unique_name(),
						typ,
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));

					let symbol = Symbol::Const(symbol);
					let name = def.name.x.clone();
					self.symbols.define_symbol(name, symbol)?;
				}
				Def::Data(def) => {
					let symbol = Rc::new(symbol::Data {
						name: def.name.x.clone(),
						unique_name: self.symbols.new_unique_name(),
						defined_at: def.name.span,
					});
					def.symbol = Some(Rc::clone(&symbol));

					let symbol = Symbol::Data(symbol);
					let name = def.name.x.clone();
					self.symbols.define_symbol(name, symbol)?;
				}
			}
		}

		Ok(())
	}

	fn check_nodes_toplevel(&mut self, nodes: &[Node]) -> problem::Result<()> {
		for node in nodes.iter() {
			match node {
				Node::Expr(expr) => {
					return Err(err!(
						expr.span(),
						"expressions outside definitions are illegal"
					));
				}
				Node::Def(def) => {
					if let Err(e) = self.check_def(def) {
						// NOTE: collecting errors without returing with `FatalError` because
						// errors within definitions do not mess up other definitions.
						self.problems.push(e);
					}
				}
			}
		}
		Ok(())
	}
	fn check_nodes(&mut self, nodes: &[Node], scope: &mut Scope) -> problem::Result<()> {
		for node in nodes.iter() {
			match node {
				Node::Expr(expr) => {
					self.check_expr(expr, scope)?;
				}
				Node::Def(def) => {
					return Err(err!(def.span(), "no local definitions yet..."));
				}
			}
		}
		Ok(())
	}

	fn check_def(&mut self, def: &Def) -> problem::Result<()> {
		macro_rules! s {
			($symbol:expr, $span:expr) => {
				$symbol
					.as_ref()
					.unwrap_or_else(|| bug!("unexpected `None` symbol at {}", $span))
			};
		}

		match def {
			Def::Type(_) => (/* do nothing */),
			Def::Struct(_) => (/* do nothing */),

			Def::Func(def) => {
				let symbol = s!(def.symbol, def.span);

				let (ws, expect_ws) = match &symbol.signature {
					FuncSignature::Vector => (vec![], vec![]),
					FuncSignature::Proc { inputs, outputs } => {
						let mut ws = Vec::with_capacity(inputs.len());

						// Push function inputs onto the stack.
						for input in inputs.iter() {
							let item = Item::named(
								input.typ.x.clone(),
								input.name.clone().map(|n| n.x),
								input.typ.span,
							);
							ws.push(item);
						}

						let mut expect_ws = Vec::with_capacity(outputs.len());
						for output in outputs.iter() {
							let item = Item::named(
								output.typ.x.clone(),
								output.name.clone().map(|n| n.x),
								output.typ.span,
							);
							expect_ws.push(item);
						}

						(ws, expect_ws)
					}
				};

				// Check function body.
				let mut scope = Scope::new(ws, expect_ws);
				{
					self.check_nodes(&def.body.nodes, &mut scope)?;
				}
				scope.end_block(def.body.end_span)?;

				// Generate IR.
				let func = ir::Func {
					is_vector: matches!(def.signature.x, FuncSignature::Vector),
					body: scope.ops,
				};

				if def.name.x.as_ref() == "on-reset" {
					self.program.reset_func = Some((symbol.unique_name, func));
				} else {
					self.program.funcs.insert(symbol.unique_name, func);
				}
			}

			Def::Var(def) => {
				let symbol = s!(def.symbol, def.span);

				// Generate IR.
				let size = symbol.typ.x.size();

				let var = ir::Var {
					size,
					in_rom: symbol.in_rom,
				};
				self.program.vars.insert(symbol.unique_name, var);
			}

			Def::Const(def) => {
				let symbol = s!(def.symbol, def.span);

				// Type check.
				let mut scope =
					Scope::new(vec![], vec![Item::new(symbol.typ.clone(), Span::default())]);
				{
					self.check_nodes(&def.body.nodes, &mut scope)?;
				}
				scope.end_block(def.name.span)?;

				// Generate IR.
				let cnst = ir::Const { body: scope.ops };
				self.program.consts.insert(symbol.unique_name, cnst);
			}

			Def::Data(def) => {
				let symbol = s!(def.symbol, def.span);

				// Generate IR.
				let mut bytes = Vec::with_capacity(64);

				for node in def.body.nodes.iter() {
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
						Node::Expr(Expr::Include { path, .. }) => {
							let result = read_bin_to(&path.x, &mut bytes);
							if let Err(e) = result {
								return Err(err!(
									path.span,
									"unable to read \"{}\": {}",
									path.x.display(),
									e.kind()
								));
							}
						}

						_ => {
							return Err(err!(node.span(), "code inside data blocks is illegal"));
						}
					}
				}

				let data = ir::Data { body: bytes };
				self.program.datas.insert(symbol.unique_name, data);
			}

			Def::Enum(def) => {
				let symbol = s!(def.symbol, def.span);

				let typ = type_of_enum(symbol);
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

					let ops: ir::Ops;
					if let Some(body) = &vari.body {
						// Type check variant body.
						let mut scope =
							Scope::new(vec![], vec![Item::new(typ.clone(), Span::default())]);
						{
							self.check_nodes(&body.nodes, &mut scope)?;
						}
						scope.end_block(vari.name.span)?;

						ops = scope.ops;
					} else {
						ops = match prev_vari_name {
							Some(prev) if is_short => Ops::new(vec![
								Op::ConstUse(prev),
								Op::Short(1),
								Op::Intr(Intr::Add, IntrMode::SHORT),
							]),
							None if is_short => Ops::new(vec![Op::Short(0)]),

							Some(prev) => Ops::new(vec![
								Op::ConstUse(prev),
								Op::Byte(1),
								Op::Intr(Intr::Add, IntrMode::NONE),
							]),
							None => Ops::new(vec![Op::Byte(0)]),
						};
					}

					// Generate IR.
					let cnst = ir::Const { body: ops };
					self.program.consts.insert(unique_name, cnst);
					prev_vari_name = Some(unique_name);
				}
			}
		}

		Ok(())
	}

	fn check_expr(&mut self, expr: &Expr, scope: &mut Scope) -> problem::Result<()> {
		if scope.cur_block().state == BlockState::Finished {
			// FIXME: this warning is being added for every expression after a `return` or `jump`.
			// It should only appear once and point at the keyword.
			self.problems.push(warn!(expr.span(), "dead code"));
			return Ok(());
		};

		match expr {
			Expr::Byte { value, span } => {
				scope.ws.push(Item::new(Type::Byte, *span));
				scope.ops.push(Op::Byte(*value));
			}
			Expr::Short { value, span } => {
				scope.ws.push(Item::new(Type::Short, *span));
				scope.ops.push(Op::Short(*value));
			}
			Expr::String { string, span } => {
				let typ = Type::short_ptr(ComplexType::unsized_array(Type::Byte));
				scope.ws.push(Item::new(typ, *span));

				// Generate IR.
				// Insert an unique data for each string literal even if strings contents are the same.
				let unique_name = self.symbols.new_unique_name();
				let body = string.as_bytes().into();
				self.program.datas.insert(unique_name, ir::Data { body });

				scope.ops.push(Op::AbsShortAddr {
					name: unique_name,
					offset: 0,
				});
			}

			Expr::Store { access, span } => self.check_store(access, scope, *span)?,

			Expr::Cast { types, span } => self.check_cast(types.as_slice(), scope, *span)?,

			Expr::Bind { names, span } => {
				if names.len() > scope.ws.len() {
					return Err(err!(
						*span,
						"trying to bind {} names but there {} items on the working stack",
						names.len(),
						scope.ws.len()
					));
				}

				for (i, name) in names.iter().rev().enumerate() {
					let len = scope.ws.items.len();
					let item = &mut scope.ws.items[len - 1 - i];

					if name.x.as_ref() == "_" {
						item.name = None;
					} else {
						item.name = Some(name.x.clone());
					}
				}
			}

			Expr::ExpectBind { names, span } => {
				if names.len() > scope.ws.len() {
					return Err(err!(
						*span,
						"expecting {} names but there {} items on the working stack",
						names.len(),
						scope.ws.len()
					));
				}

				let mut notes = Vec::<Note>::default();

				for (idx, name) in names.iter().enumerate() {
					let len = scope.ws.len();
					let item = &scope.ws.items[len - names.len() + idx];

					let item_name = option_name_str(item.name.as_ref());
					if name.x.as_ref() != item_name {
						notes.push(note!(
							item.pushed_at,
							"the name is \"{item_name}\", expected \"{}\"",
							name.x
						))
					}
				}

				if !notes.is_empty() {
					let mut e = err!(*span, "invalid names on the working stack");
					e.notes = notes;
					return Err(e);
				}
			}

			Expr::Intr { kind, mode, span } => {
				// NOTE: we don't handle the error right away because we need to reset stacks keep mode.
				let result = self.check_intrinsic(*kind, *mode, scope, *span);
				scope.ws.reset_keep();
				scope.rs.reset_keep();

				// Generate IR.
				let (kind, mode) = result?;
				scope.ops.push(Op::Intr(kind, mode))
			}
			Expr::Symbol { access, span } => self.check_symbol(access, scope, *span)?,
			Expr::PtrTo { access, span } => self.check_ptr_to(access, scope, *span)?,

			Expr::Block {
				label,
				body,
				span,
				looping,
			} => {
				let block_idx = scope.begin_block(false);
				{
					let name = label.x.clone();
					let unique_name =
						scope.define_label(&mut self.symbols, name, block_idx, label.span)?;

					if *looping {
						let again_label = self.symbols.new_unique_name();

						scope.ops.push(Op::Label(again_label));
						self.check_nodes(&body.nodes, scope)?;
						scope.ops.push(Op::Jump(again_label));
						scope.ops.push(Op::Label(unique_name));
					} else {
						self.check_nodes(&body.nodes, scope)?;
						scope.ops.push(Op::Label(unique_name));
					}
				}
				scope.end_block(*span)?;

				scope.undefine_label(&label.x);
			}

			Expr::Break { label, span } => {
				if scope.blocks.len() <= 1 {
					return Err(err!(*span, "`break` can only be used inside a block"));
				}

				let Some(block_label) = scope.labels.get(&label.x) else {
					let mut e = err!(label.span, "unknown label \"{}\" in this scope", label.x);
					for label in scope.labels.values() {
						e.notes.push(note!(label.span, "available label"));
					}
					return Err(e);
				};
				let label_name = block_label.unique_name;

				scope.propagate_state(block_label.block_idx, *span)?;

				scope.ops.push(Op::Jump(label_name));
			}
			Expr::Return { span } => {
				scope.propagate_state(0, *span)?;
				scope.ops.push(Op::Return);
			}
			Expr::If {
				if_block,
				elif_blocks,
				else_block,
			} => {
				self.check_if(if_block, elif_blocks, else_block.as_ref(), scope)?;
			}
			Expr::While {
				condition,
				body,
				span,
			} => {
				self.check_while(condition, body, scope, *span)?;
			}

			Expr::Padding { span, .. } => {
				return Err(err!(*span, "paddings are only allowed inside data blocks"));
			}
			Expr::Include { span, .. } => {
				return Err(err!(*span, "`include` is only allowed inside data blocks"));
			}
		}

		Ok(())
	}

	fn check_if(
		&mut self,
		if_block: &IfBlock,
		elif_blocks: &[ElifBlock],
		else_block: Option<&IfBlock>,
		scope: &mut Scope,
	) -> problem::Result<()> {
		// FIXME!!: typechecking should skip `if`, `elif` or `else` blocks that returned early (due
		// `break` or `return`) and should NOT account their outputing stack.
		// For example when early-returning in `if { return } else { 10 20* }`, it doesn't matter
		// what the stack signature is at the end of the `else` block because it won't upset the
		// stack balance BECAUSE if the `if` block executes it will not fallthrough to the next
		// operations in the function.

		self.consume_condition(scope, if_block.span)?;

		if !elif_blocks.is_empty()
			&& let Some(else_block) = else_block
		{
			// `if {} elif {} else {}`

			let if_label = self.symbols.new_unique_name();
			let mut next_block_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();

			scope.ops.push(Op::JumpIf(if_label));
			scope.ops.push(Op::Jump(next_block_label));
			scope.ops.push(Op::Label(if_label));

			// if
			{
				scope.begin_block(true);
				self.check_nodes(&if_block.body.nodes, scope)?;
			}

			// We are expecting the output stack of `if`, `elif`s and `else` blocks
			// to be of the same signature.
			let expect = scope.take_snapshot();

			// Restore the stack before the `if` block.
			scope.finish_block();
			let before = scope.pop_block().snapshot;

			scope.ops.push(Op::Jump(end_label));

			// elifs
			for elif_block in elif_blocks {
				scope.ops.push(Op::Label(next_block_label));

				let pass_label = self.symbols.new_unique_name();
				next_block_label = self.symbols.new_unique_name();

				{
					scope.begin_block_with(true, expect.clone());
					// elif condition
					self.check_condition(&elif_block.condition, scope, elif_block.span)?;

					scope.ops.push(Op::JumpIf(pass_label));
					scope.ops.push(Op::Jump(next_block_label));
					scope.ops.push(Op::Label(pass_label));

					{
						// elif body
						scope.begin_block_with(true, expect.clone());
						self.check_nodes(&elif_block.body.nodes, scope)?;
						scope.end_block(elif_block.body.end_span)?;
					}

					scope.end_block(elif_block.span)?;
					scope.restore_snapshot(before.clone());
				}

				scope.ops.push(Op::Jump(end_label));
			}

			scope.ops.push(Op::Label(next_block_label));

			// else
			{
				scope.begin_block_with(true, expect.clone());
				self.check_nodes(&else_block.body.nodes, scope)?;
				scope.end_block(else_block.body.end_span)?;
			}

			scope.ops.push(Op::Label(end_label));
		} else if !elif_blocks.is_empty() {
			// `if {} elif {}`

			let if_label = self.symbols.new_unique_name();
			let mut next_elif_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();

			scope.ops.push(Op::JumpIf(if_label));
			scope.ops.push(Op::Jump(next_elif_label));
			scope.ops.push(Op::Label(if_label));

			// if
			{
				scope.begin_block(true);
				self.check_nodes(&if_block.body.nodes, scope)?;
				scope.end_block(if_block.body.end_span)?;
			}

			scope.ops.push(Op::Jump(end_label));

			// elifs
			for (idx, elif_block) in elif_blocks.iter().enumerate() {
				scope.ops.push(Op::Label(next_elif_label));

				let pass_label = self.symbols.new_unique_name();
				next_elif_label = self.symbols.new_unique_name();

				{
					scope.begin_block(true);
					// elif condition
					self.check_condition(&elif_block.condition, scope, elif_block.span)?;

					scope.ops.push(Op::JumpIf(pass_label));
					if idx < elif_blocks.len() - 1 {
						scope.ops.push(Op::Jump(next_elif_label));
					} else {
						scope.ops.push(Op::Jump(end_label));
					}
					scope.ops.push(Op::Label(pass_label));

					{
						// elif body
						scope.begin_block(true);
						self.check_nodes(&elif_block.body.nodes, scope)?;
						scope.end_block(elif_block.body.end_span)?;
					}

					scope.end_block(elif_block.span)?;
				}

				scope.ops.push(Op::Jump(end_label));
			}

			scope.ops.push(Op::Label(end_label));
		} else if let Some(else_block) = else_block {
			// `if {} else {}`

			let if_label = self.symbols.new_unique_name();
			let else_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();

			scope.ops.push(Op::JumpIf(if_label));
			scope.ops.push(Op::Jump(else_label));
			scope.ops.push(Op::Label(if_label));

			// if
			{
				scope.begin_block(true);
				self.check_nodes(&if_block.body.nodes, scope)?;
			}

			// We are expecting the output stack of `if` and `else` blocks
			// to be of the same signature.
			let expect = scope.take_snapshot();

			// Restore the stack before the `if` block.
			let branching = scope.cur_block().state != BlockState::Finished;
			scope.finish_block();
			scope.pop_block();

			scope.ops.push(Op::Jump(end_label));
			scope.ops.push(Op::Label(else_label));

			// else
			{
				scope.begin_block_with(branching, expect);
				self.check_nodes(&else_block.body.nodes, scope)?;
				scope.end_block(else_block.body.end_span)?;
			}

			scope.ops.push(Op::Label(end_label));
		} else {
			// `if {}`

			let if_label = self.symbols.new_unique_name();
			let end_label = self.symbols.new_unique_name();

			scope.ops.push(Op::JumpIf(if_label));
			scope.ops.push(Op::Jump(end_label));
			scope.ops.push(Op::Label(if_label));

			{
				scope.begin_block(true);
				self.check_nodes(&if_block.body.nodes, scope)?;
				scope.end_block(if_block.body.end_span)?;
			}

			scope.ops.push(Op::Label(end_label))
		}

		Ok(())
	}

	fn check_while(
		&mut self,
		condition: &Spanned<Vec<Node>>,
		body: &Body,
		scope: &mut Scope,
		span: Span,
	) -> problem::Result<()> {
		let again_label = self.symbols.new_unique_name();
		let continue_label = self.symbols.new_unique_name();
		let end_label = self.symbols.new_unique_name();

		scope.ops.push(Op::Label(again_label));

		{
			// Condition
			let expect = self.check_condition(condition, scope, span)?;
			let restore = scope.take_snapshot();

			scope.ops.push(Op::JumpIf(continue_label));
			scope.ops.push(Op::Jump(end_label));
			scope.ops.push(Op::Label(continue_label));

			{
				// Body
				scope.begin_block_with(true, expect);
				self.check_nodes(&body.nodes, scope)?;
				scope.end_block(body.end_span)?;
			}

			scope.restore_snapshot(restore);

			scope.ops.push(Op::Jump(again_label));
			scope.ops.push(Op::Label(end_label));
		}

		Ok(())
	}

	fn check_symbol(
		&mut self,
		access: &Access,
		scope: &mut Scope,
		span: Span,
	) -> problem::Result<()> {
		let resolved = self.symbols.resolve_access(access, span)?;

		match resolved {
			ResolvedAccess::Type(_) => return Err(err!(span, "unexpected use of a user type")),
			ResolvedAccess::Struct(_) => return Err(err!(span, "unexpected use of a struct type")),

			ResolvedAccess::Var {
				var,
				field_type,
				field_offset,
				indexing_type,
			} => {
				let typ = match &field_type.x {
					ComplexType::Primitive(t) => t,
					ComplexType::Struct(_) => {
						return Err(err!(span, "cannot load a struct type"));
					}
					ComplexType::Array { .. } | ComplexType::UnsizedArray { .. } => {
						return Err(err!(span, "cannot load an array type"));
					}
				};

				let stride = match &indexing_type {
					Some(t) => t.x.size(),
					None => 0,
				};

				// Type check.
				if indexing_type.is_some() {
					self.consume_index(&mut scope.ws, var.in_rom, span)?;
				}
				scope.ws.push(Item::new(typ.clone(), span));

				// Generate IR.
				let name = var.unique_name;
				let short = var.in_rom;
				scope.ops.push_addr(name, field_offset, short, stride);

				let intr = if short {
					Intr::Load(AddrMode::AbsShort)
				} else {
					Intr::Load(AddrMode::AbsByte)
				};
				let mode = IntrMode::from_type(&typ);
				scope.ops.push(intr.op_mode(mode));
			}

			ResolvedAccess::Enum { enm, variant } => {
				// Type check.
				scope.ws.push(Item::new(type_of_enum(enm), span));

				// Generate IR.
				scope.ops.push(Op::ConstUse(variant.unique_name));
			}

			ResolvedAccess::Data { data, indexing } => {
				let stride = if indexing { 1 } else { 0 };
				let unique_name = data.unique_name;

				// Type check.
				if indexing {
					self.consume_index(&mut scope.ws, true, span)?;
				}
				scope.ws.push(Item::new(Type::Byte, span));

				// Generate IR.
				scope.ops.push_addr(unique_name, 0, true, stride);
				scope.ops.push(Intr::Load(AddrMode::AbsShort).op());
			}

			ResolvedAccess::Func(func) => match &func.signature {
				FuncSignature::Vector => {
					return Err(err!(span, "calling vector functions is illegal"));
				}
				FuncSignature::Proc { inputs, outputs } => {
					Self::check_proc_call(Some(&func.name), inputs, outputs, scope, span)?;

					// Generate IR
					scope.ops.push(Op::FuncCall(func.unique_name));
				}
			},

			ResolvedAccess::Const(cnst) => {
				// Type check.
				scope.ws.push(Item::new(cnst.typ.clone(), span));

				// Generate IR.
				scope.ops.push(Op::ConstUse(cnst.unique_name));
			}
		};

		Ok(())
	}

	fn check_ptr_to(
		&mut self,
		access: &Spanned<Access>,
		scope: &mut Scope,
		span: Span,
	) -> problem::Result<()> {
		let resolved = self.symbols.resolve_access(&access.x, access.span)?;

		match resolved {
			ResolvedAccess::Const(_)
			| ResolvedAccess::Type(_)
			| ResolvedAccess::Enum { .. }
			| ResolvedAccess::Struct(_) => {
				return Err(err!(
					span,
					"cannot take pointers to {}",
					resolved.kind().plural()
				));
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
					Some(t) => t.x.size(),
					None => 0,
				};

				// Type check.
				if indexing_type.is_some() {
					self.consume_index(&mut scope.ws, var.in_rom, span)?;
				}

				scope.ws.push(Item::new(typ, span));

				// Generate IR.
				let name = var.unique_name;
				let short = var.in_rom;
				scope.ops.push_addr(name, field_offset, short, stride);
			}

			ResolvedAccess::Data { data, indexing } => {
				let stride = if indexing { 1 } else { 0 };

				// Type check.
				let typ = if indexing {
					self.consume_index(&mut scope.ws, true, span)?;

					Type::short_ptr(Type::Byte)
				} else {
					Type::short_ptr(ComplexType::unsized_array(Type::Byte))
				};

				scope.ws.push(Item::new(typ, span));

				// Generate IR.
				scope.ops.push_addr(data.unique_name, 0, true, stride);
			}

			ResolvedAccess::Func(func) => {
				// Type check.
				let typ = Type::FuncPtr(func.signature.clone());
				scope.ws.push(Item::new(typ, span));

				// Generate IR.
				scope.ops.push(Op::AbsShortAddr {
					name: func.unique_name,
					offset: 0,
				});
			}
		};

		Ok(())
	}

	fn check_store(
		&mut self,
		access: &Spanned<Access>,
		scope: &mut Scope,
		span: Span,
	) -> problem::Result<()> {
		let resolved = self.symbols.resolve_access(&access.x, access.span)?;

		// TODO: note to where the symbol is defined.

		match resolved {
			ResolvedAccess::Func(_)
			| ResolvedAccess::Const(_)
			| ResolvedAccess::Type(_)
			| ResolvedAccess::Enum { .. }
			| ResolvedAccess::Struct(_) => {
				return Err(err!(
					access.span,
					"cannot store into {}",
					resolved.kind().plural()
				));
			}

			ResolvedAccess::Var {
				var,
				field_type,
				field_offset,
				indexing_type,
			} => {
				// Type check.
				let expect = match &field_type.x {
					ComplexType::Primitive(t) => t,
					ComplexType::Struct(t) => {
						return Err(err!(
							access.span,
							"cannot store into struct type `{}`",
							t.name
						));
					}
					ComplexType::Array { .. } | ComplexType::UnsizedArray { .. } => {
						return Err(err!(access.span, "cannot store into an array type"));
					}
				};

				if indexing_type.is_some() {
					self.consume_index(&mut scope.ws, var.in_rom, span)?;
				}

				match scope.ws.pop(span) {
					Some(value) => {
						if value.typ != *expect {
							return Err(err!(
								span,
								"cannot store `{}` into `{}`",
								value.typ,
								field_type.x,
							));
						}
					}
					None => {
						return Err(err!(span, "expected `{}` to be stored", field_type.x));
					}
				}

				// Generate IR.
				let stride = match &indexing_type {
					Some(t) => t.x.size(),
					None => 0,
				};

				let name = var.unique_name;
				let short = var.in_rom;
				scope.ops.push_addr(name, field_offset, short, stride);

				let addr = if var.in_rom {
					AddrMode::AbsShort
				} else {
					AddrMode::AbsByte
				};
				let intr = Intr::Store(addr);
				let mode = IntrMode::from_type(expect);
				scope.ops.push(intr.op_mode(mode));
			}

			ResolvedAccess::Data { data, indexing } => {
				let stride = if indexing { 1 } else { 0 };

				if indexing {
					self.consume_index(&mut scope.ws, true, span)?;
				}

				match scope.ws.pop(span) {
					Some(value) => {
						if value.typ != Type::Byte {
							return Err(err!(
								span,
								"cannot store `{}` into data (`[]byte`)",
								value.typ
							));
						}
					}
					None => {
						return Err(err!(span, "expected `byte` to be stored"));
					}
				}

				scope.ops.push_addr(data.unique_name, 0, true, stride);
				scope.ops.push(Intr::Store(AddrMode::AbsShort).op());
			}
		}

		Ok(())
	}

	// TODO: casting should also probaly work with the return stack?
	// Currently i don't know how to syntactically mark casting for return stack.
	fn check_cast(
		&mut self,
		types: &[Pair<UnknownType>],
		scope: &mut Scope,
		span: Span,
	) -> problem::Result<()> {
		let mut items = Vec::with_capacity(types.len());
		for t in types.iter() {
			let typ = self.resolve_type(t.typ.x.clone(), t.typ.span)?;
			items.push(Item::named(typ, t.name.clone().map(|n| n.x), t.typ.span));
		}

		let bytes_to_pop: u16 = items.iter().fold(0, |acc, t| acc + t.typ.size());

		let mut left_to_pop: u16 = bytes_to_pop;

		while left_to_pop > 0 {
			let Some(item) = scope.ws.pop(span) else {
				return Err(err!(
					span,
					"size of the working stack is {left_to_pop} bytes less than expected {bytes_to_pop}"
				));
			};

			let size = item.typ.size();
			if size > left_to_pop {
				return Err(err!(span, "{} bytes are unhandled", size - left_to_pop));
			} else {
				left_to_pop -= size;
			}
		}

		for item in items {
			scope.ws.push(item);
		}

		Ok(())
	}

	fn check_intrinsic(
		&mut self,
		mut intr: Intr,
		mut mode: IntrMode,
		scope: &mut Scope,
		intr_span: Span,
	) -> problem::Result<(Intr, IntrMode)> {
		let (stack, sec_stack) = if mode.contains(IntrMode::RETURN) {
			(&mut scope.rs, &mut scope.ws)
		} else {
			(&mut scope.ws, &mut scope.rs)
		};
		let stack_kind = stack.kind;

		stack.keep = mode.contains(IntrMode::KEEP);

		// TODO: add notes "consumed by" when not enough inputs.

		macro_rules! intr_err {
			($($arg:tt)*) => { Err(err!(intr_span, $($arg)*)) };
		}
		macro_rules! types_err {
			([$($item:tt),*$(,)?], $($arg:tt)*) => {{
				let e = err!(intr_span, $($arg)*);
				Err(e.with_notes([ $(problem::note_this_is(&$item), )* ]))
			}};
		}
		macro_rules! sizes_err {
			([$($item:tt),*$(,)?], $($arg:tt)*) => {{
				let e = err!(intr_span, $($arg)*);
				Err(e.with_notes([ $(problem::note_size_is(&$item), )* ]))
			}};
		}
		macro_rules! pop {
			() => {
				stack.pop(intr_span)
			};
		}

		match intr {
			Intr::Add | Intr::Sub | Intr::Mul | Intr::Div => {
				// ( a b -- a+b )
				let (Some(b), Some(a)) = (pop!(), pop!()) else {
					return intr_err!("expected 2 arithmetic operands");
				};

				let output = match (&a.typ, &b.typ) {
					(Type::Byte, Type::Byte) => Type::Byte,
					(Type::Short, Type::Short) => Type::Short,

					(Type::Byte, Type::BytePtr(t)) => Type::BytePtr(t.clone()),
					(Type::Short, Type::ShortPtr(t)) => Type::ShortPtr(t.clone()),
					(Type::Short, Type::FuncPtr(t)) => Type::FuncPtr(t.clone()),
					(Type::BytePtr(t), Type::Byte) => Type::BytePtr(t.clone()),
					(Type::ShortPtr(t), Type::Short) => Type::ShortPtr(t.clone()),
					(Type::FuncPtr(t), Type::Short) => Type::FuncPtr(t.clone()),

					(Type::BytePtr(ai), Type::BytePtr(bi)) if ai == bi => Type::BytePtr(ai.clone()),
					(Type::ShortPtr(ai), Type::ShortPtr(bi)) if ai == bi => {
						Type::ShortPtr(ai.clone())
					}
					(Type::FuncPtr(ai), Type::FuncPtr(bi)) if ai == bi => Type::FuncPtr(ai.clone()),

					_ => {
						return types_err!([a, b], "mismatched types of the arithmetic operands");
					}
				};
				mode |= IntrMode::from_type(&output);

				stack.push(Item::new(output, intr_span));

				Ok((intr, mode))
			}

			// ( a -- a+1 )
			Intr::Inc => match pop!() {
				Some(a) => {
					mode |= IntrMode::from_type(&a.typ);
					stack.push(a);
					Ok((intr, mode))
				}
				_ => intr_err!("expected an operand"),
			},

			// ( a shift8 -- c )
			Intr::Shift => match (pop!(), pop!()) {
				(Some(shift8), Some(a)) => {
					if shift8.typ != Type::Byte {
						let e = err!(
							intr_span,
							"the shift amount can only be a `byte`"
						);
						let n = problem::note_this_is_but_expected(&shift8, &Type::Byte);
						return Err(e.with_note(n));
					}

					mode |= IntrMode::from_type(&a.typ);
					stack.push(Item::new(a.typ, intr_span));
					Ok((intr, mode))
				}

				(Some(_), None) => intr_err!("also expected an operand"),
				_ => intr_err!("expected an operand and a shift amount"),
			},

			// ( a b -- c )
			Intr::And | Intr::Or | Intr::Xor => {
				let output = match (pop!(), pop!()) {
					(Some(b), Some(a)) => match (&a.typ, &b.typ) {
						(Type::Byte, Type::Byte) => Type::Byte,
						(Type::Short, Type::Short) => Type::Short,
						(Type::Byte, Type::Short) | (Type::Short, Type::Byte) => {
							// TODO: hint to the input types
							return types_err!(
								[a, b],
								"mismatched types of the logic operands",
							);
						}
						(_, _) => {
							return types_err!(
								[a, b],
								"can only perform logic operations on `byte`s or `short`s",
							);
						}
					},

					_ => {
						return intr_err!("expected 2 logic operands");
					}
				};

				mode |= IntrMode::from_type(&output);

				stack.push(Item::new(output, intr_span));
				Ok((intr, mode))
			}

			// ( a b -- bool8 )
			Intr::Eq | Intr::Neq | Intr::Gth | Intr::Lth => {
				let (b, a) = match (pop!(), pop!()) {
					(Some(b), Some(a)) => (b, a),
					_ => return intr_err!("expected 2 operands for comparison"),
				};

				mode |= IntrMode::from_type(&a.typ);

				if !a.typ.similar(&b.typ) {
					return types_err!([a, b], "the types of the operands must be similar");
				}

				stack.push(Item::new(Type::Byte, intr_span));
				Ok((intr, mode))
			}

			// ( a -- )
			Intr::Pop => {
				let Some(a) = pop!() else {
					return intr_err!("the {stack_kind} is already empty");
				};

				mode |= IntrMode::from_type(&a.typ);
				Ok((intr, mode))
			}

			// ( a b -- b a )
			Intr::Swap => {
				let (Some(b), Some(a)) = (pop!(), pop!()) else {
					return intr_err!("expected 2 items to swap");
				};

				if a.typ.size() != b.typ.size() {
					return sizes_err!([a, b], "cannot swap items of different sizes");
				}

				mode |= IntrMode::from_type(&a.typ);
				stack.push(b);
				stack.push(a);
				Ok((intr, mode))
			}

			// ( a b -- b )
			Intr::Nip => {
				let (Some(b), Some(a)) = (pop!(), pop!()) else {
					return intr_err!("expected 2 items to nip");
				};
				if a.typ.size() != b.typ.size() {
					return sizes_err!([a, b], "cannot nip items of different sizes");
				}

				mode |= IntrMode::from_type(&a.typ);
				stack.push(b);
				Ok((intr, mode))
			}

			// ( a b c -- b c a )
			Intr::Rot => {
				let (Some(c), Some(b), Some(a)) = (pop!(), pop!(), pop!()) else {
					return intr_err!("expected 3 items to rotate");
				};
				if a.typ.size() != b.typ.size() || b.typ.size() != c.typ.size() {
					return sizes_err!([a, b], "cannot rotate items of different sizes");
				}

				mode |= IntrMode::from_type(&a.typ);
				stack.push(b);
				stack.push(c);
				stack.push(a);
				Ok((intr, mode))
			}

			// ( a -- a a )
			Intr::Dup => {
				let Some(a) = pop!() else {
					return intr_err!("expected an item to duplicate");
				};

				mode |= IntrMode::from_type(&a.typ);
				stack.push(a.clone());
				stack.push(Item::named(a.typ, a.name.clone(), intr_span));
				Ok((intr, mode))
			}

			// ( a b -- a b a )
			Intr::Over => {
				let (Some(b), Some(a)) = (pop!(), pop!()) else {
					return intr_err!("expected 2 items to duplicate over");
				};
				if a.typ.size() != b.typ.size() {
					return sizes_err!([a, b], "i cannot duplicate over items of different sizes");
				}

				mode |= IntrMode::from_type(&a.typ);
				stack.push(a.clone());
				stack.push(b);
				stack.push(Item::named(a.typ, a.name, intr_span));
				Ok((intr, mode))
			}

			// ( a -- | a )
			Intr::Sth => {
				let Some(a) = pop!() else {
					return intr_err!("expected an item to stash");
				};

				mode |= IntrMode::from_type(&a.typ);
				sec_stack.push(a);
				Ok((intr, mode))
			}

			// ( ptr -- value )
			Intr::Load(AddrMode::Unknown) => {
				let Some(ptr) = pop!() else {
					return intr_err!("expected a pointer to load");
				};

				let output = match &ptr.typ {
					Type::BytePtr(t) => t,
					Type::ShortPtr(t) => t,
					Type::FuncPtr(_) => {
						return types_err!([ptr], "cannot load function pointers");
					}
					t => return types_err!([ptr], "expected a pointer, but got a `{t}`"),
				};

				let output = match output.as_ref() {
					ComplexType::Primitive(t) => t,
					ComplexType::Struct(_) => {
						return types_err!([ptr], "cannot load structs onto a stack");
					}
					ComplexType::Array { .. } | ComplexType::UnsizedArray { .. } => {
						return types_err!([ptr], "cannot load arrays onto a stack");
					}
				};

				if output.size() == 2 {
					intr = Intr::Load(AddrMode::AbsShort);
				} else {
					intr = Intr::Load(AddrMode::AbsByte);
				}

				mode |= IntrMode::from_type(&output);

				stack.push(Item::new(output.clone(), intr_span));
				Ok((intr, mode))
			}
			Intr::Load(addr) => {
				bug!("address mode of `load` intrinsic cannot be `{addr:?}` at typecheck stage")
			}

			// ( value ptr -- )
			Intr::Store(AddrMode::Unknown) => {
				let (Some(ptr), Some(value)) = (pop!(), pop!()) else {
					return intr_err!("expected a value and a pointer");
				};

				let expect = match &ptr.typ {
					Type::BytePtr(t) => t,
					Type::ShortPtr(t) => t,
					Type::FuncPtr(_) => {
						return types_err!([ptr], "cannot store into function pointers");
					}
					t => return types_err!([ptr], "expected a pointer, but got a `{t}`"),
				};
				let expect = match expect.as_ref() {
					ComplexType::Primitive(t) => t,
					ComplexType::Struct(_) => {
						return types_err!([ptr], "cannot store into structs");
					}
					ComplexType::Array { .. } | ComplexType::UnsizedArray { .. } => {
						return types_err!([ptr], "cannot store into arrays");
					}
				};

				if *expect != value.typ {
					let e = err!(
						intr_span,
						"cannot store a `{}` into a `{}`",
						value.typ,
						ptr.typ
					);
					return Err(e.with_notes([
						problem::note_this_is_but_expected(&value, expect),
						problem::note_this_is(&ptr),
					]));
				}

				let addr_mode = if ptr.typ.size() == 2 {
					AddrMode::AbsShort
				} else {
					AddrMode::AbsByte
				};

				intr = Intr::Store(addr_mode);
				mode |= IntrMode::from_type(&value.typ);
				Ok((intr, mode))
			}
			Intr::Store(addr) => {
				bug!("address mode of `store` intrinsic cannot be `{addr:?}` at typecheck stage")
			}

			Intr::Call => {
				let Some(ptr) = pop!() else {
					return intr_err!("expected a function pointer to call");
				};
				let Type::FuncPtr(sig) = &ptr.typ else {
					return types_err!([ptr], "expected a function pointer, but got a `{}`", ptr.typ);
				};

				match &sig {
					FuncSignature::Vector => {
						return types_err!([ptr], "cannot call vector function pointers");
					}
					FuncSignature::Proc { inputs, outputs } => {
						let result = Self::check_proc_call(None, inputs, outputs, scope, intr_span);
						if let Err(e) = result {
							let n = note!(ptr.pushed_at, "while calling this function pointer");
							return Err(e.with_note(n));
						}
					}
				}

				mode |= IntrMode::SHORT;
				Ok((intr, mode))
			}

			// ( device8 -- value )
			Intr::Input | Intr::Input2 => {
				let Some(device8) = pop!() else {
					return intr_err!("expected a device port");
				};
				if device8.typ != Type::Byte {
					return intr_err!("expected a device port, but got a `{}`", device8.typ);
				}

				if intr == Intr::Input2 {
					stack.push(Item::new(Type::Short, intr_span));
					Ok((intr, mode | IntrMode::SHORT))
				} else {
					stack.push(Item::new(Type::Byte, intr_span));
					Ok((intr, mode))
				}
			}

			// ( value device8 -- )
			Intr::Output => {
				let (Some(device8), Some(value)) = (pop!(), pop!()) else {
					return intr_err!("expected a value and a device port");
				};
				if device8.typ != Type::Byte {
					return intr_err!("expected a device port, but got a `{}`", device8.typ);
				}

				mode |= IntrMode::from_type(&value.typ);
				Ok((intr, mode))
			}
		}
	}

	// ==============================
	// Helper functions
	// ==============================

	fn check_condition(
		&mut self,
		condition: &Spanned<Vec<Node>>,
		scope: &mut Scope,
		span: Span,
	) -> problem::Result<Snapshot> {
		let expect = scope.take_snapshot();
		self.check_nodes(&condition.x, scope)?;
		self.consume_condition(scope, span)?;
		Ok(expect)
	}
	#[inline(always)]
	fn check_proc_call(
		name: Option<&Name>,
		inputs: &[Pair<Type>],
		outputs: &[Pair<Type>],
		scope: &mut Scope,
		span: Span,
	) -> problem::Result<()> {
		// Check number of inputs
		if scope.ws.len() < inputs.len() {
			// Not enough inputs
			if let Some(name) = name {
				return Err(err!(
					span,
					"expected {} inputs for `{name}` function, but got {}",
					inputs.len(),
					scope.ws.len()
				));
			} else {
				return Err(err!(
					span,
					"expected {} inputs for the calling function pointer, but got {}",
					inputs.len(),
					scope.ws.len()
				));
			}
		}

		// Check each input type
		let mut notes = Vec::<Note>::default();
		for (idx, input) in inputs.iter().enumerate() {
			let len = scope.ws.len();
			let item = &scope.ws.items[len - inputs.len() + idx];

			if item.typ != input.typ.x {
				let n = problem::note_this_is_but_expected(item, &input.typ.x);
				notes.push(n);
			}
		}

		// Consume inputs
		scope.ws.drain(inputs.len(), span);

		if !notes.is_empty() {
			let mut e: Problem;
			if let Some(name) = name {
				e = err!(span, "invalid inputs for function `{name}`");
			} else {
				e = err!(span, "invalid inputs for the calling function pointer");
			}
			e.notes = notes;
			return Err(e);
		}

		// Push outputs onto the working stack
		for output in outputs.iter() {
			scope.ws.push(Item::new(output.typ.x.clone(), span));
		}

		Ok(())
	}

	fn consume_condition(&mut self, scope: &mut Scope, span: Span) -> problem::Result<()> {
		let Some(bool8) = scope.ws.pop(span) else {
			return Err(err!(span, "expected a condition"));
		};
		if bool8.typ != Type::Byte {
			let e = err!(span, "condition is not a `byte`");
			let n = problem::note_this_is_but_expected(&bool8, &Type::Byte);
			return Err(e.with_note(n));
		}

		Ok(())
	}
	fn consume_index(&self, stack: &mut Stack, short: bool, span: Span) -> problem::Result<()> {
		let typ = if short { Type::Short } else { Type::Byte };

		let Some(value) = stack.pop(span) else {
			return Err(err!(span, "expected a `{typ}` index, but got nothing"));
		};
		if value.typ != typ {
			let e = err!(span, "expected a `{typ}` index, but got a `{}`", value.typ);
			let n = problem::note_this_is(&value);
			return Err(e.with_note(n));
		}

		Ok(())
	}

	fn resolve_type(&mut self, typ: UnknownType, span: Span) -> problem::Result<Type> {
		match typ {
			UnknownType::Byte => Ok(Type::Byte),
			UnknownType::Short => Ok(Type::Short),
			UnknownType::BytePtr(t) => {
				Ok(Type::byte_ptr(self.resolve_complex_impl(*t, span, true)?))
			}
			UnknownType::ShortPtr(t) => {
				Ok(Type::short_ptr(self.resolve_complex_impl(*t, span, true)?))
			}
			UnknownType::FuncPtr(sig) => Ok(Type::FuncPtr(self.resolve_signature(sig)?)),
			UnknownType::Type(name) => {
				let symbol = self.symbols.get_type(&name, span)?;
				match symbol {
					symbol::AnyUserType::User(t) => Ok(type_of_user_type(t)),
					symbol::AnyUserType::Enum(t) => Ok(type_of_enum(t)),
					symbol::AnyUserType::Struct(t) => Err(err!(
						span,
						"expected a simple type, but got a struct type `{}`",
						t.name
					)),
				}
			}
			UnknownType::Array { .. } | UnknownType::UnsizedArray { .. } => {
				Err(err!(span, "expected a simple type, but got an array type"))
			}
		}
	}
	#[inline(always)]
	fn resolve_complex_impl(
		&mut self,
		typ: UnknownType,
		span: Span,
		allow_unsized_array: bool,
	) -> problem::Result<ComplexType> {
		match typ {
			UnknownType::Byte => Ok(Type::Byte.into()),
			UnknownType::Short => Ok(Type::Short.into()),
			UnknownType::BytePtr(t) => {
				let t = self.resolve_complex_impl(*t, span, true)?;
				Ok(Type::BytePtr(t.into()).into())
			}
			UnknownType::ShortPtr(t) => {
				let t = self.resolve_complex_impl(*t, span, true)?;
				Ok(Type::ShortPtr(t.into()).into())
			}
			UnknownType::FuncPtr(sig) => {
				let sig = self.resolve_signature(sig)?;
				Ok(Type::FuncPtr(sig).into())
			}
			UnknownType::Type(name) => {
				let typ = self.symbols.get_type(&name, span)?;
				match typ {
					symbol::AnyUserType::User(t) => Ok(type_of_user_type(t).into()),
					symbol::AnyUserType::Enum(t) => Ok(type_of_enum(t).into()),
					symbol::AnyUserType::Struct(t) => Ok(ComplexType::Struct(Rc::clone(t))),
				}
			}
			UnknownType::Array { typ, count } => Ok(ComplexType::Array {
				typ: self.resolve_complex_impl(*typ, span, false)?.into(),
				count,
			}),
			UnknownType::UnsizedArray { typ } => {
				if allow_unsized_array {
					let typ = self.resolve_complex_impl(*typ, span, false)?;
					Ok(ComplexType::UnsizedArray { typ: typ.into() })
				} else {
					return Err(err!(span, "you can only take pointers to unsized arrays"));
				}
			}
		}
	}
	/// Convert `UnknownType` into `ComplexType`.
	fn resolve_complex(&mut self, typ: UnknownType, span: Span) -> problem::Result<ComplexType> {
		self.resolve_complex_impl(typ, span, false)
	}
	/// Convert `FuncSignature<UnknownType>` into `FuncSignature<Type>`.
	fn resolve_signature(
		&mut self,
		sig: FuncSignature<UnknownType>,
	) -> problem::Result<FuncSignature<Type>> {
		fn into_known(
			checker: &mut Typechecker,
			types: Vec<Pair<UnknownType>>,
		) -> problem::Result<Vec<Pair<Type>>> {
			let mut result = Vec::with_capacity(types.len());
			for t in types.into_iter() {
				let typ = checker.resolve_type(t.typ.x, t.typ.span)?;

				result.push(Pair {
					typ: Spanned::new(typ, t.typ.span),
					name: t.name,
					span: t.span,
				});
			}
			Ok(result)
		}

		match sig {
			FuncSignature::Vector { .. } => Ok(FuncSignature::Vector),
			FuncSignature::Proc {
				inputs, outputs, ..
			} => Ok(FuncSignature::Proc {
				inputs: into_known(self, inputs)?,
				outputs: into_known(self, outputs)?,
			}),
		}
	}
}

fn read_bin_to(path: impl AsRef<Path>, buffer: &mut Vec<u8>) -> io::Result<()> {
	// TODO!!: path must be relative to the current file's path,
	// not to the current working dir.
	let cwd = std::env::current_dir()?;
	let path = cwd.join(&path).canonicalize()?;
	let mut file = fs::File::open(&path)?;
	let meta = file.metadata()?;
	let file_len = meta.len() as usize;

	if buffer.try_reserve(file_len).is_err() {
		return Err(io::Error::new(
			io::ErrorKind::FileTooLarge,
			"file too large",
		));
	}

	const CHUNK_SIZE: usize = 128;
	let mut read_size: usize = 0;

	loop {
		let mut chunk: [u8; CHUNK_SIZE] = [0; CHUNK_SIZE];
		let size = file.read(&mut chunk)?;
		if size == 0 {
			return Ok(());
		}

		buffer.extend_from_slice(&chunk[..size]);
		read_size += size;

		// TODO: allow user to customize the limit.
		if read_size > 1024 * 1024 {
			// Exit if we read more than 1MB.
			return Err(io::Error::new(
				io::ErrorKind::FileTooLarge,
				"file too large",
			));
		}
	}
}
