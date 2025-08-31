use std::collections::HashMap;

use crate::{
	ast::{Ast, Definition, Expr, FuncArgs, Name, Node, SymbolKind},
	error::{self, ErrorKind, HintKind},
	lexer::{Span, Spanned},
	program::{
		AddrKind, Constant, Data, Function, Intrinsic, IntrinsicMode, Op, Program, Variable,
	},
	symbols::{SymbolsTable, UniqueName},
};

/// Let it crash when a field in a map was overwritten
fn ensure_no_overwrite<T>(opt: Option<T>, name: &Name) {
	if opt.is_some() {
		unreachable!("unexpected name collision {name:?}");
	}
}

/// Let it crash when `opt` is `None`
fn ensure_exists<T>(opt: Option<T>, name: &Name) -> T {
	match opt {
		Some(v) => v,
		None => unreachable!("unexpected non-existing name {name:?}"),
	}
}

/// Intermediate program generator from a typed AST
#[derive(Debug)]
pub struct Generator {
	program: Program,
	symbols: SymbolsTable,

	/// List of labels unique names accessible in the current scope
	labels: HashMap<Name, UniqueName>,
}
impl Generator {
	pub fn generate(typed_ast: &Ast, symbols: SymbolsTable) -> error::Result<Program> {
		assert!(typed_ast.typed, "provided AST must be typed");

		let mut gener = Self {
			program: Program::default(),
			symbols,

			labels: HashMap::with_capacity(16),
		};
		gener.gen_nodes(&typed_ast.nodes, &mut vec![])?;

		Ok(gener.program)
	}

	fn gen_nodes(&mut self, nodes: &[Spanned<Node>], ops: &mut Vec<Op>) -> error::Result<()> {
		for node in nodes.iter() {
			match &node.x {
				Node::Def(def) => self.gen_definition(def, node.span)?,
				Node::Expr(expr) => self.gen_expression(expr, ops)?,
			}
		}

		Ok(())
	}
	fn gen_expression(&mut self, expr: &Expr, ops: &mut Vec<Op>) -> error::Result<()> {
		match expr {
			Expr::Byte(b) => ops.push(Op::Byte(*b)),
			Expr::Short(s) => ops.push(Op::Short(*s)),
			Expr::Padding(p) => ops.push(Op::Padding(*p)),
			Expr::String(s) => {
				let data = Data {
					body: s.clone().into_boxed_bytes(),
				};

				// Allow strings with the same contents to be stored twice
				let unique_name = self.symbols.new_unique_name("string");
				self.program.datas.insert(unique_name.clone(), data);

				ops.push(Op::ShortAddrOf(unique_name));
			}

			Expr::Intrinsic(intr, mode) => ops.push(Op::Intrinsic(*intr, *mode)),

			Expr::Symbol(_, SymbolKind::Binding, _) => (/* ignore */),
			Expr::Symbol(name, kind, mode) => {
				let unique_name = ensure_exists(self.symbols.get(name), name).x.unique_name();

				match kind {
					SymbolKind::Unknown => unreachable!("unexpected unknown symbol {name:?}"),
					SymbolKind::Binding => unreachable!(),

					SymbolKind::Func => {
						ops.push(Op::Call(unique_name.clone()));
					}
					SymbolKind::Var => {
						ops.push(Op::ByteAddrOf(unique_name.clone()));
						ops.push(Op::Intrinsic(Intrinsic::Load(AddrKind::AbsByte), *mode));
					}
					SymbolKind::Const => {
						ops.push(Op::ConstUse(unique_name.clone()));
					}
					SymbolKind::Data => {
						ops.push(Op::ShortAddrOf(unique_name.clone()));
						ops.push(Op::Intrinsic(
							Intrinsic::Load(AddrKind::AbsShort),
							IntrinsicMode::NONE,
						));
					}
				}
			}
			Expr::PtrTo(_, SymbolKind::Binding) => (/* ignore */),
			Expr::PtrTo(name, kind) => {
				let unique_name = ensure_exists(self.symbols.get(name), name).x.unique_name();

				match kind {
					SymbolKind::Unknown => unreachable!("unexpected pointer to unknown {name:?}"),
					SymbolKind::Const => unreachable!("unexpected pointer to constant {name:?}"),
					SymbolKind::Binding => unreachable!(),

					SymbolKind::Func => ops.push(Op::ShortAddrOf(unique_name.clone())),
					SymbolKind::Var => ops.push(Op::ByteAddrOf(unique_name.clone())),
					SymbolKind::Data => ops.push(Op::ShortAddrOf(unique_name.clone())),
				}
			}

			Expr::Block {
				looping,
				label,
				body,
			} => {
				let unique_label = self.symbols.new_unique_name(&label.x);

				// Define label's unique name for the current scope
				let opt = self.labels.insert(label.x.clone(), unique_label.clone());
				ensure_no_overwrite(opt, &label.x);

				if *looping {
					let repeat_label = self.symbols.new_unique_name("loop-repeat");
					ops.push(Op::Label(repeat_label.clone()));
					self.gen_nodes(body, ops)?;
					ops.push(Op::Jump(repeat_label.clone()));
					ops.push(Op::Label(unique_label.clone()));
				} else {
					self.gen_nodes(body, ops)?;
					ops.push(Op::Label(unique_label.clone()));
				}

				// Undefine label
				self.labels.remove(&label.x);
			}
			Expr::Jump { label, conditional } => {
				let Some(block_label) = self.labels.get(&label.x) else {
					unreachable!("unexpected non-existing label {:?}", label.x);
				};

				if *conditional {
					ops.push(Op::JumpIf(block_label.clone()));
				} else {
					ops.push(Op::Jump(block_label.clone()));
				}
			}
			Expr::If { if_body, else_body } => {
				if let Some(else_body) = else_body {
					let if_skip_label = self.symbols.new_unique_name("if-skip");
					let else_skip_label = self.symbols.new_unique_name("else-skip");

					ops.push(Op::JumpIf(else_skip_label.clone()));

					// Else block
					self.gen_nodes(&else_body, ops)?;

					ops.push(Op::Jump(if_skip_label.clone()));
					ops.push(Op::Label(else_skip_label));

					// If block
					self.gen_nodes(&if_body, ops)?;

					ops.push(Op::Label(if_skip_label));
				} else {
					let skip_label = self.symbols.new_unique_name("if-skip");
					let continue_label = self.symbols.new_unique_name("if-continue");

					ops.push(Op::JumpIf(continue_label.clone()));
					ops.push(Op::Jump(skip_label.clone()));
					ops.push(Op::Label(continue_label));

					self.gen_nodes(if_body, ops)?;

					ops.push(Op::Label(skip_label));
				}
			}
			Expr::While { condition, body } => {
				let repeat_label = self.symbols.new_unique_name("while-repeat");
				let continue_label = self.symbols.new_unique_name("while-continue");
				let break_label = self.symbols.new_unique_name("while-break");

				ops.push(Op::Label(repeat_label.clone()));

				self.gen_nodes(condition, ops)?;

				ops.push(Op::JumpIf(continue_label.clone()));
				ops.push(Op::Jump(break_label.clone()));
				ops.push(Op::Label(continue_label));

				self.gen_nodes(body, ops)?;

				ops.push(Op::Jump(repeat_label));
				ops.push(Op::Label(break_label));
			}

			Expr::Bind(_) => (/* ignore */),
		}

		Ok(())
	}
	fn gen_definition(&mut self, def: &Definition, def_span: Span) -> error::Result<()> {
		match def {
			Definition::Func(def) => {
				let mut body = Vec::<Op>::with_capacity(128);
				self.gen_nodes(&def.body, &mut body)?;

				let unique_name = self.symbol_unique_name(&def.name);
				let func = Function {
					is_vector: matches!(def.args, FuncArgs::Vector),
					body: body.into(),
				};

				if def.name.as_ref() == "on-reset" {
					assert!(self.program.reset_func.is_none());
					self.program.reset_func = Some((unique_name.clone(), func));
				} else {
					let opt = self.program.funcs.insert(unique_name.clone(), func);
					ensure_no_overwrite(opt, &def.name);
				}
			}

			Definition::Var(def) => {
				let unique_name = self.symbol_unique_name(&def.name);
				let var = Variable {
					size: def.typ.x.size(),
				};

				let opt = self.program.vars.insert(unique_name.clone(), var);
				ensure_no_overwrite(opt, &def.name);
			}

			Definition::Const(def) => {
				let mut body = Vec::<Op>::with_capacity(128);
				self.gen_nodes(&def.body, &mut body)?;

				let unique_name = self.symbol_unique_name(&def.name);
				let cnst = Constant { body: body.into() };

				let opt = self.program.consts.insert(unique_name.clone(), cnst);
				ensure_no_overwrite(opt, &def.name);
			}

			Definition::Data(def) => {
				let mut bytes = Vec::<u8>::with_capacity(128);

				for node in def.body.iter() {
					match &node.x {
						Node::Expr(Expr::Byte(b)) => bytes.push(*b),
						Node::Expr(Expr::Short(s)) => {
							let a = ((s & 0xFF00) >> 8) as u8;
							let b = (s & 0x00FF) as u8;
							bytes.push(a);
							bytes.push(b);
						}
						Node::Expr(Expr::Padding(p)) => {
							for _ in 0..*p {
								bytes.push(0)
							}
						}
						Node::Expr(Expr::String(s)) => {
							bytes.extend(s.as_bytes());
						}

						_ => {
							let mut err = ErrorKind::IllegalExprInData.err(def_span);
							err.hints.push(HintKind::CausedBy, node.span);
							return Err(err);
						}
					}
				}

				let unique_name = self.symbol_unique_name(&def.name);
				let data = Data { body: bytes.into() };

				let opt = self.program.datas.insert(unique_name.clone(), data);
				ensure_no_overwrite(opt, &def.name);
			}
		}

		Ok(())
	}

	fn symbol_unique_name(&self, name: &Name) -> &UniqueName {
		match self.symbols.get(name) {
			Some(sym) => sym.x.unique_name(),
			None => unreachable!("unexpected non-existing symbol {name:?}"),
		}
	}
}
