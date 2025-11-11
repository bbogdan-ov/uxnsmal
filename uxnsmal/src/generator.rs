use crate::{
	ast::{Ast, Def, Expr, FuncArgs, Node},
	error::{self, Error},
	lexer::{Span, Spanned},
	program::{Constant, Data, Function, IntrMode, Intrinsic, Op, Program, Variable},
	symbols::{FuncSignature, Name, SymbolSignature, SymbolsTable},
};

pub struct Generator<'a> {
	symbols: &'a mut SymbolsTable,
	program: Program,
}
impl<'a> Generator<'a> {
	pub fn generate(ast: &Ast, symbols: &'a mut SymbolsTable) -> error::Result<Program> {
		let mut gener = Self {
			symbols,
			program: Program::default(),
		};
		gener.gen_nodes(&ast.nodes, 0, &mut vec![])?;
		Ok(gener.program)
	}

	fn gen_nodes(
		&mut self,
		nodes: &[Spanned<Node>],
		level: u32,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		for node in nodes.iter() {
			self.gen_node(&node.x, node.span, level, ops)?;
		}
		Ok(())
	}

	fn gen_node(
		&mut self,
		node: &Node,
		node_span: Span,
		level: u32,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		match node {
			Node::Def(def) => self.gen_def(def, node_span, level),
			Node::Expr(expr) => self.gen_expr(expr, node_span, level, ops),
		}
	}

	fn gen_expr(
		&mut self,
		expr: &Expr,
		expr_span: Span,
		level: u32,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		match expr {
			Expr::Byte(b) => {
				ops.push(Op::Byte(*b));
			}
			Expr::Short(s) => {
				ops.push(Op::Short(*s));
			}
			Expr::String(s) => {
				let unique_name = self.symbols.new_unique_name();
				let data = Data {
					body: s.as_bytes().into(),
				};
				self.program.datas.insert(unique_name, data);

				ops.push(Op::AbsShortAddrOf(unique_name));
			}
			Expr::Padding(_) => {
				todo!("`Expr::Padding` outside 'data' blocks should error before typecheck stage");
			}

			Expr::Intrinsic(intr, mode) => ops.push(Op::Intrinsic(*intr, *mode)),
			Expr::Symbol(name) => self.gen_symbol(name, expr_span, ops)?,
			Expr::PtrTo(name) => self.gen_ptr_to(name, expr_span, ops)?,

			Expr::Block {
				looping: _,
				label,
				body,
			} => {
				let label_unique_name =
					self.symbols
						.define_label(label.x.clone(), level, label.span)?;
				self.gen_nodes(body, level + 1, ops)?;
				ops.push(Op::Label(label_unique_name));
				self.symbols.undefine_label(&label.x);
			}

			Expr::Jump { label, conditional } => {
				let Some(block_label) = self.symbols.labels.get(&label.x).cloned() else {
					return Err(Error::UnknownLabel(label.span));
				};

				if *conditional {
					ops.push(Op::JumpIf(block_label.unique_name));
				} else {
					ops.push(Op::Jump(block_label.unique_name));
				}
			}

			Expr::If { if_body, else_body } => {
				if let Some(else_body) = else_body {
					// If-else chain

					let if_begin_label = self.symbols.new_unique_name();
					let end_label = self.symbols.new_unique_name();

					ops.push(Op::JumpIf(if_begin_label));

					// 'else' block
					self.gen_nodes(else_body, level + 1, ops)?;
					ops.push(Op::Jump(end_label));

					// 'if' block
					ops.push(Op::Label(if_begin_label));
					self.gen_nodes(if_body, level + 1, ops)?;
					ops.push(Op::Label(end_label));
				} else {
					let if_begin_label = self.symbols.new_unique_name();
					let end_label = self.symbols.new_unique_name();

					// Single 'if'
					ops.push(Op::JumpIf(if_begin_label));
					ops.push(Op::Jump(end_label));
					ops.push(Op::Label(if_begin_label));
					self.gen_nodes(if_body, level + 1, ops)?;
					ops.push(Op::Label(end_label));
				}
			}

			Expr::While { condition, body } => {
				let again_label = self.symbols.new_unique_name();
				let continue_label = self.symbols.new_unique_name();
				let end_label = self.symbols.new_unique_name();

				ops.push(Op::Label(again_label));

				self.gen_nodes(condition, level + 1, ops)?;
				ops.push(Op::JumpIf(continue_label));
				ops.push(Op::Jump(end_label));
				ops.push(Op::Label(continue_label));

				self.gen_nodes(body, level + 1, ops)?;
				ops.push(Op::Jump(again_label));
				ops.push(Op::Label(end_label));
			}
		}
		Ok(())
	}

	fn gen_symbol(
		&mut self,
		name: &Name,
		symbol_span: Span,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.table.get(name) else {
			return Err(Error::UnknownSymbol(symbol_span));
		};

		match &symbol.signature {
			// Function call
			SymbolSignature::Func(sig) => match sig {
				FuncSignature::Vector => {
					return Err(Error::IllegalVectorCall {
						defined_at: symbol.span,
						span: symbol_span,
					});
				}
				FuncSignature::Proc { .. } => ops.push(Op::FuncCall(symbol.unique_name)),
			},
			// Variable load
			SymbolSignature::Var(sig) => {
				let mut mode = IntrMode::ABS_BYTE_ADDR;
				if sig.typ.is_short() {
					mode |= IntrMode::SHORT;
				}

				ops.push(Op::AbsByteAddrOf(symbol.unique_name));
				ops.push(Op::Intrinsic(Intrinsic::Load, mode));
			}
			// Constant use
			SymbolSignature::Const(_) => {
				ops.push(Op::ConstUse(symbol.unique_name));
			}
			// Data load
			SymbolSignature::Data => {
				ops.push(Op::AbsShortAddrOf(symbol.unique_name));
				ops.push(Op::Intrinsic(Intrinsic::Load, IntrMode::ABS_SHORT_ADDR));
			}
		};

		Ok(())
	}
	fn gen_ptr_to(
		&mut self,
		name: &Name,
		symbol_span: Span,
		ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Some(symbol) = self.symbols.table.get(name) else {
			return Err(Error::UnknownSymbol(symbol_span));
		};

		let unique_name = symbol.unique_name;

		match &symbol.signature {
			SymbolSignature::Func(_) => ops.push(Op::AbsShortAddrOf(unique_name)),
			SymbolSignature::Var(_) => ops.push(Op::AbsByteAddrOf(unique_name)),
			SymbolSignature::Data => ops.push(Op::AbsShortAddrOf(unique_name)),

			SymbolSignature::Const(_) => {
				return Err(Error::IllegalPtrToConst {
					defined_at: symbol.span,
					span: symbol_span,
				});
			}
		};

		Ok(())
	}

	fn gen_def(&mut self, def: &Def, def_span: Span, level: u32) -> error::Result<()> {
		if level > 0 {
			return Err(Error::NoLocalDefsYet(def_span));
		}

		let Some(symbol) = self.symbols.table.get(def.name()) else {
			todo!("'no such symbol' iternal error");
		};
		let unique_name = symbol.unique_name;

		match def {
			Def::Func(def) => {
				let mut ops = Vec::with_capacity(64);
				self.gen_nodes(&def.body, level + 1, &mut ops)?;

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
				let var = Variable {
					size: def.typ.x.size(),
				};
				self.program.vars.insert(unique_name, var);
			}

			Def::Const(def) => {
				let mut ops = Vec::with_capacity(32);
				self.gen_nodes(&def.body, level + 1, &mut ops)?;

				let cnst = Constant { body: ops.into() };
				self.program.consts.insert(unique_name, cnst);
			}

			Def::Data(def) => {
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
						_ => return Err(Error::NoDataCodeEvaluationYet(node.span)),
					}
				}

				let data = Data { body: bytes.into() };
				self.program.datas.insert(unique_name, data);
			}
		}
		Ok(())
	}
}
