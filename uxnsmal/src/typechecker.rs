use std::{borrow::Borrow, fmt::Display, rc::Rc};

use crate::{
	ast::{Ast, Definition, Expr, FuncArgs, FuncDef, Name, Node},
	error::{self, Error, ErrorKind, ErrorStacks, HintKind},
	lexer::{Span, Spanned},
	program::{
		AddrKind, Constant, Data, Function, Intrinsic, IntrinsicMode, Op, Program, Variable,
	},
	symbols::{
		ConstSignature, DataSignature, FuncSignature, Label, Symbol, SymbolsTable, VarSignature,
	},
};

/// Expected stack height
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackMatch {
	Exact,
	Tail,
}

/// Value type kind
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
	Byte,
	Short,
	BytePtr(Box<Type>),
	ShortPtr(Box<Type>),
	/// Pointer to a vector or proc function
	/// Always a short pointer
	FuncPtr(FuncSignature),
}
impl Type {
	/// Size of the type in bytes
	pub fn size(&self) -> u8 {
		match self {
			Self::Byte => 1,
			Self::Short => 2,
			Self::BytePtr(_) => 1,
			Self::ShortPtr(_) => 2,
			Self::FuncPtr(_) => 2,
		}
	}
}
impl Display for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Byte => write!(f, "byte"),
			Self::Short => write!(f, "short"),
			Self::BytePtr(t) => write!(f, "ptr {t}"),
			Self::ShortPtr(t) => write!(f, "ptr2 {t}"),
			Self::FuncPtr(t) => write!(f, "funptr{t}"),
		}
	}
}

/// Unique name of a symbol
/// Guaranteed to be an existant symbol name
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniqueName(pub Rc<str>);
impl AsRef<str> for UniqueName {
	fn as_ref(&self) -> &str {
		&self.0
	}
}
impl Borrow<str> for UniqueName {
	fn borrow(&self) -> &str {
		&self.0
	}
}

/// Stack item
#[derive(Debug, Clone, Eq)]
pub struct StackItem {
	pub typ: Type,
	pub name: Option<Name>,
	pub span: Span,
}
impl StackItem {
	pub fn new(typ: Type, span: Span) -> Self {
		Self {
			typ,
			name: None,
			span,
		}
	}
}
impl From<StackItem> for (Option<Name>, Type) {
	fn from(value: StackItem) -> Self {
		(value.name, value.typ)
	}
}
impl From<StackItem> for Type {
	fn from(value: StackItem) -> Self {
		value.typ
	}
}
impl From<(Type, Span)> for StackItem {
	fn from(value: (Type, Span)) -> Self {
		Self::new(value.0, value.1)
	}
}
impl From<Spanned<Type>> for StackItem {
	fn from(value: Spanned<Type>) -> Self {
		Self::new(value.x, value.span)
	}
}
impl Borrow<Type> for StackItem {
	fn borrow(&self) -> &Type {
		&self.typ
	}
}
impl PartialEq for StackItem {
	fn eq(&self, other: &Self) -> bool {
		self.typ == other.typ && self.name == other.name
	}
}

/// Stack
#[derive(Debug, Clone)]
pub struct Stack {
	pub items: Vec<StackItem>,
	/// List of consumed items
	/// `Spanned(original_item, consumed_at)`
	pub consumed: Vec<Spanned<StackItem>>,
	/// Snapshots of the stack taken at each block start
	pub snapshots: Vec<Vec<StackItem>>,

	/// Index of an item from the end of the stack that will
	/// be popped (cloned actually) next in keep mode
	/// `0` means the topmost/last item
	keep_cursor: usize,
}
impl Default for Stack {
	fn default() -> Self {
		Self {
			items: Vec::with_capacity(256),
			consumed: Vec::with_capacity(256),
			snapshots: Vec::with_capacity(16),

			keep_cursor: 0,
		}
	}
}
impl Stack {
	/// Push a type onto the stack
	pub fn push(&mut self, item: impl Into<StackItem>) {
		let item: StackItem = item.into();
		self.keep_cursor = 0;
		self.items.push(item);
	}
	/// Pop a type from the stack if any
	pub fn pop(&mut self, span: Span, keep: bool) -> Option<StackItem> {
		let item = if keep {
			let idx = self.items.len() - self.keep_cursor - 1;
			self.keep_cursor += 1;
			self.items.get(idx)?.clone()
		} else {
			self.keep_cursor = 0;
			self.items.pop()?
		};

		let consumed = item.clone();
		self.consumed.push(Spanned::new(consumed, span));

		Some(item)
	}
	/// Take a snapshot of the current stack signature
	pub fn snapshot(&mut self) {
		self.snapshots.push(self.items.clone());
	}

	/// Compare an iterator of types with the top of the working stack
	pub fn compare<T, I>(&mut self, mtch: StackMatch, expect: I, span: Span) -> error::Result<()>
	where
		T: Borrow<Type>,
		I: IntoIterator<Item = T>,
		I::IntoIter: DoubleEndedIterator + Clone,
	{
		let expect = expect.into_iter();
		let expect_len = expect.size_hint().1.unwrap_or(0);

		let mut is_ok = match mtch {
			StackMatch::Exact => expect_len == self.len(),
			StackMatch::Tail => true,
		};

		// Remember the tail of the working stack signature before consuming
		// the items for comparison
		let start = self.len().saturating_sub(expect_len);
		let prev = self.items[start..].to_owned();

		if is_ok {
			for expect_typ in expect.clone().rev() {
				let Some(item) = self.pop(span, false) else {
					is_ok = false;
					break;
				};

				if item.typ != *expect_typ.borrow() {
					is_ok = false;
					break;
				}

				is_ok = true;
			}
		}

		if is_ok {
			Ok(())
		} else {
			// Restore the previous tail signature of the working stack
			self.items.truncate(start);
			self.items.extend(prev);

			Err(self.error_invalid_stack(
				ErrorKind::InvalidStackSignature,
				mtch,
				expect.map(|t| t.borrow().clone()),
				span,
			))
		}
	}

	pub fn reset(&mut self) {
		self.keep_cursor = 0;
		self.items.clear();
		self.consumed.clear();
	}

	pub fn topmost(&self) -> Option<&StackItem> {
		self.items.last()
	}
	pub fn len(&self) -> usize {
		self.items.len()
	}

	fn error_invalid_stack<T, I>(
		&mut self,
		kind: ErrorKind,
		mtch: StackMatch,
		expected: I,
		span: Span,
	) -> Error
	where
		T: Into<Type>,
		I: IntoIterator<Item = T>,
	{
		let expected = expected.into_iter();
		let mut error = kind.err(span);

		let exp_len = expected.size_hint().1.unwrap_or(0);

		// diff < 0 - underflow
		// diff > 0 - overflow
		// diff == 0 - equal
		let diff: i32 = self.len() as i32 - exp_len as i32;

		let found = match mtch {
			StackMatch::Exact => &self.items,
			StackMatch::Tail if diff < 0 => &self.items,
			StackMatch::Tail => &self.items[self.len() - exp_len..],
		};
		let found = found.iter().map(|t| t.typ.clone().into()).collect();

		if diff > 0 && mtch == StackMatch::Exact {
			// Collect hints to ops that caused the overflow
			for _ in 0..diff {
				let Some(item) = self.items.pop() else {
					break;
				};
				error.hints.push(HintKind::CausedBy, item.span);
			}
		} else if diff < 0 {
			// Collect hints to ops that consumed values and caused the underflow
			let mut n = diff.abs();
			while n > 0 {
				let Some(consumed) = self.consumed.pop() else {
					break;
				};
				if consumed.span == span {
					continue;
				}

				error.hints.push(HintKind::ConsumedHere, consumed.span);
				n -= 1;
			}
		}

		let expected_list: Vec<Type> = expected.map(|t| t.into()).collect();

		for typ in expected_list.iter().rev() {
			if let Some(item) = self.items.pop() {
				if item.typ == *typ {
					continue;
				}

				error.hints.push(
					HintKind::ExpectedType {
						expected: typ.clone(),
						found: item.typ,
					},
					item.span,
				);
			}
		}

		error.stacks = Some(ErrorStacks {
			expected: expected_list,
			found,
			mtch,
		});

		error
	}
	fn error_intr_invalid_stack(&mut self, a: &StackItem, b: &StackItem, span: Span) -> Error {
		let mut error = ErrorKind::IntrinsicInvalidStackSignature.err(span);

		let hint = HintKind::BecauseOfType { typ: b.typ.clone() };
		error.hints.push(hint, b.span);

		let hint = HintKind::ExpectedType {
			expected: b.typ.clone(),
			found: a.typ.clone(),
		};
		error.hints.push(hint, a.span);

		error
	}
	fn error_underflow(&mut self, expected_len: usize, span: Span) -> Error {
		let kind = ErrorKind::IntrinsicInvalidStackHeight {
			expected: expected_len,
			found: self.len(),
		};
		let mut error = kind.err(span);
		let n = expected_len - self.len();

		for _ in 0..n {
			let Some(consumed) = self.consumed.pop() else {
				break;
			};
			if consumed.span == span {
				continue;
			}

			error.hints.push(HintKind::ConsumedHere, consumed.span);
		}

		error
	}
}

/// Current node scope
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Scope {
	Toplevel,
	Block(usize),
}

/// AST typechecker
///
/// Type checks the specified AST and builds an intermediate representation
#[derive(Debug, Default)]
pub struct Typechecker {
	program: Program,
	symbols: SymbolsTable,

	/// Working stack
	stack: Stack,

	unique_name_idx: usize,
}
impl Typechecker {
	pub fn check(ast: Ast) -> error::Result<Program> {
		Self::default().do_check(ast)
	}

	fn do_check(mut self, ast: Ast) -> error::Result<Program> {
		self.collect(&ast)?;
		self.check_nodes(&ast.nodes, Scope::Toplevel, &mut vec![])?;
		Ok(self.program)
	}

	/// Collect symbols
	fn collect(&mut self, ast: &Ast) -> error::Result<()> {
		for node in ast.nodes.iter() {
			let (name, signature): (Name, Symbol) = match &node.x {
				Node::Expr(_) => continue,

				Node::Def(Definition::Func(def)) => {
					let unique_name = self.new_unique_name(&def.name);
					let sig = def.args.to_signature();
					(def.name.clone(), Symbol::Function(unique_name, sig))
				}
				Node::Def(Definition::Var(def)) => {
					let unique_name = self.new_unique_name(&def.name);
					let sig = VarSignature {
						typ: def.typ.x.clone(),
					};
					(def.name.clone(), Symbol::Variable(unique_name, sig))
				}
				Node::Def(Definition::Const(def)) => {
					let unique_name = self.new_unique_name(&def.name);
					let sig = ConstSignature {
						typ: def.typ.x.clone(),
					};
					(def.name.clone(), Symbol::Constant(unique_name, sig))
				}
				Node::Def(Definition::Data(def)) => {
					let unique_name = self.new_unique_name(&def.name);
					(def.name.clone(), Symbol::Data(unique_name, DataSignature))
				}
			};

			self.symbols.define(name.clone(), signature, node.span)?;
		}

		Ok(())
	}

	fn check_nodes(
		&mut self,
		nodes: &[Spanned<Node>],
		scope: Scope,
		body_ops: &mut Vec<Op>,
	) -> error::Result<()> {
		for node in nodes.iter() {
			match &node.x {
				Node::Expr(expr) => self.check_expression(expr, node.span, scope, body_ops)?,
				Node::Def(def) => self.check_definition(def, node.span, scope)?,
			}
		}

		Ok(())
	}

	fn check_definition(
		&mut self,
		def: &Definition,
		def_span: Span,
		scope: Scope,
	) -> error::Result<()> {
		if scope != Scope::Toplevel {
			return Err(ErrorKind::NoLocalDefsYet.err(def_span));
		}

		match def {
			Definition::Func(def) => {
				self.reset();
				let func = self.check_func(def, def_span)?;
				let unique_name = self.symbols.get(&def.name).unwrap().x.unique_name();

				if def.name.as_ref() == "on-reset" {
					if func.is_vector {
						self.program.reset_func = Some((unique_name.clone(), func));
					} else {
						return Err(ErrorKind::ResetFuncIsNotVector.err(def_span));
					}
				} else {
					self.program.funcs.insert(unique_name.clone(), func);
				}
			}

			Definition::Var(def) => {
				let var = Variable {
					size: def.typ.x.size(),
				};
				let unique_name = self.symbols.get(&def.name).unwrap().x.unique_name();
				self.program.vars.insert(unique_name.clone(), var);
			}

			Definition::Const(def) => {
				self.reset();

				let mut body_ops = Vec::<Op>::with_capacity(128);
				self.check_nodes(&def.body, Scope::Block(0), &mut body_ops)?;

				let res = self
					.stack
					.compare(StackMatch::Exact, [&def.typ.x], def_span);
				if let Err(mut err) = res {
					err.hints.push(HintKind::BecauseOf, def.typ.span);
					return Err(err);
				}

				let cnst = Constant {
					body: body_ops.into_boxed_slice(),
				};
				let unique_name = self.symbols.get(&def.name).unwrap().x.unique_name();
				self.program.consts.insert(unique_name.clone(), cnst);
			}

			Definition::Data(def) => {
				self.reset();
				let mut body = Vec::with_capacity(128);

				for node in def.body.iter() {
					match &node.x {
						Node::Expr(Expr::Byte(b)) => body.push(*b),
						Node::Expr(Expr::Short(s)) => {
							let a = ((s & 0xFF00) >> 8) as u8;
							let b = (s & 0x00FF) as u8;
							body.push(a);
							body.push(b);
						}
						Node::Expr(Expr::Padding(p)) => {
							for _ in 0..*p {
								body.push(0)
							}
						}
						Node::Expr(Expr::String(s)) => {
							body.extend(s.as_bytes());
						}

						_ => {
							let mut err = ErrorKind::IllegalExprInData.err(def_span);
							err.hints.push(HintKind::CausedBy, node.span);
							return Err(err);
						}
					}
				}

				let data = Data {
					body: body.into_boxed_slice(),
				};
				let unique_name = self.symbols.get(&def.name).unwrap().x.unique_name();
				self.program.datas.insert(unique_name.clone(), data);
			}
		}

		Ok(())
	}
	fn check_expression(
		&mut self,
		expr: &Expr,
		expr_span: Span,
		scope: Scope,
		body_ops: &mut Vec<Op>,
	) -> error::Result<()> {
		let Scope::Block(block_depth) = scope else {
			return Err(ErrorKind::IllegalExprInToplevel.err(expr_span));
		};

		let ops: &[Op] = match expr {
			Expr::Byte(b) => {
				self.stack.push((Type::Byte, expr_span));
				&[Op::Byte(*b)]
			}
			Expr::Short(s) => {
				self.stack.push((Type::Short, expr_span));
				&[Op::Short(*s)]
			}
			Expr::String(s) => {
				self.stack
					.push((Type::ShortPtr(Box::new(Type::Byte)), expr_span));

				let data = Data {
					body: s.clone().into_boxed_bytes(),
				};

				// Do not store the same string twice
				let res = self.program.datas.iter().find(|(_, v)| **v == data);
				let unique_name = match res {
					Some((name, _)) => name.clone(),
					None => {
						let name = self.new_unique_name("string");
						self.program.datas.insert(name.clone(), data);
						name
					}
				};

				&[Op::ShortAddrOf(unique_name)]
			}
			Expr::Padding(p) => &[Op::Padding(*p)],

			Expr::Intrinsic(intr, mode) => {
				let (intr, mode) = self.check_intrinsic(*intr, *mode, expr_span)?;
				&[Op::Intrinsic(intr, mode)]
			}
			Expr::Symbol(name) => {
				if let Some(symbol) = self.symbols.get(name) {
					match &symbol.x {
						Symbol::Function(unique_name, func) => match func {
							FuncSignature::Vector => {
								// Unfortunately you can't call vector functions
								return Err(ErrorKind::IllegalVectorCall.err(expr_span));
							}
							FuncSignature::Proc { inputs, outputs } => {
								match self.stack.compare(StackMatch::Tail, inputs, expr_span) {
									Ok(()) => (),
									Err(mut err) => match err.kind {
										ErrorKind::InvalidStackSignature => {
											err.hints.push(HintKind::DefinedHere, symbol.span);
											return Err(err);
										}
										_ => return Err(err),
									},
								}
								for typ in outputs.iter() {
									self.stack.push((typ.clone(), expr_span));
								}

								&[Op::Call(unique_name.clone())]
							}
						},

						Symbol::Variable(unique_name, var) => {
							let mode = if var.typ.size() == 2 {
								IntrinsicMode::SHORT
							} else {
								IntrinsicMode::NONE
							};

							self.stack.push((var.typ.clone(), expr_span));

							&[
								Op::ByteAddrOf(unique_name.clone()),
								Op::Intrinsic(Intrinsic::Load(AddrKind::AbsByte), mode),
							]
						}

						Symbol::Constant(unique_name, cnst) => {
							self.stack.push((cnst.typ.clone(), expr_span));
							&[Op::ConstUse(unique_name.clone())]
						}

						Symbol::Data(unique_name, _) => {
							self.stack.push((Type::Byte, expr_span));
							&[
								Op::ShortAddrOf(unique_name.clone()),
								Op::Intrinsic(
									Intrinsic::Load(AddrKind::AbsShort),
									IntrinsicMode::NONE,
								),
							]
						}
					}
				} else {
					match self.stack.topmost() {
						Some(item) => match &item.name {
							Some(item_name) if *item_name == *name => &[/* nothing */],
							_ => return Err(ErrorKind::UnknownSymbol.err(expr_span)),
						},
						None => return Err(ErrorKind::UnknownSymbol.err(expr_span)),
					}
				}
			}
			Expr::PtrTo(name) => {
				let Some(symbol) = self.symbols.get(name) else {
					return Err(ErrorKind::UnknownSymbol.err(expr_span));
				};

				match &symbol.x {
					Symbol::Function(unique_name, func) => {
						self.stack.push((Type::FuncPtr(func.clone()), expr_span));
						&[Op::ShortAddrOf(unique_name.clone())]
					}

					Symbol::Variable(unique_name, var) => {
						self.stack
							.push((Type::BytePtr(Box::new(var.typ.clone())), expr_span));
						&[Op::ByteAddrOf(unique_name.clone())]
					}

					Symbol::Data(unique_name, _) => {
						self.stack
							.push((Type::ShortPtr(Box::new(Type::Byte)), expr_span));
						&[Op::ShortAddrOf(unique_name.clone())]
					}

					Symbol::Constant(_, _) => {
						return Err(ErrorKind::IllegalConstantPtr.err(expr_span));
					}
				}
			}

			Expr::Jump { label, conditional } => {
				if block_depth == 0 {
					return Err(ErrorKind::JumpNotInBlock.err(expr_span));
				}

				if *conditional {
					let Some(item) = self.stack.pop(expr_span, false) else {
						return Err(self.stack.error_underflow(1, expr_span));
					};
					self.check_item(&item, Type::Byte, expr_span)?;
				}

				let Some(block_label) = self.symbols.labels.get(&label.x) else {
					return Err(ErrorKind::UnknownLabel.err(label.span));
				};

				let expect_stack = &self.stack.snapshots[block_label.depth];
				if *expect_stack != self.stack.items {
					return Err(self.stack.error_invalid_stack(
						ErrorKind::MismatchedBlockStack,
						StackMatch::Exact,
						expect_stack.clone(),
						expr_span,
					));
				}

				if *conditional {
					&[Op::JumpIf(block_label.unique_name.clone())]
				} else {
					&[Op::Jump(block_label.unique_name.clone())]
				}
			}
			Expr::Block {
				looping,
				label,
				body: block_body,
			} => {
				self.stack.snapshot();

				let label_unique_name = self.new_unique_name(&label.x);
				let prev_label = self.symbols.labels.insert(
					label.x.clone(),
					Label {
						unique_name: label_unique_name.clone(),
						depth: block_depth,
						span: label.span,
					},
				);

				if let Some(prev_label) = prev_label {
					let mut err = ErrorKind::LabelRedefinition.err(label.span);
					err.hints.push(HintKind::DefinedHere, prev_label.span);
					return Err(err);
				}

				let mut repeat_label: Option<UniqueName> = None;
				if *looping {
					let unique_name = self.new_unique_name("loop-repeat");
					repeat_label = Some(unique_name.clone());
					body_ops.push(Op::Label(unique_name));
				}

				self.check_nodes(block_body, Scope::Block(block_depth + 1), body_ops)?;

				let expect_stack = self.stack.snapshots.pop().unwrap();
				if *expect_stack != self.stack.items {
					return Err(self.stack.error_invalid_stack(
						ErrorKind::MismatchedBlockStack,
						StackMatch::Exact,
						expect_stack,
						expr_span,
					));
				}

				self.symbols.labels.remove(&label.x);

				if let Some(repeat_label) = repeat_label {
					&[Op::Jump(repeat_label), Op::Label(label_unique_name)]
				} else {
					&[Op::Label(label_unique_name)]
				}
			}
			Expr::If { body } => {
				let Some(item) = self.stack.pop(expr_span, false) else {
					return Err(self.stack.error_underflow(1, expr_span));
				};
				self.check_item(&item, Type::Byte, expr_span)?;

				self.stack.snapshot();

				let skip_label = self.new_unique_name("if-skip");
				let continue_label = self.new_unique_name("if-continue");

				body_ops.extend([
					Op::JumpIf(continue_label.clone()),
					Op::Jump(skip_label.clone()),
					Op::Label(continue_label),
				]);

				self.check_nodes(body, Scope::Block(block_depth + 1), body_ops)?;

				// TODO: move this into a separate method
				let expect_stack = self.stack.snapshots.pop().unwrap();
				if *expect_stack != self.stack.items {
					return Err(self.stack.error_invalid_stack(
						ErrorKind::MismatchedBlockStack,
						StackMatch::Exact,
						expect_stack,
						expr_span,
					));
				}

				&[Op::Label(skip_label)]
			}

			Expr::Bind(names) => {
				let len = names.len();
				if len > self.stack.len() {
					return Err(self.stack.error_underflow(len, expr_span));
				}

				for (idx, name) in names.iter().enumerate() {
					self.symbols.ensure_not_exists(&name.x, name.span)?;

					let ws_len = self.stack.len();
					let item = &mut self.stack.items[ws_len - len + idx];
					item.name = Some(name.x.clone());
				}

				&[/* nothing */]
			}
		};

		body_ops.extend(ops.iter().cloned());

		Ok(())
	}

	fn check_func(&mut self, func: &FuncDef, span: Span) -> error::Result<Function> {
		match &func.args {
			FuncArgs::Vector => (),
			FuncArgs::Proc { inputs, .. } => {
				// Push proc function input types onto the stack
				for input in inputs.iter() {
					self.stack.push(input.clone());
				}
			}
		}

		let mut body_ops = Vec::<Op>::with_capacity(128);
		self.check_nodes(&func.body, Scope::Block(0), &mut body_ops)?;

		// Expect stack to be equal to function outputs
		match &func.args {
			FuncArgs::Vector => {
				self.stack
					.compare::<StackItem, _>(StackMatch::Exact, [], span)?;
			}
			FuncArgs::Proc { outputs, .. } => {
				self.stack
					.compare(StackMatch::Exact, outputs.iter().map(|t| &t.x), span)?;
			}
		}

		Ok(Function {
			is_vector: matches!(func.args, FuncArgs::Vector),
			body: body_ops.into_boxed_slice(),
		})
	}

	// TODO: this method is a mess i think, need to refactor it.
	// make intrinsic checks use less unique code and move +- repeating
	// parts into separate methods
	fn check_intrinsic(
		&mut self,
		mut intr: Intrinsic,
		mut mode: IntrinsicMode,
		span: Span,
	) -> error::Result<(Intrinsic, IntrinsicMode)> {
		let keep = mode.contains(IntrinsicMode::KEEP);

		macro_rules! new {
			($from:expr) => {
				StackItem { span, ..$from }
			};
		}
		macro_rules! intrinsic {
			($n_inputs:expr, $($input:ident),+$(,)? => $($output:expr),*$(,)?) => {{
				$(let $input = self.stack.pop(span, keep);)+

				let ($(Some($input), )+) = ($($input, )+) else {
					return Err(self.stack.error_underflow($n_inputs, span));
				};

				// Check whether all the inputs are 1 byte size
				// or all inputs are 2 bytes size
				let is_bytes = true $(&& $input.typ.size() == 1)+;
				let is_shorts = true $(&& $input.typ.size() == 2)+;
				if !is_bytes && !is_shorts {
					let mut err = ErrorKind::IntrinsicInvalidStackSignature.err(span);
					$(err.hints.push(HintKind::SizeIs { size: $input.typ.size() }, $input.span);)+
					return Err(err);
				}

				// Update intrinsic mode based on its inputs
				if is_shorts {
					mode |= IntrinsicMode::SHORT;
				}

				$(self.stack.push($output);)*
			}};
		}

		#[allow(unused_variables)]
		match intr {
			Intrinsic::Add | Intrinsic::Sub | Intrinsic::Mul | Intrinsic::Div => {
				let b = self.stack.pop(span, keep);
				let a = self.stack.pop(span, keep);

				let (Some(a), Some(b)) = (a, b) else {
					return Err(self.stack.error_underflow(2, span));
				};

				// All the allowed signatures
				let output = match (&a.typ, &b.typ) {
					(Type::Byte, Type::Byte) => Type::Byte,
					(Type::Short, Type::Short) => Type::Short,
					(Type::Byte, Type::BytePtr(t)) => Type::BytePtr(t.clone()),
					(Type::Short, Type::ShortPtr(t)) => Type::ShortPtr(t.clone()),
					(Type::Short, Type::FuncPtr(f)) => Type::FuncPtr(f.clone()),
					(Type::BytePtr(t), Type::Byte) => Type::BytePtr(t.clone()),
					(Type::ShortPtr(t), Type::Short) => Type::ShortPtr(t.clone()),
					(Type::FuncPtr(f), Type::Short) => Type::FuncPtr(f.clone()),
					(Type::BytePtr(a), Type::BytePtr(b)) if a == b => Type::BytePtr(a.clone()),
					(Type::ShortPtr(a), Type::ShortPtr(b)) if a == b => Type::ShortPtr(a.clone()),
					(Type::FuncPtr(a), Type::FuncPtr(b)) if a == b => Type::FuncPtr(a.clone()),
					_ => {
						let mut err = ErrorKind::IntrinsicInvalidStackSignature.err(span);

						let hint = HintKind::BecauseOfType { typ: b.typ.clone() };
						err.hints.push(hint, b.span);

						let hint = match &b.typ {
							Type::Byte => HintKind::ExpectedAnyByte { found: a.typ },
							Type::Short => HintKind::ExpectedAnyShort { found: a.typ },
							Type::BytePtr(t) => HintKind::ExpectedAnyBytePtr {
								inner: *t.clone(),
								found: a.typ,
							},
							Type::ShortPtr(t) => HintKind::ExpectedAnyShortPtr {
								inner: *t.clone(),
								found: a.typ,
							},
							Type::FuncPtr(t) => HintKind::ExpectedAnyShortFuncPtr {
								inner: t.clone(),
								found: a.typ,
							},
						};
						err.hints.push(hint, a.span);

						return Err(err);
					}
				};

				if output.size() == 2 {
					mode |= IntrinsicMode::SHORT;
				}

				self.stack.push((output, span));
			}
			Intrinsic::Inc => intrinsic! { 1, a => new!(a) },
			Intrinsic::Shift => {
				let shift = self.stack.pop(span, keep);
				let a = self.stack.pop(span, keep);

				let (Some(a), Some(shift)) = (a, shift) else {
					return Err(self.stack.error_underflow(2, span));
				};

				if shift.typ != Type::Byte {
					let mut err = ErrorKind::IntrinsicInvalidStackSignature.err(span);
					let hint = HintKind::ExpectedType {
						expected: Type::Byte,
						found: shift.typ.clone(),
					};
					err.hints.push(hint, shift.span);
					return Err(err);
				}

				self.stack.push(new!(a));
			}

			Intrinsic::And | Intrinsic::Or | Intrinsic::Xor => {
				let b = self.stack.pop(span, keep);
				let a = self.stack.pop(span, keep);

				let (Some(a), Some(b)) = (a, b) else {
					return Err(self.stack.error_underflow(2, span));
				};

				match (&a.typ, &b.typ) {
					(Type::Byte, Type::Byte) => self.stack.push((Type::Byte, span)),
					(Type::Short, Type::Short) => self.stack.push((Type::Short, span)),
					_ => return Err(self.stack.error_intr_invalid_stack(&a, &b, span)),
				}
			}

			Intrinsic::Eq | Intrinsic::Neq | Intrinsic::Gth | Intrinsic::Lth => {
				intrinsic! { 2, b, a => (Type::Byte, span) }
			}
			Intrinsic::Pop => intrinsic! { 1, a => },
			Intrinsic::Swap => intrinsic! { 2, b, a => b, a },
			Intrinsic::Nip => intrinsic! { 2, b, a => b },
			Intrinsic::Rot => intrinsic! { 3, c, b, a => b, c, a },
			Intrinsic::Dup => intrinsic! { 1, a => a.clone(), new!(a) },
			Intrinsic::Over => intrinsic! { 2, b, a => a.clone(), b, new!(a), },

			Intrinsic::Load(kind) => {
				let Some(a) = self.stack.pop(span, keep) else {
					return Err(self.stack.error_underflow(1, span));
				};

				let (output, addr) = match a.typ {
					Type::BytePtr(typ) => (*typ, AddrKind::AbsByte),
					Type::ShortPtr(typ) => (*typ, AddrKind::AbsShort),
					_ => {
						let mut err = ErrorKind::IntrinsicInvalidStackSignature.err(span);
						let hint = HintKind::ExpectedAnyPtr {
							found: a.typ.clone(),
						};
						err.hints.push(hint, a.span);
						return Err(err);
					}
				};

				if output.size() == 2 {
					mode |= IntrinsicMode::SHORT;
				}

				intr = Intrinsic::Load(addr);
				self.stack.push((output, span));
			}
			Intrinsic::Store(kind) => {
				let ptr = self.stack.pop(span, keep);
				let val = self.stack.pop(span, keep);

				let (Some(val), Some(ptr)) = (val, ptr) else {
					return Err(self.stack.error_underflow(2, span));
				};

				let (expect, addr) = match &ptr.typ {
					Type::BytePtr(typ) => (typ, AddrKind::AbsByte),
					Type::ShortPtr(typ) => (typ, AddrKind::AbsShort),
					_ => {
						let mut err = ErrorKind::IntrinsicInvalidStackSignature.err(span);
						let hint = HintKind::ExpectedAnyPtr {
							found: ptr.typ.clone(),
						};
						err.hints.push(hint, ptr.span);
						return Err(err);
					}
				};
				intr = Intrinsic::Store(addr);

				if **expect != val.typ {
					let mut err = ErrorKind::IntrinsicInvalidStackSignature.err(span);
					err.hints.push(
						HintKind::BecauseOfType {
							typ: ptr.typ.clone(),
						},
						ptr.span,
					);

					let hint = HintKind::ExpectedType {
						expected: *expect.clone(),
						found: val.typ.clone(),
					};
					err.hints.push(hint, val.span);

					return Err(err);
				}
				if expect.size() == 2 {
					mode |= IntrinsicMode::SHORT;
				}
			}

			Intrinsic::Input | Intrinsic::Input2 => {
				let Some(dev) = self.stack.pop(span, keep) else {
					return Err(self.stack.error_underflow(1, span));
				};

				self.check_item(&dev, Type::Byte, span)?;

				match intr {
					Intrinsic::Input => self.stack.push((Type::Byte, span)),
					Intrinsic::Input2 => {
						mode |= IntrinsicMode::SHORT;
						self.stack.push((Type::Short, span))
					}
					_ => unreachable!(),
				}
			}
			Intrinsic::Output => {
				let dev = self.stack.pop(span, keep);
				let val = self.stack.pop(span, keep);

				let (Some(val), Some(dev)) = (val, dev) else {
					return Err(self.stack.error_underflow(2, span));
				};

				self.check_item(&dev, Type::Byte, span)?;
				if val.typ.size() == 2 {
					mode |= IntrinsicMode::SHORT;
				}
			}
		}

		self.stack.keep_cursor = 0;
		Ok((intr, mode))
	}

	fn check_item(&mut self, item: &StackItem, expect: Type, span: Span) -> error::Result<()> {
		if item.typ == expect {
			Ok(())
		} else {
			let mut error = ErrorKind::IntrinsicInvalidStackSignature.err(span);

			let hint = HintKind::ExpectedType {
				expected: expect,
				found: item.typ.clone(),
			};
			error.hints.push(hint, item.span);

			Err(error)
		}
	}

	/// Reset all stacks
	pub fn reset(&mut self) {
		self.stack.reset();
	}

	fn new_unique_name(&mut self, prefix: impl Display) -> UniqueName {
		let unique = UniqueName(format!("{prefix}_{}", self.unique_name_idx).into());
		self.unique_name_idx += 1;
		unique
	}
}
