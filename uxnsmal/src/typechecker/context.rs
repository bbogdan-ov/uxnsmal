use crate::bug;
use crate::error::{self, Error, SymbolError};
use crate::lexer::Span;
use crate::program::Ops;
use crate::symbols::{Name, SymbolsTable, Type, UniqueName};
use crate::typechecker::{Stack, StackItem, StackMatch, empty_stack};
use std::borrow::Borrow;
use std::collections::HashMap;

/// Working and return stacks snapshot
#[derive(Debug, Default, Clone)]
pub struct Snapshot {
	pub ws: Vec<StackItem>,
	pub rs: Vec<StackItem>,
}
impl Snapshot {
	pub fn new(ws: Vec<StackItem>, rs: Vec<StackItem>) -> Self {
		Self { ws, rs }
	}
}

/// Block state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockState {
	Normal,
	/// Branching blocks are blocks that can exit early
	Branching,
	/// Following operations in this block will never be executed
	Finished,
}

/// Block propagate
#[derive(Debug, Clone, Copy)]
pub struct Propagate {
	pub state: BlockState,
	pub target_idx: usize,
	pub from: Span,
}
impl Propagate {
	pub fn new(state: BlockState, target_idx: usize, from: Span) -> Self {
		Self {
			state,
			target_idx,
			from,
		}
	}
}

/// Block
#[derive(Debug)]
pub struct Block {
	pub index: usize,
	pub state: BlockState,
	pub propagate: Option<Propagate>,
	/// Stacks before this block
	pub snapshot: Snapshot,
}
impl Block {
	pub fn new(ctx: &Context, parenting: &Block, branching: bool) -> Self {
		Self::new_with(parenting, branching, ctx.take_snapshot())
	}
	pub fn new_with(parenting: &Block, branching: bool, snapshot: Snapshot) -> Self {
		Self {
			index: parenting.index + 1,
			state: if branching {
				BlockState::Branching
			} else {
				BlockState::Normal
			},
			propagate: None,
			snapshot,
		}
	}
	pub fn new_root(ctx: &Context) -> Self {
		Self {
			index: 0,
			state: BlockState::Normal,
			propagate: None,
			snapshot: ctx.take_snapshot(),
		}
	}

	pub fn finish(&mut self, ctx: &mut Context) {
		if self.state == BlockState::Branching {
			// Restore previous state of the stacks for branching blocks to pretend that
			// this block has never been executed.
			// Because it indeed may not execute, that's why it is a "branching" block.
			ctx.apply_snapshot(self.snapshot.clone());
		}

		self.state = BlockState::Finished;
	}
	pub fn compare(&mut self, ctx: &mut Context, span: Span) -> error::Result<()> {
		if self.state == BlockState::Branching {
			let span = match self.propagate {
				Some(p) => p.from,
				None => span,
			};
			ctx.compare_snapshot(&self.snapshot, span)?;
		}
		Ok(())
	}
	pub fn end(mut self, ctx: &mut Context, block: &mut Block, span: Span) -> error::Result<()> {
		self.compare(ctx, span)?;

		if let Some(p) = self.propagate {
			if self.index == 0 {
				bug!("root/definition block cannot propagate state any lower {p:?}");
			}

			block.propagate(p.state, p.target_idx, p.from);
		}

		self.finish(ctx);
		Ok(())
	}

	pub fn propagate(&mut self, state: BlockState, target_idx: usize, span: Span) {
		self.state = state;
		if self.index != target_idx {
			self.propagate = Some(Propagate::new(state, target_idx, span));
		} else {
			self.propagate = None;
		}
	}
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
#[derive(Debug, Default)]
pub struct Context {
	/// Working stack
	pub ws: Stack,
	/// Return stack
	pub rs: Stack,

	pub ops: Ops,

	/// Table of labels accessible in the current scope/block.
	/// It is a separate table from symbols because labels have a separate namespace.
	pub labels: HashMap<Name, Label>,
}
impl Context {
	/// Compare outputing stack at the end of a definition
	pub fn compare_def_stacks<'t, T, I>(&mut self, ws: I, span: Span) -> error::Result<()>
	where
		T: Borrow<Type> + 't,
		I: Iterator<Item = &'t T> + ExactSizeIterator + DoubleEndedIterator + Clone,
	{
		let rs = empty_stack();
		self.ws.consumer_keep(span).compare(ws, StackMatch::Exact)?;
		self.rs.consumer_keep(span).compare(rs, StackMatch::Exact)?;
		Ok(())
	}

	pub fn take_snapshot(&self) -> Snapshot {
		Snapshot::new(self.ws.items.clone(), self.rs.items.clone())
	}
	pub fn apply_snapshot(&mut self, snapshot: Snapshot) {
		self.ws.items = snapshot.ws;
		self.rs.items = snapshot.rs;
	}
	pub fn compare_snapshot(&mut self, snapshot: &Snapshot, span: Span) -> error::Result<()> {
		let mut ws_consumer = self.ws.consumer_keep(span);
		ws_consumer.compare(snapshot.ws.iter(), StackMatch::Exact)?;
		ws_consumer.compare_names(snapshot.ws.iter().map(|t| t.name.as_ref()))?;

		let mut rs_consumer = self.rs.consumer_keep(span);
		rs_consumer.compare(snapshot.rs.iter(), StackMatch::Exact)?;
		rs_consumer.compare_names(snapshot.rs.iter().map(|t| t.name.as_ref()))?;

		Ok(())
	}

	pub fn define_label(
		&mut self,
		name: Name,
		block_idx: usize,
		symbols: &mut SymbolsTable,
		span: Span,
	) -> error::Result<UniqueName> {
		let unique_name = symbols.new_unique_name();
		let label = Label::new(unique_name, block_idx, span);
		let prev = self.labels.insert(name, label);
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
	pub fn undefine_label(&mut self, name: &Name) {
		let prev = self.labels.remove(name);
		if prev.is_none() {
			bug!("unexpected non-existing label {name:?}");
		}
	}
}
