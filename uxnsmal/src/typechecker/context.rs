use crate::error;
use crate::lexer::Span;
use crate::program::Op;
use crate::symbols::{Name, UniqueName};
use crate::typechecker::{Stack, StackItem, StackMatch};
use std::collections::HashMap;
use std::num::NonZeroUsize;

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
	pub depth: NonZeroUsize,
	pub from: Span,
}
impl Propagate {
	pub fn new(state: BlockState, depth: usize, from: Span) -> Option<Self> {
		Some(Self {
			state,
			depth: NonZeroUsize::new(depth)?,
			from,
		})
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
			block.propagate(p.state, p.depth.get() - 1, p.from);
		}

		self.finish(ctx);
		Ok(())
	}

	pub fn propagate(&mut self, state: BlockState, depth: usize, span: Span) {
		self.state = state;
		self.propagate = Propagate::new(state, depth, span);
	}
	pub fn propagate_till(&mut self, state: BlockState, till_idx: usize, span: Span) {
		assert!(self.index >= till_idx);
		self.propagate(state, self.index - till_idx, span);
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
#[derive(Debug)]
pub struct Context {
	/// Working stack
	pub ws: Stack,
	/// Return stack
	pub rs: Stack,

	pub ops: Vec<Op>,

	/// Table of labels accessible in the current scope/block.
	/// It is a separate table from symbols because labels have a separate namespace.
	pub labels: HashMap<Name, Label>,
}
impl Context {
	pub fn new() -> Self {
		Self {
			ws: Stack::default(),
			rs: Stack::default(),

			ops: Vec::with_capacity(32),

			labels: HashMap::default(),
		}
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
}
