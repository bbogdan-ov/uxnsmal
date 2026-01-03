use vec1::Vec1;

use crate::bug;
use crate::error::{self, Error, SymbolError};
use crate::lexer::Span;
use crate::program::Ops;
use crate::symbols::{Name, SymbolsTable, UniqueName};
use crate::typechecker::{Stack, StackItem, StackMatch};
use std::collections::HashMap;

/// Working and return stacks snapshot.
/// Taken at the start of each block to ensure stack balance.
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

/// Block state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockState {
	Normal,
	/// Branching blocks are blocks that can exit early.
	Branching,
	/// Following operations in this block will never be executed.
	Finished,
}

/// Block.
#[derive(Debug)]
pub struct Block {
	pub state: BlockState,
	pub snapshot: Snapshot,
}

/// Block label.
#[derive(Debug, Clone)]
pub struct Label {
	pub unique_name: UniqueName,
	pub block_idx: usize,
	/// Location at which this label is defined.
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

/// Global scope.
#[derive(Default, Debug)]
pub struct GlobalScope {
	/// Symbols accessible from everywhere in the file.
	pub symbols: SymbolsTable,
}

/// Scope.
/// New scope is only being created inside a definition (function, constant, enum variant, etc),
/// any blocks `{ ... }` do not create a separate scope.
#[derive(Debug)]
pub struct Scope<'g> {
	pub global: &'g mut GlobalScope,

	/// Working stack.
	pub ws: Stack,
	/// Return stack.
	pub rs: Stack,

	pub ops: Ops,

	/// Table of labels accessible in the current scope.
	/// It is a separate table from symbols because labels have a separate namespace.
	pub labels: HashMap<Name, Label>,

	/// Stack of pareting and child blocks.
	/// The last block in the stack is always the current.
	pub blocks: Vec1<Block>,
}
impl<'g> Scope<'g> {
	pub fn new(global: &'g mut GlobalScope, ws: Vec<StackItem>, expect_ws: Vec<StackItem>) -> Self {
		Self {
			global,

			ws: Stack::new(ws.clone()),
			rs: Stack::default(),

			ops: Ops::default(),

			labels: HashMap::default(),

			blocks: vec1::vec1![Block {
				state: BlockState::Branching,
				snapshot: Snapshot::new(expect_ws, vec![]),
			}],
		}
	}

	pub fn begin_block(&mut self, branching: bool) -> usize {
		let snapshot = self.take_snapshot();
		self.begin_block_with(branching, snapshot)
	}
	pub fn begin_block_with(&mut self, branching: bool, snapshot: Snapshot) -> usize {
		let block = Block {
			state: if branching {
				BlockState::Branching
			} else {
				BlockState::Normal
			},
			snapshot,
		};
		self.blocks.push(block);
		self.blocks.len() - 1
	}
	pub fn end_block(&mut self, span: Span) -> error::Result<()> {
		if self.cur_block().state == BlockState::Branching {
			self.compare_block(self.blocks.len() - 1, span)?;
		}

		self.finish_block();

		if self.blocks.len() > 1 {
			self.pop_block();
		}
		Ok(())
	}
	pub fn pop_block(&mut self) -> Block {
		let Ok(block) = self.blocks.pop() else {
			panic!("cannot pop the root block");
		};
		block
	}
	pub fn finish_block(&mut self) {
		let block = self.cur_block();
		if block.state == BlockState::Branching {
			// Restore previous state of the stacks for branching blocks to pretend that
			// this block has never been executed.
			// Because it indeed may not execute, that's why it is a "branching" block.
			let snapshot = block.snapshot.clone();
			self.restore_snapshot(snapshot);
		}

		self.cur_block_mut().state = BlockState::Finished;
	}
	pub fn compare_block(&mut self, idx: usize, span: Span) -> error::Result<()> {
		let block = &self.blocks[idx];

		let mut ws_consumer = self.ws.consumer_keep(span);
		ws_consumer.compare(block.snapshot.ws.iter(), StackMatch::Exact)?;
		ws_consumer.compare_names(block.snapshot.ws.iter().map(|t| t.name.as_ref()))?;

		let mut rs_consumer = self.rs.consumer_keep(span);
		rs_consumer.compare(block.snapshot.rs.iter(), StackMatch::Exact)?;
		rs_consumer.compare_names(block.snapshot.rs.iter().map(|t| t.name.as_ref()))?;

		Ok(())
	}
	pub fn propagate_state(&mut self, target_idx: usize, span: Span) -> error::Result<()> {
		let state = match self.cur_block().state {
			BlockState::Branching => BlockState::Branching,
			_ => BlockState::Finished,
		};

		let branching = state == BlockState::Branching
			|| self.blocks[target_idx].state == BlockState::Branching;
		if branching {
			self.compare_block(target_idx, span)?;
		}

		for (idx, block) in self.blocks.iter_mut().enumerate().rev() {
			block.state = state;
			if idx == target_idx {
				break;
			}
		}

		self.finish_block();

		Ok(())
	}

	pub fn take_snapshot(&mut self) -> Snapshot {
		let ws = self.ws.items.clone();
		let rs = self.rs.items.clone();
		Snapshot::new(ws, rs)
	}
	pub fn restore_snapshot(&mut self, snapshot: Snapshot) {
		self.ws.items = snapshot.ws;
		self.rs.items = snapshot.rs;
	}

	pub fn define_label(
		&mut self,
		name: Name,
		block_idx: usize,
		span: Span,
	) -> error::Result<UniqueName> {
		let unique_name = self.global.symbols.new_unique_name();
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

	pub fn cur_block(&self) -> &Block {
		self.blocks.last()
	}
	pub fn cur_block_mut(&mut self) -> &mut Block {
		self.blocks.last_mut()
	}
}
