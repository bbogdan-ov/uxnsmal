use vec1::Vec1;

use std::collections::HashMap;

use crate::{
	bug, err, ir,
	lexer::Span,
	problem::{self, Note},
	symbol::{self, Name, UniqueName},
	typechecker::{Item, Stack, StackKind},
};

/// Working and return stacks snapshot.
/// Taken at the start of each block to ensure stack balance.
#[derive(Debug, Default, Clone)]
pub struct Snapshot {
	pub ws: Vec<Item>,
	pub rs: Vec<Item>,
}
impl Snapshot {
	pub fn new(ws: Vec<Item>, rs: Vec<Item>) -> Self {
		Self { ws, rs }
	}
}

/// Block state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockState {
	Normal,
	/// Branching blocks are blocks that can exit early.
	Branching,
	/// After this state is set, following operations in this block will never be executed.
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

/// Scope.
/// New scope is only being created inside a definition (function, constant, enum variant, etc),
/// any other blocks `{ ... }` do not create a scope.
#[derive(Debug)]
pub struct Scope {
	/// Working stack.
	pub ws: Stack,
	/// Return stack.
	pub rs: Stack,

	pub ops: ir::Ops,

	/// Table of labels accessible in the current scope.
	/// It is a separate table from symbols because labels have a separate namespace.
	pub labels: HashMap<Name, Label>,

	/// Stack of pareting and child blocks.
	/// The last block in the stack is always the current.
	pub blocks: Vec1<Block>,
}
impl Scope {
	pub fn new(ws: Vec<Item>, expect_ws: Vec<Item>) -> Self {
		Self {
			ws: Stack::new(StackKind::Working, ws.clone()),
			rs: Stack::new(StackKind::Return, Vec::with_capacity(256)),

			ops: ir::Ops::default(),

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
	pub fn end_block(&mut self, block_end_span: Span) -> problem::Result<()> {
		if self.cur_block().state == BlockState::Branching {
			self.compare_block(self.blocks.len() - 1, block_end_span)?;
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
	fn compare_block_impl(
		&mut self,
		rs: bool,
		idx: usize,
		block_end_span: Span,
	) -> problem::Result<()> {
		let block = &self.blocks[idx];

		let expect_stack = if rs {
			&block.snapshot.rs
		} else {
			&block.snapshot.ws
		};
		let expect_len = expect_stack.len();
		let stack = if rs { &self.rs } else { &self.ws };
		let kind = stack.kind;

		// Check stack length.
		if stack.len() < expect_len {
			// Too few.
			let diff = expect_len - stack.len();
			let e = err!(
				block_end_span,
				"this block disbalances the {kind} by consuming {diff} items"
			);
			return Err(e.with_notes_consumed_here(stack, diff));
		} else if expect_stack.len() < stack.len() {
			// Too many.
			let diff = stack.len() - expect_len;
			let e = err!(
				block_end_span,
				"this block disbalances the {kind} by spitting {diff} items"
			);
			return Err(e.with_notes_caused_by(stack, diff));
		}

		let mut notes = Vec::<Note>::default();

		// Check each item type and name in the stack with items in the snapshot.
		for (idx, item) in stack.items.iter().enumerate() {
			let expect = &expect_stack[idx];
			if item.typ != expect.typ {
				let n = problem::note_this_is_but_expected(item, &expect.typ);
				notes.push(n);
			} else if item.name != expect.name {
				let n = problem::note_name_is_but_expected(item, expect.name.as_ref());
				notes.push(n);
			}
		}

		if !notes.is_empty() {
			let mut e = err!(
				block_end_span,
				"invalid {} at the end of this block",
				stack.kind,
			);
			e.notes = notes;
			return Err(e);
		} else {
			Ok(())
		}
	}
	pub fn compare_block(&mut self, idx: usize, block_end_span: Span) -> problem::Result<()> {
		self.compare_block_impl(false, idx, block_end_span)?;
		self.compare_block_impl(true, idx, block_end_span)?;
		Ok(())
	}
	pub fn propagate_state(
		&mut self,
		target_idx: usize,
		block_end_span: Span,
	) -> problem::Result<()> {
		let state = match self.cur_block().state {
			BlockState::Branching => BlockState::Branching,
			_ => BlockState::Finished,
		};

		let branching = state == BlockState::Branching
			|| self.blocks[target_idx].state == BlockState::Branching;
		if branching {
			self.compare_block(target_idx, block_end_span)?;
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
		symbols: &mut symbol::Table,
		name: Name,
		block_idx: usize,
		span: Span,
	) -> problem::Result<UniqueName> {
		let unique_name = symbols.new_unique_name();
		let label = Label::new(unique_name, block_idx, span);
		if let Some(prev) = self.labels.get(&name) {
			let e = problem::err_redefinition(&name, "label", prev.span, span);
			Err(e)
		} else {
			self.labels.insert(name, label);
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
