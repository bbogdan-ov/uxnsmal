use vec1::Vec1;

use std::{cmp::Ordering, collections::HashMap};

use crate::{
	bug, err,
	lexer::Span,
	note,
	problem::{self, Note},
	ir,
	symbol::{self, Name, UniqueName, option_name_str},
	typechecker::{Item, Stack},
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
			ws: Stack::new(ws.clone()),
			rs: Stack::default(),

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

		let name = if rs { "return" } else { "working" };
		let ss_stack = if rs {
			&block.snapshot.rs
		} else {
			&block.snapshot.ws
		};
		let stack = if rs { &self.rs } else { &self.ws };

		match stack.len().cmp(&ss_stack.len()) {
			Ordering::Less => {
				let diff = ss_stack.len() - stack.len();
				// TODO: display a proper form of "items"
				let mut e = err!(
					block_end_span,
					"{diff} items less on the {name} stack at the end of this block"
				);
				for item in stack.consumed.iter().rev().take(diff) {
					e.notes.push(note!(item.consumed_at, "consumed here"));
				}
				return Err(e);
			}
			Ordering::Greater => {
				let diff = stack.len() - ss_stack.len();
				// TODO: display a proper form of "items"
				let mut e = err!(
					block_end_span,
					"{diff} items more on the {name} stack at the end of this block"
				);
				for item in stack.items.iter().rev().take(diff) {
					e.notes.push(note!(item.pushed_at, "caused by this"));
				}
				return Err(e);
			}
			Ordering::Equal => (/* ok */),
		}

		let mut notes = Vec::<Note>::default();

		// Check each item type and name in the stack with items in the snapshot.
		for (idx, item) in stack.items.iter().enumerate() {
			let expect = &ss_stack[idx];
			if item.typ != expect.typ {
				notes.push(note!(
					item.pushed_at,
					"this is `{}`, expected `{}`",
					item.typ,
					expect.typ
				))
			} else if item.name != expect.name {
				notes.push(note!(
					item.pushed_at,
					"name is \"{}\", expected \"{}\"",
					option_name_str(item.name.as_ref()),
					option_name_str(expect.name.as_ref())
				))
			}
		}

		if !notes.is_empty() {
			let mut e = err!(
				block_end_span,
				"invalid {name} stack at the end of this block"
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
			let e = err!(span, "\"{name}\" label redefinition");
			let n = note!(prev.span, "defined here");
			Err(e.with_note(n))
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
