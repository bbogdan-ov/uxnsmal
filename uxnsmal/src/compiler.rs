use std::collections::HashMap;

use crate::{
	error::{self, Error, ErrorKind},
	program::{Function, Intrinsic, Op, Program, TypedIntrMode},
	symbols::UniqueName,
};

#[rustfmt::skip]
#[allow(non_upper_case_globals)]
mod opcode {
	pub const BRK: u8   = 0x00;

	pub const LIT: u8   = 0x80;
	pub const LIT2: u8  = 0xa0;

	pub const JCI: u8   = 0x20;
	pub const JMI: u8   = 0x40;
	pub const JSI: u8   = 0x60;
	pub const JMP2r: u8 = 0x6c;

	pub const LDZ: u8   = 0x10;
	pub const LDA: u8   = 0x14;
	pub const STZ: u8   = 0x11;
	pub const STA: u8   = 0x15;
}

/// Intermediate opcode
#[derive(Debug, Clone, PartialEq, Eq)]
enum Intermediate {
	Opcode(u8),
	LabelRelShortAddr(UniqueName, u16),
	LabelAbsShortAddr(UniqueName),
	ZeropageAbsByteAddr(UniqueName),
}
impl Intermediate {
	fn size(&self) -> u16 {
		match self {
			Intermediate::Opcode(_) => 1,
			Intermediate::LabelRelShortAddr(_, _) => 2, // byte byte
			Intermediate::LabelAbsShortAddr(_) => 1 + 2, // LIT2 byte byte
			Intermediate::ZeropageAbsByteAddr(_) => 1 + 1, // LIT byte
		}
	}
}
impl From<u8> for Intermediate {
	fn from(value: u8) -> Self {
		Self::Opcode(value)
	}
}

/// Program compiler
/// Compiles program down to the UXNTAL bytecode which can be written right into a `.rom` file!!!
pub struct Compiler {
	/// List of intermediate opcodes
	intermediates: Vec<Intermediate>,
	/// Table of labels (functions beginnings and actual labels) and their addresses
	/// collected during first compilation step
	labels: HashMap<UniqueName, u16>,
	/// Table of zero-page memory "allocations" and their addresses in the zero-page memory
	/// collected during first compilation step
	zeropage: HashMap<UniqueName, u8>,

	/// Current opcode absolute offset in bytes
	rom_offset: u16,
	/// Current zero-page absolute offset in bytes
	zeropage_offset: u8,
}
impl Compiler {
	const ROM_START: u16 = 0x100;

	pub fn compile(program: &Program) -> error::Result<Vec<u8>> {
		let mut compiler = Self {
			intermediates: Vec::with_capacity(1024),
			labels: HashMap::with_capacity(128),
			zeropage: HashMap::with_capacity(64),

			rom_offset: Self::ROM_START,
			zeropage_offset: 0,
		};
		compiler.do_compile(program)?;
		Ok(compiler.resolve())
	}

	fn do_compile(&mut self, program: &Program) -> error::Result<()> {
		let Some(reset_func) = &program.reset_func else {
			return Err(Error::everywhere(ErrorKind::NoResetVector));
		};

		// `on-reset` vector must always be at the top of ROM
		self.labels.insert(reset_func.0.clone(), Self::ROM_START);
		self.compile_func(program, &reset_func.1);

		// Collect all zero-page memory allocations
		for (name, var) in program.vars.iter() {
			self.zeropage.insert(name.clone(), self.zeropage_offset);
			self.zeropage_offset += var.size;
		}

		// Compile other functions below `on-reset`
		for (name, func) in program.funcs.iter() {
			self.labels.insert(name.clone(), self.rom_offset);
			self.compile_func(program, func);
		}

		// Put all data into the ROM
		for (name, data) in program.datas.iter() {
			self.labels.insert(name.clone(), self.rom_offset);
			for byte in data.body.iter() {
				self.push(*byte);
			}
		}

		Ok(())
	}
	/// Resolve all the unknown opcodes like labels addresses and return UXNTAl bytecode
	fn resolve(&mut self) -> Vec<u8> {
		let mut bytecode = Vec::with_capacity(1024);

		for idx in 0..self.intermediates.len() {
			// Let any table indexing panic because name of any symbol is guaranteed to be
			// valid at the compilation step
			match &self.intermediates[idx] {
				Intermediate::Opcode(oc) => bytecode.push(*oc),
				Intermediate::LabelRelShortAddr(name, pos) => {
					let abs_addr = self.labels[name];
					let rel_addr = abs_addr.wrapping_sub(*pos + 2);

					let a = ((rel_addr & 0xFF00) >> 8) as u8;
					let b = (rel_addr & 0x00FF) as u8;
					bytecode.push(a);
					bytecode.push(b);
				}
				Intermediate::ZeropageAbsByteAddr(name) => {
					let addr = self.zeropage[name];

					bytecode.push(opcode::LIT);
					bytecode.push(addr);
				}
				Intermediate::LabelAbsShortAddr(name) => {
					let addr = self.labels[name];

					let a = ((addr & 0xFF00) >> 8) as u8;
					let b = (addr & 0x00FF) as u8;
					bytecode.push(opcode::LIT2);
					bytecode.push(a);
					bytecode.push(b);
				}
			}
		}

		bytecode
	}

	fn compile_func(&mut self, program: &Program, func: &Function) {
		self.compile_ops(program, &func.body);

		// Add "return" or "break" opcode based on function kind
		if func.is_vector {
			self.push(opcode::BRK);
		} else {
			self.push(opcode::JMP2r); // return
		}
	}
	fn compile_ops(&mut self, program: &Program, ops: &[Op]) {
		macro_rules! intrinsic {
			($mode:expr, $opcode:expr) => {{
				let mut opcode = $opcode;
				if ($mode.contains(TypedIntrMode::SHORT)) {
					opcode |= 0b00100000;
				}
				if ($mode.contains(TypedIntrMode::RETURN)) {
					opcode |= 0b01000000;
				}
				if ($mode.contains(TypedIntrMode::KEEP)) {
					opcode |= 0b10000000;
				}
				self.push(opcode);
			}};
		}

		// Compile each operation
		for op in ops.iter() {
			match op {
				// Byte literal
				Op::Byte(v) => {
					self.push(opcode::LIT);
					self.push(*v);
				}
				// Short literal
				Op::Short(v) => {
					let a = ((*v & 0xFF00) >> 8) as u8;
					let b = (*v & 0x00FF) as u8;
					self.push(opcode::LIT2);
					self.push(a);
					self.push(b);
				}
				Op::Padding(p) => {
					let iter = std::iter::repeat(Intermediate::Opcode(0x0)).take(*p as usize);
					self.intermediates.extend(iter);
					self.rom_offset += *p;
				}

				// Intrinsic call
				#[rustfmt::skip]
				Op::Intrinsic(kind, mode) => match kind {
					Intrinsic::Add    => intrinsic!(mode, 0x18),
					Intrinsic::Sub    => intrinsic!(mode, 0x19),
					Intrinsic::Mul    => intrinsic!(mode, 0x1a),
					Intrinsic::Div    => intrinsic!(mode, 0x1b),
					Intrinsic::Inc    => intrinsic!(mode, 0x01),
					Intrinsic::Shift  => intrinsic!(mode, 0x1f),

					Intrinsic::And    => intrinsic!(mode, 0x1c),
					Intrinsic::Or     => intrinsic!(mode, 0x1d),
					Intrinsic::Xor    => intrinsic!(mode, 0x1e),

					Intrinsic::Eq     => intrinsic!(mode, 0x08),
					Intrinsic::Neq    => intrinsic!(mode, 0x09),
					Intrinsic::Gth    => intrinsic!(mode, 0x0a),
					Intrinsic::Lth    => intrinsic!(mode, 0x0b),

					Intrinsic::Pop    => intrinsic!(mode, 0x02),
					Intrinsic::Nip    => intrinsic!(mode, 0x03),
					Intrinsic::Swap   => intrinsic!(mode, 0x04),
					Intrinsic::Rot    => intrinsic!(mode, 0x05),
					Intrinsic::Dup    => intrinsic!(mode, 0x06),
					Intrinsic::Over   => intrinsic!(mode, 0x07),

					Intrinsic::Input  => intrinsic!(mode, 0x16),
					Intrinsic::Input2 => intrinsic!(mode, 0x36),
					Intrinsic::Output => intrinsic!(mode, 0x17),

					Intrinsic::Load => {
						if mode.contains(TypedIntrMode::ABS_BYTE_ADDR) {
							intrinsic!(mode, opcode::LDZ)
						} else if mode.contains(TypedIntrMode::ABS_BYTE_ADDR) {
							intrinsic!(mode, opcode::LDA)
						} else {
							unreachable!(concat!(
								"either ABS_BYTE_ADDR or ABS_SHORT_ADDR modes must be",
								"set for 'load' intrinsic at compile stage"
							));
						}
					},
					Intrinsic::Store => {
						if mode.contains(TypedIntrMode::ABS_BYTE_ADDR) {
							intrinsic!(mode, opcode::STZ)
						} else if mode.contains(TypedIntrMode::ABS_BYTE_ADDR) {
							intrinsic!(mode, opcode::STA)
						} else {
							unreachable!(concat!(
								"either ABS_BYTE_ADDR or ABS_SHORT_ADDR modes must be",
								"set for 'store' intrinsic at compile stage"
							));
						}
					},
				},

				Op::FuncCall(name) => {
					self.push(opcode::JSI);
					self.push(Intermediate::LabelRelShortAddr(
						name.clone(),
						self.rom_offset,
					));
				}
				Op::ConstUse(name) => {
					let cnst = &program.consts[name];
					self.compile_ops(program, &cnst.body);
				}

				Op::AbsByteAddrOf(name) => {
					self.push(Intermediate::ZeropageAbsByteAddr(name.clone()));
				}
				Op::AbsShortAddrOf(name) => {
					self.push(Intermediate::LabelAbsShortAddr(name.clone()));
				}

				Op::Label(name) => {
					self.labels.insert(name.clone(), self.rom_offset);
				}
				Op::Jump(label) => {
					self.push(opcode::JMI);
					self.push(Intermediate::LabelRelShortAddr(
						label.clone(),
						self.rom_offset,
					));
				}
				Op::JumpIf(label) => {
					self.push(opcode::JCI);
					self.push(Intermediate::LabelRelShortAddr(
						label.clone(),
						self.rom_offset,
					));
				}
			}
		}
	}

	fn push(&mut self, intermediate: impl Into<Intermediate>) {
		let intermediate: Intermediate = intermediate.into();
		self.rom_offset += intermediate.size();
		self.intermediates.push(intermediate);
	}
}
