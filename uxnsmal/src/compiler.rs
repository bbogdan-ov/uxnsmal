use std::collections::HashMap;

use crate::{
	error,
	opcodes::{self, Bytecode},
	program::{Function, IntrMode, Intrinsic, Op, Program},
	symbols::UniqueName,
};

/// Intermediate opcode
#[derive(Debug, Clone, PartialEq, Eq)]
enum Intermediate {
	/// Any byte, whether an operation or simply a byte
	Byte(u8),
	/// Insert relative short address (ROM memory) of the label
	RelShortAddrOf {
		name: UniqueName,
		/// Absolute short address of this intruction.
		/// Used to calculate relative address to label `name`
		relative_to: u16,
	},
	/// Insert absolute short address (ROM memory) of the label
	AbsShortAddrOf(UniqueName),
	/// Insert absolute byte address (zero-page memory) of the label
	AbsByteAddrOf(UniqueName),
}
impl Intermediate {
	fn size(&self) -> u16 {
		match self {
			Intermediate::Byte(_) => 1,
			Intermediate::RelShortAddrOf { .. } => 2,
			Intermediate::AbsShortAddrOf(_) => 2,
			Intermediate::AbsByteAddrOf(_) => 1,
		}
	}
}
impl From<u8> for Intermediate {
	fn from(value: u8) -> Self {
		Self::Byte(value)
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

	pub fn compile(program: &Program) -> error::Result<Bytecode> {
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
		// TODO: add some sort of a flag to make `on-reset ( -> )` optional.
		// Make it always optional for now
		if let Some(reset_func) = &program.reset_func {
			// `on-reset` vector must always be at the top of ROM
			self.labels.insert(reset_func.0, Self::ROM_START);
			self.compile_func(program, &reset_func.1);
		};

		// Collect all zero-page memory allocations
		for (name, var) in program.vars.iter() {
			self.zeropage.insert(*name, self.zeropage_offset);
			self.zeropage_offset += var.size;
		}

		// Compile other functions below `on-reset`
		for (name, func) in program.funcs.iter() {
			self.labels.insert(*name, self.rom_offset);
			self.compile_func(program, func);
		}

		// Put all data into the ROM
		for (name, data) in program.datas.iter() {
			self.labels.insert(*name, self.rom_offset);
			for byte in data.body.iter() {
				self.push(*byte);
			}
		}

		Ok(())
	}
	/// Resolve all the unknown opcodes like labels addresses and return UXNTAl bytecode
	fn resolve(&mut self) -> Bytecode {
		let mut opcodes = Vec::with_capacity(1024);

		for idx in 0..self.intermediates.len() {
			// Let any table indexing panic because name of any symbol is guaranteed to be
			// valid at the compilation step
			match &self.intermediates[idx] {
				Intermediate::Byte(oc) => opcodes.push(*oc),
				Intermediate::RelShortAddrOf { name, relative_to } => {
					let abs_addr = self.labels[name];
					let rel_addr = abs_addr.wrapping_sub(*relative_to + 2);

					let a = ((rel_addr & 0xFF00) >> 8) as u8;
					let b = (rel_addr & 0x00FF) as u8;
					opcodes.push(a);
					opcodes.push(b);
				}
				Intermediate::AbsByteAddrOf(name) => {
					let addr = self.zeropage[name];

					opcodes.push(addr);
				}
				Intermediate::AbsShortAddrOf(name) => {
					let addr = self.labels[name];

					let a = ((addr & 0xFF00) >> 8) as u8;
					let b = (addr & 0x00FF) as u8;
					opcodes.push(a);
					opcodes.push(b);
				}
			}
		}

		Bytecode { opcodes }
	}

	fn compile_func(&mut self, program: &Program, func: &Function) {
		self.compile_ops(program, func.is_vector, &func.body);

		// Push "return" or "break" opcode based on function type
		if func.is_vector {
			self.push(opcodes::BRK);
		} else {
			self.push(opcodes::JMP2r); // return
		}
	}
	fn compile_ops(&mut self, program: &Program, is_vector: bool, ops: &[Op]) {
		macro_rules! intrinsic {
			($mode:expr, $opcode:expr) => {{
				let mut opcode = $opcode;
				if ($mode.contains(IntrMode::SHORT)) {
					opcode |= opcodes::SHORT_BITS;
				}
				if ($mode.contains(IntrMode::RETURN)) {
					opcode |= opcodes::RET_BITS;
				}
				if ($mode.contains(IntrMode::KEEP)) {
					opcode |= opcodes::KEEP_BITS;
				}
				self.push(opcode);
			}};
		}

		// Compile each operation
		for op in ops.iter() {
			match op {
				// Byte literal
				Op::Byte(v) => {
					self.push(opcodes::LIT);
					self.push(*v);
				}
				// Short literal
				Op::Short(v) => {
					let a = ((*v & 0xFF00) >> 8) as u8;
					let b = (*v & 0x00FF) as u8;
					self.push(opcodes::LIT2);
					self.push(a);
					self.push(b);
				}
				Op::Padding(p) => {
					let iter = std::iter::repeat_n(Intermediate::Byte(0x0), *p as usize);
					self.intermediates.extend(iter);
					self.rom_offset += *p;
				}

				// Intrinsic call
				#[rustfmt::skip]
				Op::Intrinsic(kind, mode) => match kind {
					Intrinsic::Add    => intrinsic!(mode, opcodes::ADD),
					Intrinsic::Sub    => intrinsic!(mode, opcodes::SUB),
					Intrinsic::Mul    => intrinsic!(mode, opcodes::MUL),
					Intrinsic::Div    => intrinsic!(mode, opcodes::DIV),
					Intrinsic::Inc    => intrinsic!(mode, opcodes::INC),
					Intrinsic::Shift  => intrinsic!(mode, opcodes::SFT),

					Intrinsic::And    => intrinsic!(mode, opcodes::AND),
					Intrinsic::Or     => intrinsic!(mode, opcodes::ORA),
					Intrinsic::Xor    => intrinsic!(mode, opcodes::EOR),

					Intrinsic::Eq     => intrinsic!(mode, opcodes::EQU),
					Intrinsic::Neq    => intrinsic!(mode, opcodes::NEQ),
					Intrinsic::Gth    => intrinsic!(mode, opcodes::GTH),
					Intrinsic::Lth    => intrinsic!(mode, opcodes::LTH),

					Intrinsic::Pop    => intrinsic!(mode, opcodes::POP),
					Intrinsic::Nip    => intrinsic!(mode, opcodes::NIP),
					Intrinsic::Swap   => intrinsic!(mode, opcodes::SWP),
					Intrinsic::Rot    => intrinsic!(mode, opcodes::ROT),
					Intrinsic::Dup    => intrinsic!(mode, opcodes::DUP),
					Intrinsic::Over   => intrinsic!(mode, opcodes::OVR),
					Intrinsic::Sth    => intrinsic!(mode, opcodes::STH),

					Intrinsic::Input  => intrinsic!(mode, opcodes::DEI),
					Intrinsic::Input2 => intrinsic!(mode, opcodes::DEI | opcodes::SHORT_BITS),
					Intrinsic::Output => intrinsic!(mode, opcodes::DEO),

					Intrinsic::Load => {
						if mode.contains(IntrMode::ABS_BYTE_ADDR) {
							intrinsic!(mode, opcodes::LDZ)
						} else if mode.contains(IntrMode::ABS_SHORT_ADDR) {
							intrinsic!(mode, opcodes::LDA)
						} else {
							panic!(concat!(
								"either ABS_BYTE_ADDR or ABS_SHORT_ADDR modes must be",
								"set for `load` intrinsic at compile stage"
							));
						}
					},
					Intrinsic::Store => {
						if mode.contains(IntrMode::ABS_BYTE_ADDR) {
							intrinsic!(mode, opcodes::STZ)
						} else if mode.contains(IntrMode::ABS_SHORT_ADDR) {
							intrinsic!(mode, opcodes::STA)
						} else {
							panic!(concat!(
								"either ABS_BYTE_ADDR or ABS_SHORT_ADDR modes must be",
								"set for `store` intrinsic at compile stage"
							));
						}
					},
				},

				Op::FuncCall(name) => {
					self.push(opcodes::JSI);
					self.push(Intermediate::RelShortAddrOf {
						name: *name,
						relative_to: self.rom_offset,
					});
				}
				Op::ConstUse(name) => {
					let cnst = &program.consts[name];
					self.compile_ops(program, false, &cnst.body);
				}

				Op::AbsByteAddrOf(name) => {
					self.push(opcodes::LIT);
					self.push(Intermediate::AbsByteAddrOf(*name));
				}
				Op::AbsShortAddrOf(name) => {
					self.push(opcodes::LIT2);
					self.push(Intermediate::AbsShortAddrOf(*name));
				}

				Op::Label(name) => {
					self.labels.insert(*name, self.rom_offset);
				}
				Op::Jump(label) => {
					self.push(opcodes::JMI);
					self.push(Intermediate::RelShortAddrOf {
						name: *label,
						relative_to: self.rom_offset,
					});
				}
				Op::JumpIf(label) => {
					self.push(opcodes::JCI);
					self.push(Intermediate::RelShortAddrOf {
						name: *label,
						relative_to: self.rom_offset,
					});
				}
				Op::Return => {
					if is_vector {
						self.push(opcodes::BRK);
					} else {
						self.push(opcodes::JMP2r);
					}
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
