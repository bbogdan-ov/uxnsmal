use std::collections::{BTreeMap, HashMap};

use crate::{
	bug,
	opcodes::{self, Bytecode},
	ir::{self, Op, Intr},
	symbol::UniqueName,
};

/// Intermediate opcode.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Intermediate {
	/// Any byte, whether an operation or simply a byte.
	Byte(u8),
	/// Insert relative short address (ROM memory) of a label.
	RelShortAddr {
		name: UniqueName,
		/// Calculate relative address to this address.
		relative_to: u16,
	},
	/// Insert absolute short address (ROM memory) of a label.
	AbsShortAddr {
		name: UniqueName,
		/// Offset that will be added to this address.
		offset: u16,
	},
	/// Insert absolute byte address (zero-page memory) of a label.
	AbsByteAddr {
		name: UniqueName,
		/// Offset that will be added to this address.
		offset: u8,
	},
}
impl Intermediate {
	fn size(&self) -> u16 {
		match self {
			Intermediate::Byte(_) => 1,
			Intermediate::RelShortAddr { .. } => 2,
			Intermediate::AbsShortAddr { .. } => 2,
			Intermediate::AbsByteAddr { .. } => 1,
		}
	}
}
impl From<u8> for Intermediate {
	fn from(value: u8) -> Self {
		Self::Byte(value)
	}
}

/// Program compiler.
/// Compiles program down to the UXNTAL bytecode which can be written right into a `.rom` file!!!
pub struct Compiler {
	/// List of intermediate opcodes.
	intermediates: Vec<Intermediate>,
	/// Table of labels (functions beginnings and actual labels) and their addresses.
	/// collected during first compilation step.
	labels: HashMap<UniqueName, u16>,
	/// Table of zero-page memory "allocations" and their addresses in the zero-page memory.
	/// collected during first compilation step.
	zeropage: HashMap<UniqueName, u8>,

	/// Current opcode absolute offset in bytes.
	rom_offset: u16,
	/// Current zero-page absolute offset in bytes.
	zeropage_offset: u8,
}
impl Compiler {
	const ROM_START: u16 = 0x100;

	pub fn compile(program: &ir::Program) -> Bytecode {
		let mut compiler = Self {
			intermediates: Vec::with_capacity(1024),
			labels: HashMap::with_capacity(128),
			zeropage: HashMap::with_capacity(64),

			rom_offset: Self::ROM_START,
			zeropage_offset: 0,
		};
		compiler.do_compile(program);
		compiler.resolve(program)
	}

	fn do_compile(&mut self, program: &ir::Program) {
		// TODO: add some sort of a flag to make `on-reset ( -> )` optional.
		// Make it always optional for now.
		if let Some(reset_func) = &program.reset_func {
			// `on-reset` vector must always be at the top of ROM.
			self.labels.insert(reset_func.0, Self::ROM_START);
			self.compile_func(program, &reset_func.1);
		};

		// Compile other functions below `on-reset`.
		for (name, func) in program.funcs.iter() {
			self.labels.insert(*name, self.rom_offset);
			self.compile_func(program, func);
		}

		// Collect all zero-page memory allocations.
		for (name, var) in program.vars.iter() {
			if var.in_rom {
				self.labels.insert(*name, self.rom_offset);
				for _ in 0..var.size {
					self.push(0);
				}
			} else {
				self.zeropage.insert(*name, self.zeropage_offset);
				// TODO!: check for zero-page memory overflow.
				self.zeropage_offset += var.size as u8;
			}
		}

		// Put all data into the ROM.
		for (name, data) in program.datas.iter() {
			self.labels.insert(*name, self.rom_offset);
			for byte in data.body.iter() {
				self.push(*byte);
			}
		}
	}
	/// Resolve all the unknown opcodes like labels addresses and return UXNTAl bytecode.
	fn resolve(&mut self, program: &ir::Program) -> Bytecode {
		let mut opcodes = Vec::with_capacity(1024);

		for idx in 0..self.intermediates.len() {
			// Let any table indexing panic because name of any symbol is guaranteed to be
			// valid at the compilation step.
			match &self.intermediates[idx] {
				Intermediate::Byte(oc) => opcodes.push(*oc),
				Intermediate::RelShortAddr { name, relative_to } => {
					let abs_addr = self.labels[name];
					let rel_addr = abs_addr.wrapping_sub(*relative_to + 2);

					let a = ((rel_addr & 0xFF00) >> 8) as u8;
					let b = (rel_addr & 0x00FF) as u8;
					opcodes.push(a);
					opcodes.push(b);
				}
				Intermediate::AbsByteAddr { name, offset } => {
					let addr = self.zeropage[name] + *offset;

					opcodes.push(addr);
				}
				Intermediate::AbsShortAddr { name, offset } => {
					let addr = self.labels[name] + *offset;

					let a = ((addr & 0xFF00) >> 8) as u8;
					let b = (addr & 0x00FF) as u8;
					opcodes.push(a);
					opcodes.push(b);
				}
			}
		}

		// Build string-keyed symbol maps from UniqueName maps and program.name table
		let mut labels_map: BTreeMap<String, u16> = BTreeMap::new();
		for (uniq, &addr) in self.labels.iter() {
			if let Some(name) = program.names.get(uniq) {
				labels_map.insert(name.clone(), addr);
			}
		}

		let mut zeropage_map: BTreeMap<String, u8> = BTreeMap::new();
		for (uniq, &addr) in self.zeropage.iter() {
			if let Some(name) = program.names.get(uniq) {
				zeropage_map.insert(name.clone(), addr);
			}
		}

		Bytecode {
			opcodes,
			labels: labels_map,
			zeropage: zeropage_map,
		}
	}

	fn compile_func(&mut self, program: &ir::Program, func: &ir::Func) {
		self.compile_ops(program, func.is_vector, &func.body);

		// Push "return" or "break" opcode based on function type.
		if func.is_vector {
			self.push(opcodes::BRK);
		} else {
			self.push(opcodes::JMP2r); // return
		}
	}
	fn compile_ops(&mut self, program: &ir::Program, is_vector: bool, ops: &ir::Ops) {
		macro_rules! intrinsic {
			($mode:expr, $opcode:expr) => {{
				let mut opcode = $opcode;
				if ($mode.contains(ir::IntrMode::SHORT)) {
					opcode |= opcodes::SHORT_BITS;
				}
				if ($mode.contains(ir::IntrMode::RETURN)) {
					opcode |= opcodes::RET_BITS;
				}
				if ($mode.contains(ir::IntrMode::KEEP)) {
					opcode |= opcodes::KEEP_BITS;
				}
				self.push(opcode);
			}};
		}

		// Compile each operation.
		for op in ops.list.iter() {
			match op {
				// Byte literal.
				Op::Byte(v) => {
					self.push(opcodes::LIT);
					self.push(*v);
				}
				// Short literal.
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

				// Intrinsic call.
				#[rustfmt::skip]
				Op::Intr(kind, mode) => match kind {
					Intr::Add    => intrinsic!(mode, opcodes::ADD),
					Intr::Sub    => intrinsic!(mode, opcodes::SUB),
					Intr::Mul    => intrinsic!(mode, opcodes::MUL),
					Intr::Div    => intrinsic!(mode, opcodes::DIV),
					Intr::Inc    => intrinsic!(mode, opcodes::INC),
					Intr::Shift  => intrinsic!(mode, opcodes::SFT),

					Intr::And    => intrinsic!(mode, opcodes::AND),
					Intr::Or     => intrinsic!(mode, opcodes::ORA),
					Intr::Xor    => intrinsic!(mode, opcodes::EOR),

					Intr::Eq     => intrinsic!(mode, opcodes::EQU),
					Intr::Neq    => intrinsic!(mode, opcodes::NEQ),
					Intr::Gth    => intrinsic!(mode, opcodes::GTH),
					Intr::Lth    => intrinsic!(mode, opcodes::LTH),

					Intr::Pop    => intrinsic!(mode, opcodes::POP),
					Intr::Nip    => intrinsic!(mode, opcodes::NIP),
					Intr::Swap   => intrinsic!(mode, opcodes::SWP),
					Intr::Rot    => intrinsic!(mode, opcodes::ROT),
					Intr::Dup    => intrinsic!(mode, opcodes::DUP),
					Intr::Over   => intrinsic!(mode, opcodes::OVR),
					Intr::Sth    => intrinsic!(mode, opcodes::STH),

					Intr::Input  => intrinsic!(mode, opcodes::DEI),
					Intr::Input2 => intrinsic!(mode, opcodes::DEI | opcodes::SHORT_BITS),
					Intr::Output => intrinsic!(mode, opcodes::DEO),

					Intr::Load(addr) => {
						match addr {
							ir::AddrMode::AbsByte => intrinsic!(mode, opcodes::LDZ),
							ir::AddrMode::AbsShort => intrinsic!(mode, opcodes::LDA),
							ir::AddrMode::Unknown => bug!("address mode of `load` intrinsic cannot be `Unknown` at compile stage"),
						}
					},
					Intr::Store(addr) => {
						match addr {
							ir::AddrMode::AbsByte => intrinsic!(mode, opcodes::STZ),
							ir::AddrMode::AbsShort => intrinsic!(mode, opcodes::STA),
							ir::AddrMode::Unknown => bug!("address mode of `store` intrinsic cannot be `Unknown` at compile stage"),
						}
					},

					Intr::Call => intrinsic!(mode, opcodes::JSR)
				},

				Op::FuncCall(name) => {
					self.push(opcodes::JSI);
					self.push(Intermediate::RelShortAddr {
						name: *name,
						relative_to: self.rom_offset,
					});
				}
				Op::ConstUse(name) => {
					let cnst = &program.consts[name];
					self.compile_ops(program, false, &cnst.body);
				}

				Op::AbsByteAddr { name, offset } => {
					self.push(opcodes::LIT);
					self.push(Intermediate::AbsByteAddr {
						name: *name,
						offset: *offset,
					});
				}
				Op::AbsShortAddr { name, offset } => {
					self.push(opcodes::LIT2);
					self.push(Intermediate::AbsShortAddr {
						name: *name,
						offset: *offset,
					});
				}

				Op::Label(name) => {
					self.labels.insert(*name, self.rom_offset);
				}
				Op::Jump(label) => {
					self.push(opcodes::JMI);
					self.push(Intermediate::RelShortAddr {
						name: *label,
						relative_to: self.rom_offset,
					});
				}
				Op::JumpIf(label) => {
					self.push(opcodes::JCI);
					self.push(Intermediate::RelShortAddr {
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
