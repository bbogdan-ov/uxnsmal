use std::collections::HashMap;

use crate::{
	bytecode::{Bytecode, Opcode},
	error::{self, Error, ErrorKind},
	program::{AddrKind, Function, Intrinsic, Op, Program},
	typechecker::UniqueName,
};

/// Intermediate opcode
#[derive(Debug, Clone, PartialEq, Eq)]
enum Intermediate {
	Opcode(Opcode),
	LabelRelShortAddr(UniqueName, u16),
	LabelAbsShortAddr(UniqueName),
	ZeropageAbsByteAddr(UniqueName),
}
impl Intermediate {
	fn size(&self) -> u16 {
		match self {
			Intermediate::Opcode(Opcode::Padding(s)) => *s,
			Intermediate::Opcode(_) => 1,
			Intermediate::LabelRelShortAddr(_, _) => 2, // byte byte
			Intermediate::LabelAbsShortAddr(_) => 1 + 2, // LIT2 byte byte
			Intermediate::ZeropageAbsByteAddr(_) => 1 + 1, // LIT byte
		}
	}
}
impl From<Opcode> for Intermediate {
	fn from(value: Opcode) -> Self {
		Self::Opcode(value)
	}
}

/// Program compiler
/// Compiles program down to sequence of opcodes
pub struct Compiler<'a> {
	program: &'a Program,
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
impl<'a> Compiler<'a> {
	const ROM_START: u16 = 0x100;

	pub fn new(program: &'a Program) -> Self {
		Self {
			program,
			intermediates: Vec::with_capacity(1024),
			labels: HashMap::with_capacity(128),
			zeropage: HashMap::with_capacity(64),

			rom_offset: Self::ROM_START,
			zeropage_offset: 0,
		}
	}

	pub fn compile(mut self) -> error::Result<Bytecode> {
		let Some(reset_func) = &self.program.reset_func else {
			return Err(Error::everywhere(ErrorKind::NoResetVector));
		};

		// `on-reset` vector must always be at the top of ROM
		self.compile_func(reset_func);
		// TODO: insert `on-reset` func into `labels` table

		// Collect all zero-page memory allocations
		for (name, var) in self.program.vars.iter() {
			self.zeropage.insert(name.clone(), self.zeropage_offset);
			self.zeropage_offset += var.size;
		}

		// Compile other functions below `on-reset`
		for (name, func) in self.program.funcs.iter() {
			if name.as_ref() == "on-reset" {
				continue;
			}

			self.labels.insert(name.clone(), self.rom_offset);
			self.compile_func(func);
		}

		// Put all data into the ROM
		for (name, data) in self.program.datas.iter() {
			self.labels.insert(name.clone(), self.rom_offset);
			for byte in data.body.iter() {
				self.push(Opcode::Byte(*byte));
			}
		}

		Ok(Bytecode {
			opcodes: self.resolve(),
		})
	}
	/// Resolve all the unknown opcodes like labels addresses
	fn resolve(&mut self) -> Vec<Opcode> {
		let mut opcodes = Vec::with_capacity(1024);

		for idx in 0..self.intermediates.len() {
			// Let any table indexing panic because name of any symbol is guaranteed to be
			// valid at the compilation step
			match &self.intermediates[idx] {
				Intermediate::Opcode(oc) => opcodes.push(*oc),
				Intermediate::LabelRelShortAddr(name, pos) => {
					let abs_addr = self.labels[name];
					let rel_addr = abs_addr.wrapping_sub(*pos + 2);

					let a = ((rel_addr & 0xFF00) >> 8) as u8;
					let b = (rel_addr & 0x00FF) as u8;
					opcodes.push(Opcode::Byte(a));
					opcodes.push(Opcode::Byte(b));
				}
				Intermediate::ZeropageAbsByteAddr(name) => {
					let addr = self.zeropage[name];

					opcodes.push(Opcode::LIT);
					opcodes.push(Opcode::Byte(addr));
				}
				Intermediate::LabelAbsShortAddr(name) => {
					let addr = self.labels[name];

					let a = ((addr & 0xFF00) >> 8) as u8;
					let b = (addr & 0x00FF) as u8;
					opcodes.push(Opcode::LIT2);
					opcodes.push(Opcode::Byte(a));
					opcodes.push(Opcode::Byte(b));
				}
			}
		}

		opcodes
	}

	fn compile_func(&mut self, func: &'a Function) {
		self.compile_ops(&func.body);

		// Add "return" or "break" opcode based on function kind
		if func.is_vector {
			self.push(Opcode::BRK);
		} else {
			self.push(Opcode::JMP2r); // return
		}
	}
	fn compile_ops(&mut self, ops: &[Op]) {
		use crate::program::IntrinsicMode as M;

		// Rust dev team, pleeeease, stabilize `${concat(...)}`
		// https://github.com/rust-lang/rust/issues/124225
		// https://github.com/rust-lang/rust/pull/142704
		macro_rules! intrinsic {
			(
				$mode:expr,
				$OP:ident,
				$OP2:ident,
				$OPr:ident,
				$OP2r:ident,
				$OPk:ident,
				$OP2k:ident,
				$OPkr:ident,
				$OP2kr:ident$(,)?
			) => {{
				let oc = if $mode.contains(M::SHORT) {
					Opcode::$OP2
				} else if $mode.contains(M::RETURN) {
					Opcode::$OPr
				} else if $mode.contains(M::SHORT | M::RETURN) {
					Opcode::$OP2r
				} else if $mode.contains(M::KEEP) {
					Opcode::$OPk
				} else if $mode.contains(M::SHORT | M::KEEP) {
					Opcode::$OP2k
				} else if $mode.contains(M::KEEP | M::RETURN) {
					Opcode::$OPkr
				} else if $mode.contains(M::SHORT | M::KEEP | M::RETURN) {
					Opcode::$OP2kr
				} else {
					Opcode::$OP
				};

				self.push(oc);
			}};
		}

		// Compile each operation
		for op in ops.iter() {
			match op {
				// Byte literal
				Op::Byte(v) => {
					self.push(Opcode::LIT);
					self.push(Opcode::Byte(*v));
				}
				// Short literal
				Op::Short(v) => {
					let a = ((*v & 0xFF00) >> 8) as u8;
					let b = (*v & 0x00FF) as u8;
					self.push(Opcode::LIT2);
					self.push(Opcode::Byte(a));
					self.push(Opcode::Byte(b));
				}
				Op::Padding(p) => {
					self.push(Opcode::Padding(*p));
				}

				// Intrinsic call
				Op::Intrinsic(kind, mode) => match kind {
					Intrinsic::Add => intrinsic! {
						mode, ADD, ADD2, ADDr, ADD2r, ADDk, ADD2k, ADDkr, ADD2kr,
					},
					Intrinsic::Sub => intrinsic! {
						mode, SUB, SUB2, SUBr, SUB2r, SUBk, SUB2k, SUBkr, SUB2kr,
					},
					Intrinsic::Mul => intrinsic! {
						mode, MUL, MUL2, MULr, MUL2r, MULk, MUL2k, MULkr, MUL2kr,
					},
					Intrinsic::Div => intrinsic! {
						mode, DIV, DIV2, DIVr, DIV2r, DIVk, DIV2k, DIVkr, DIV2kr,
					},
					Intrinsic::Inc => intrinsic! {
						mode, INC, INC2, INCr, INC2r, INCk, INC2k, INCkr, INC2kr,
					},
					Intrinsic::Shift => intrinsic! {
						mode, SFT, SFT2, SFTr, SFT2r, SFTk, SFT2k, SFTkr, SFT2kr,
					},

					Intrinsic::And => intrinsic! {
						mode, AND, AND2, ANDr, AND2r, ANDk, AND2k, ANDkr, AND2kr,
					},
					Intrinsic::Or => intrinsic! {
						mode, ORA, ORA2, ORAr, ORA2r, ORAk, ORA2k, ORAkr, ORA2kr,
					},
					Intrinsic::Xor => intrinsic! {
						mode, EOR, EOR2, EORr, EOR2r, EORk, EOR2k, EORkr, EOR2kr,
					},

					Intrinsic::Eq => intrinsic! {
						mode, EQU, EQU2, EQUr, EQU2r, EQUk, EQU2k, EQUkr, EQU2kr,
					},
					Intrinsic::Neq => intrinsic! {
						mode, NEQ, NEQ2, NEQr, NEQ2r, NEQk, NEQ2k, NEQkr, NEQ2kr,
					},
					Intrinsic::Gth => intrinsic! {
						mode, GTH, GTH2, GTHr, GTH2r, GTHk, GTH2k, GTHkr, GTH2kr,
					},
					Intrinsic::Lth => intrinsic! {
						mode, LTH, LTH2, LTHr, LTH2r, LTHk, LTH2k, LTHkr, LTH2kr,
					},

					Intrinsic::Pop => intrinsic! {
						mode, POP, POP2, POPr, POP2r, POPk, POP2k, POPkr, POP2kr,
					},
					Intrinsic::Swap => intrinsic! {
						mode, SWP, SWP2, SWPr, SWP2r, SWPk, SWP2k, SWPkr, SWP2kr,
					},
					Intrinsic::Nip => intrinsic! {
						mode, NIP, NIP2, NIPr, NIP2r, NIPk, NIP2k, NIPkr, NIP2kr,
					},
					Intrinsic::Rot => intrinsic! {
						mode, ROT, ROT2, ROTr, ROT2r, ROTk, ROT2k, ROTkr, ROT2kr,
					},
					Intrinsic::Dup => intrinsic! {
						mode, DUP, DUP2, DUPr, DUP2r, DUPk, DUP2k, DUPkr, DUP2kr,
					},
					Intrinsic::Over => intrinsic! {
						mode, OVR, OVR2, OVRr, OVR2r, OVRk, OVR2k, OVRkr, OVR2kr,
					},

					Intrinsic::Load(addr) => match addr {
						AddrKind::Unknown => unreachable!("found unknown addr kind {addr:?}"),

						AddrKind::AbsByte => intrinsic! {
							mode, LDZ, LDZ2, LDZr, LDZ2r, LDZk, LDZ2k, LDZkr, LDZ2kr,
						},
						AddrKind::AbsShort => intrinsic! {
							mode, LDA, LDA2, LDAr, LDA2r, LDAk, LDA2k, LDAkr, LDA2kr,
						},
					},
					Intrinsic::Store(addr) => match addr {
						AddrKind::Unknown => unreachable!("found unknown addr kind {addr:?}"),

						AddrKind::AbsByte => intrinsic! {
							mode, STZ, STZ2, STZr, STZ2r, STZk, STZ2k, STZkr, STZ2kr,
						},
						AddrKind::AbsShort => intrinsic! {
							mode, STA, STA2, STAr, STA2r, STAk, STA2k, STAkr, STA2kr,
						},
					},

					Intrinsic::Input => intrinsic! {
						mode, DEI, DEI2, DEIr, DEI2r, DEIk, DEI2k, DEIkr, DEI2kr,
					},
					Intrinsic::Input2 => intrinsic! {
						mode, DEI, DEI2, DEIr, DEI2r, DEIk, DEI2k, DEIkr, DEI2kr,
					},
					Intrinsic::Output => intrinsic! {
						mode, DEO, DEO2, DEOr, DEO2r, DEOk, DEO2k, DEOkr, DEO2kr,
					},
				},

				Op::Call(name) => {
					self.push(Opcode::JSI);
					self.push(Intermediate::LabelRelShortAddr(
						name.clone(),
						self.rom_offset,
					));
				}
				Op::ConstUse(name) => {
					let cnst = &self.program.consts[name];
					self.compile_ops(&cnst.body);
				}

				Op::ByteAddrOf(name) => {
					self.push(Intermediate::ZeropageAbsByteAddr(name.clone()));
				}
				Op::ShortAddrOf(name) => {
					self.push(Intermediate::LabelAbsShortAddr(name.clone()));
				}

				Op::Label(name) => {
					self.labels.insert(name.clone(), self.rom_offset);
				}
				Op::Jump(label) => {
					self.push(Opcode::JMI);
					self.push(Intermediate::LabelRelShortAddr(
						label.clone(),
						self.rom_offset,
					));
				}
				Op::JumpIf(label) => {
					self.push(Opcode::JCI);
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
