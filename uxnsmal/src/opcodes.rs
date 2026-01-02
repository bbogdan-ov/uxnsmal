#![allow(non_upper_case_globals)]

use std::fmt::Debug;

macro_rules! opcodes {
	($($name:ident => $val:expr),*$(,)?) => {
		$(pub const $name: u8 = $val;)*

		#[allow(clippy::bad_bit_mask)]
		pub fn opcode_display(op: u8, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			let mut flags = op;

			if false {
				unreachable!()
			} else if op == 0 {
				write!(f, "BRK")?;
				flags = 0;
			} else if op == JCI {
				write!(f, "JCI")?;
				flags = 0;
			} else if op == JMI {
				write!(f, "JMI")?;
				flags = 0;
			} else if op == JSI {
				write!(f, "JSI")?;
				flags = 0;
			} else if op & 0b00011111 == 0 {
				write!(f, "LIT")?;
				flags ^= 0x80;
			}
			$(else if op & 0b00011111 == $val {
				write!(f, stringify!($name))?;
			})*
			else {
				write!(f, "0x{op:x}")?;
				return Ok(());
			}

			if flags & SHORT_BITS == SHORT_BITS { write!(f, "2")?; }
			if flags & KEEP_BITS == KEEP_BITS { write!(f, "k")?; }
			if flags & RET_BITS == RET_BITS { write!(f, "r")?; }

			write!(f, " (0x{op:x})")
		}
	};
}

pub const SHORT_BITS: u8 = 0b00100000;
pub const RET_BITS: u8 = 0b01000000;
pub const KEEP_BITS: u8 = 0b10000000;

#[rustfmt::skip]
opcodes! {
	BRK   => 0x00,

	INC   => 0x01,
	POP   => 0x02,
	NIP   => 0x03,
	SWP   => 0x04,
	ROT   => 0x05,
	DUP   => 0x06,
	OVR   => 0x07,
	EQU   => 0x08,
	NEQ   => 0x09,
	GTH   => 0x0a,
	LTH   => 0x0b,
	JMP   => 0x0c,
	JCN   => 0x0d,
	JSR   => 0x0e,
	STH   => 0x0f,

	LDZ   => 0x10,
	STZ   => 0x11,
	LDR   => 0x12,
	STR   => 0x13,
	LDA   => 0x14,
	STA   => 0x15,
	DEI   => 0x16,
	DEO   => 0x17,
	ADD   => 0x18,
	SUB   => 0x19,
	MUL   => 0x1a,
	DIV   => 0x1b,
	AND   => 0x1c,
	ORA   => 0x1d,
	EOR   => 0x1e,
	SFT   => 0x1f,

	JCI   => 0x20,
	JMI   => 0x40,
	JSI   => 0x60,
	LIT   => 0x80,
}

pub const LIT2: u8 = 0xa0;
pub const LITr: u8 = 0xc0;
pub const LIT2r: u8 = 0xe0;
pub const JMP2r: u8 = JMP | SHORT_BITS | RET_BITS;

/// Bytecode of the UXN virtual machine.
#[derive(Clone)]
pub struct Bytecode {
	pub opcodes: Vec<u8>,
}
impl Debug for Bytecode {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if f.alternate() {
			writeln!(f, "[")?;
			for op in self.opcodes.iter() {
				opcode_display(*op, f)?;
				writeln!(f, ",")?;
			}
		} else {
			write!(f, "[")?;
			for op in self.opcodes.iter() {
				opcode_display(*op, f)?;
				write!(f, ", ")?;
			}
		}
		write!(f, "]")?;
		Ok(())
	}
}
