#![allow(non_upper_case_globals)]

macro_rules! opcodes {
	($($name:ident => $val:expr),*$(,)?) => {
		pub fn opcode_display(op: u8, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			match op {
				$($val => {
					write!(f, stringify!($name))?;
					if op & SHORT_BITS != 0 { write!(f, "2")?; }
					if op & KEEP_BITS != 0 { write!(f, "k")?; }
					if op & RET_BITS != 0 { write!(f, "r")?; }
				},)*
				_ => write!(f, "{op}")?,
			}
			Ok(())
		}

		$(pub const $name: u8 = $val;)*
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
	JMP2r => 0x6c,
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
	LIT2  => 0xa0,
}
