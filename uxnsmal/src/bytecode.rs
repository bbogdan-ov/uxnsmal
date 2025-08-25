use std::io::Write;

macro_rules! opcode {
	($($variant:ident => $byte:expr),*$(,)?) => {
		/// UXN opcode
		/// See [wiki] for the full list of opcodes and their description
		///
		/// [wiki]: https://wiki.xxiivv.com/site/uxntal_opcodes.html
		#[allow(clippy::upper_case_acronyms)]
		#[derive(Debug, Clone, Copy, PartialEq, Eq)]
		pub enum Opcode {
			Byte(u8),
			Padding(u16),
			$($variant,)*
		}
		impl From<Opcode> for u8 {
			fn from(value: Opcode) -> Self {
				match value {
					Opcode::Byte(b) => b,
					Opcode::Padding(_) => 0,
					$(Opcode::$variant => $byte,)*
				}
			}
		}
	};
}

#[rustfmt::skip]
opcode! {
	// BRK
	BRK      => 0x00,

	// LDZ
	LDZ      => 0x10,
	LDZ2     => 0x30,
	LDZr     => 0x50,
	LDZ2r    => 0x70,
	LDZk     => 0x90,
	LDZ2k    => 0xb0,
	LDZkr    => 0xd0,
	LDZ2kr   => 0xf0,

	// LDA
	LDA      => 0x14,
	LDA2     => 0x34,
	LDAr     => 0x54,
	LDA2r    => 0x74,
	LDAk     => 0x94,
	LDA2k    => 0xb4,
	LDAkr    => 0xd4,
	LDA2kr   => 0xf4,

	// STZ
	STZ      => 0x11,
	STZ2     => 0x31,
	STZr     => 0x51,
	STZ2r    => 0x71,
	STZk     => 0x91,
	STZ2k    => 0xb1,
	STZkr    => 0xd1,
	STZ2kr   => 0xf1,

	// STA
	STA      => 0x15,
	STA2     => 0x35,
	STAr     => 0x55,
	STA2r    => 0x75,
	STAk     => 0x95,
	STA2k    => 0xb5,
	STAkr    => 0xd5,
	STA2kr   => 0xf5,

	// Literal
	LIT      => 0x80,
	LIT2     => 0xa0,
	LITr     => 0xc0,
	LIT2r    => 0xe0,

	// JCI
	JCI      => 0x20,
	// JMI
	JMI      => 0x40,
	// JSI
	JSI      => 0x60,

	// DEI
	DEI      => 0x16,
	DEI2     => 0x36,
	DEIr     => 0x56,
	DEI2r    => 0x76,
	DEIk     => 0x96,
	DEI2k    => 0xb6,
	DEIkr    => 0xd6,
	DEI2kr   => 0xf6,

	// DEO
	DEO      => 0x17,
	DEO2     => 0x37,
	DEOr     => 0x57,
	DEO2r    => 0x77,
	DEOk     => 0x97,
	DEO2k    => 0xb7,
	DEOkr    => 0xd7,
	DEO2kr   => 0xf7,

	// INC
	INC      => 0x01,
	INC2     => 0x21,
	INCr     => 0x41,
	INC2r    => 0x61,
	INCk     => 0x81,
	INC2k    => 0xa1,
	INCkr    => 0xc1,
	INC2kr   => 0xe1,

	// POP
	POP      => 0x02,
	POP2     => 0x22,
	POPr     => 0x42,
	POP2r    => 0x62,
	POPk     => 0x82,
	POP2k    => 0xa2,
	POPkr    => 0xc2,
	POP2kr   => 0xe2,

	// NIP
	NIP      => 0x03,
	NIP2     => 0x23,
	NIPr     => 0x43,
	NIP2r    => 0x63,
	NIPk     => 0x83,
	NIP2k    => 0xa3,
	NIPkr    => 0xc3,
	NIP2kr   => 0xe3,

	// SWP
	SWP      => 0x04,
	SWP2     => 0x24,
	SWPr     => 0x44,
	SWP2r    => 0x64,
	SWPk     => 0x84,
	SWP2k    => 0xa4,
	SWPkr    => 0xc4,
	SWP2kr   => 0xe4,

	// ROT
	ROT      => 0x05,
	ROT2     => 0x25,
	ROTr     => 0x45,
	ROT2r    => 0x65,
	ROTk     => 0x85,
	ROT2k    => 0xa5,
	ROTkr    => 0xc5,
	ROT2kr   => 0xe5,

	// DUP
	DUP      => 0x06,
	DUP2     => 0x26,
	DUPr     => 0x46,
	DUP2r    => 0x66,
	DUPk     => 0x86,
	DUP2k    => 0xa6,
	DUPkr    => 0xc6,
	DUP2kr   => 0xe6,

	// OVR
	OVR      => 0x07,
	OVR2     => 0x27,
	OVRr     => 0x47,
	OVR2r    => 0x67,
	OVRk     => 0x87,
	OVR2k    => 0xa7,
	OVRkr    => 0xc7,
	OVR2kr   => 0xe7,

	// ADD
	ADD      => 0x18,
	ADD2     => 0x38,
	ADDr     => 0x58,
	ADD2r    => 0x78,
	ADDk     => 0x98,
	ADD2k    => 0xb8,
	ADDkr    => 0xd8,
	ADD2kr   => 0xf8,

	// SUB
	SUB      => 0x19,
	SUB2     => 0x39,
	SUBr     => 0x59,
	SUB2r    => 0x79,
	SUBk     => 0x99,
	SUB2k    => 0xb9,
	SUBkr    => 0xd9,
	SUB2kr   => 0xf9,

	// MUL
	MUL      => 0x1a,
	MUL2     => 0x3a,
	MULr     => 0x5a,
	MUL2r    => 0x7a,
	MULk     => 0x9a,
	MUL2k    => 0xba,
	MULkr    => 0xda,
	MUL2kr   => 0xfa,

	// DIV
	DIV      => 0x1b,
	DIV2     => 0x3b,
	DIVr     => 0x5b,
	DIV2r    => 0x7b,
	DIVk     => 0x9b,
	DIV2k    => 0xbb,
	DIVkr    => 0xdb,
	DIV2kr   => 0xfb,

	// AND
	AND      => 0x1c,
	AND2     => 0x3c,
	ANDr     => 0x5c,
	AND2r    => 0x7c,
	ANDk     => 0x9c,
	AND2k    => 0xbc,
	ANDkr    => 0xdc,
	AND2kr   => 0xfc,

	// ORA (or)
	ORA      => 0x1d,
	ORA2     => 0x3d,
	ORAr     => 0x5d,
	ORA2r    => 0x7d,
	ORAk     => 0x9d,
	ORA2k    => 0xbd,
	ORAkr    => 0xdd,
	ORA2kr   => 0xfd,

	// EOR (xor)
	EOR      => 0x1e,
	EOR2     => 0x3e,
	EORr     => 0x5e,
	EOR2r    => 0x7e,
	EORk     => 0x9e,
	EOR2k    => 0xbe,
	EORkr    => 0xde,
	EOR2kr   => 0xfe,

	// JMP
	JMP      => 0x0c,
	JMP2     => 0x2c,
	JMPr     => 0x4c,
	JMP2r    => 0x6c,
	JMPk     => 0x8c,
	JMP2k    => 0xac,
	JMPkr    => 0xcc,
	JMP2kr   => 0xec,

	// SFT
	SFT      => 0x1f,
	SFT2     => 0x3f,
	SFTr     => 0x5f,
	SFT2r    => 0x7f,
	SFTk     => 0x9f,
	SFT2k    => 0xbf,
	SFTkr    => 0xdf,
	SFT2kr   => 0xff,

	// EQU
	EQU      => 0x08,
	EQU2     => 0x28,
	EQUr     => 0x48,
	EQU2r    => 0x68,
	EQUk     => 0x88,
	EQU2k    => 0xa8,
	EQUkr    => 0xc8,
	EQU2kr   => 0xe8,

	// NEQ
	NEQ      => 0x09,
	NEQ2     => 0x29,
	NEQr     => 0x49,
	NEQ2r    => 0x69,
	NEQk     => 0x89,
	NEQ2k    => 0xa9,
	NEQkr    => 0xc9,
	NEQ2kr   => 0xe9,

	// GTH
	GTH      => 0x0a,
	GTH2     => 0x2a,
	GTHr     => 0x4a,
	GTH2r    => 0x6a,
	GTHk     => 0x8a,
	GTH2k    => 0xaa,
	GTHkr    => 0xca,
	GTH2kr   => 0xea,

	// LTH
	LTH      => 0x0b,
	LTH2     => 0x2b,
	LTHr     => 0x4b,
	LTH2r    => 0x6b,
	LTHk     => 0x8b,
	LTH2k    => 0xab,
	LTHkr    => 0xcb,
	LTH2kr   => 0xeb,
}

/// Bytecode
#[derive(Debug, Clone)]
pub struct Bytecode {
	pub opcodes: Vec<Opcode>,
}
impl Bytecode {
	/// Write UXN bytecode into the specified buffer
	/// Buffer can be an output .rom file
	pub fn write_to(&self, buffer: &mut impl Write) -> std::io::Result<()> {
		for opcode in self.opcodes.iter() {
			match opcode {
				Opcode::Padding(p) => {
					let zeros = vec![0; *p as usize];
					buffer.write_all(&zeros)?;
				}
				opcode => {
					let byte: u8 = (*opcode).into();
					buffer.write_all(std::slice::from_ref(&byte))?;
				}
			}
		}

		Ok(())
	}
}
