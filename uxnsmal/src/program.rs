use std::{
	collections::BTreeMap,
	fmt::{Debug, Display},
	hash::Hash,
	str::FromStr,
};

use crate::typechecker::UniqueName;

bitflags::bitflags! {
	/// Intrinsic mode
	#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
	pub struct IntrinsicMode: u8 {
		const NONE = 0;
		const SHORT = 1 << 1;
		const KEEP = 1 << 2;
		const RETURN = 1 << 3;
	}
}

/// Address kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddrKind {
	Unknown,
	/// Absolute byte
	AbsByte,
	/// Absolute short
	AbsShort,
}

/// Operation intrinsic kind
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intrinsic {
	Add,
	Sub,
	Mul,
	Div,
	Inc,
	Shift,

	And,
	Or,
	Xor,

	Eq,
	Neq,
	Gth,
	Lth,

	Pop,
	Swap,
	Nip,
	Rot,
	Dup,
	Over,

	Load(AddrKind),
	Store(AddrKind),

	Input,
	Input2,
	Output,
}
impl FromStr for Intrinsic {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		match s {
			"add" => Ok(Self::Add),
			"sub" => Ok(Self::Sub),
			"mul" => Ok(Self::Mul),
			"div" => Ok(Self::Div),
			"inc" => Ok(Self::Inc),
			"shift" => Ok(Self::Shift),

			"and" => Ok(Self::And),
			"or" => Ok(Self::Or),
			"xor" => Ok(Self::Xor),

			"eq" => Ok(Self::Eq),
			"neq" => Ok(Self::Neq),
			"gth" => Ok(Self::Gth),
			"lth" => Ok(Self::Lth),

			"pop" => Ok(Self::Pop),
			"swap" => Ok(Self::Swap),
			"nip" => Ok(Self::Nip),
			"rot" => Ok(Self::Rot),
			"dup" => Ok(Self::Dup),
			"over" => Ok(Self::Over),

			"load" => Ok(Self::Load(AddrKind::Unknown)),
			"store" => Ok(Self::Store(AddrKind::Unknown)),

			"input" => Ok(Self::Input),
			"input2" => Ok(Self::Input2),
			"output" => Ok(Self::Output),

			_ => Err(()),
		}
	}
}
impl Display for Intrinsic {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Add => write!(f, "add"),
			Self::Sub => write!(f, "sub"),
			Self::Mul => write!(f, "mul"),
			Self::Div => write!(f, "div"),
			Self::Inc => write!(f, "inc"),
			Self::Shift => write!(f, "shift"),

			Self::And => write!(f, "and"),
			Self::Or => write!(f, "or"),
			Self::Xor => write!(f, "xor"),

			Self::Eq => write!(f, "eq"),
			Self::Neq => write!(f, "neq"),
			Self::Gth => write!(f, "gth"),
			Self::Lth => write!(f, "lth"),

			Self::Pop => write!(f, "pop"),
			Self::Swap => write!(f, "swap"),
			Self::Nip => write!(f, "nip"),
			Self::Rot => write!(f, "rot"),
			Self::Dup => write!(f, "dup"),
			Self::Over => write!(f, "over"),

			Self::Load(_) => write!(f, "load"),
			Self::Store(_) => write!(f, "store"),

			Self::Input => write!(f, "input"),
			Self::Input2 => write!(f, "input2"),
			Self::Output => write!(f, "output"),
		}
	}
}

/// Operation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
	/// Push byte literal onto the stack
	Byte(u8),
	/// Push short literal onto the stack
	Short(u16),
	/// Put N number of zero bytes into ROM
	Padding(u16),

	/// Intrinsic call
	Intrinsic(Intrinsic, IntrinsicMode),
	/// Function call
	Call(UniqueName),
	/// Constant use
	ConstUse(UniqueName),

	/// Push absolute byte address of a symbol
	ByteAddrOf(UniqueName),
	/// Push absolute short address of a symbol
	ShortAddrOf(UniqueName),

	Label(UniqueName),
	/// Jump to a label
	Jump(UniqueName),
	/// Conditionally jump to a label
	JumpIf(UniqueName),
}

/// Intermediate function definition
#[derive(Debug, Clone)]
pub struct Function {
	pub is_vector: bool,
	pub body: Box<[Op]>,
}

/// Intermediate variable definition
#[derive(Debug, Clone)]
pub struct Variable {
	pub size: u8,
}

/// Intermediate constant definition
#[derive(Debug, Clone)]
pub struct Constant {
	pub body: Box<[Op]>,
}

/// Intermediate constant definition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Data {
	pub body: Box<[u8]>,
}

/// Program
///
/// Intermediate representation of the program
#[derive(Debug, Default)]
pub struct Program {
	pub reset_func: Option<(UniqueName, Function)>,
	pub funcs: BTreeMap<UniqueName, Function>,
	pub vars: BTreeMap<UniqueName, Variable>,
	pub consts: BTreeMap<UniqueName, Constant>,
	pub datas: BTreeMap<UniqueName, Data>,
}
