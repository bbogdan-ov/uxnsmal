use std::{
	borrow::Borrow,
	fmt::{Debug, Display},
	ops::{Deref, DerefMut, Range},
	str::FromStr,
};

use crate::error::{self, Error, ErrorKind};

/// Range of text inside source code
#[derive(Default, Clone, Copy, PartialEq, Eq)]
pub struct Span {
	pub start: usize,
	pub end: usize,
	/// Line index
	pub line: usize,
	/// Byte index on the line
	pub col: usize,
}
impl Span {
	pub const fn new(start: usize, end: usize, line: usize, col: usize) -> Self {
		assert!(start <= end);
		Self {
			start,
			end,
			line,
			col,
		}
	}

	/// Create span starting at `from` and ending at `to`
	pub fn from_to(from: Span, to: Span) -> Self {
		if from.start < to.end {
			Self {
				start: from.start,
				end: to.end,
				line: from.line,
				col: from.col,
			}
		} else {
			Self {
				start: to.start,
				end: from.end,
				line: to.line,
				col: to.col,
			}
		}
	}

	/// Calculate range with specified length on the line
	/// This function counts each tab (`\t`) as 4 spaces i.e. 4 chars
	pub fn range_on_line(&self, line: &str) -> Range<usize> {
		let mut start = 0;
		let mut end = 0;

		let mut offset = 0;
		for (idx, ch) in line.char_indices() {
			// Calculate hightlight range
			if idx == self.col {
				start = offset;
			} else if idx == self.col + self.len() - 1 {
				end = offset;
			}

			if ch == '\t' {
				offset += 4;
			} else {
				offset += ch.len_utf8();
			}
		}

		start..end
	}

	pub fn into_range(self) -> Range<usize> {
		self.start..self.end
	}
	pub fn len(&self) -> usize {
		self.end - self.start
	}
	pub fn is_empty(&self) -> bool {
		self.start == self.end
	}
}
impl Display for Span {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}:{}", self.line + 1, self.col + 1)
	}
}
impl Debug for Span {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"Span({}..{}, {}:{})",
			self.start, self.end, self.line, self.col
		)
	}
}

/// Node with span
#[derive(Clone, Eq)]
pub struct Spanned<T>(pub T, pub Span);
impl<T: Debug> Debug for Spanned<T> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if f.alternate() {
			write!(f, "Spanned({:#?}, {:?})", self.0, self.1)
		} else {
			write!(f, "Spanned({:?}, {:?})", self.0, self.1)
		}
	}
}
impl<T> Borrow<T> for Spanned<T> {
	fn borrow(&self) -> &T {
		&self.0
	}
}
impl<T> Deref for Spanned<T> {
	type Target = T;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}
impl<T> DerefMut for Spanned<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}
impl<T: PartialEq> PartialEq for Spanned<T> {
	fn eq(&self, other: &Self) -> bool {
		self.0 == other.0
	}
}

pub fn is_symbol(ch: char) -> bool {
	ch.is_ascii_alphanumeric() || matches!(ch, '_' | '-' | '.')
}
pub fn is_number(s: &str, radix: u32) -> bool {
	for ch in s.chars() {
		if !ch.is_digit(radix) {
			return false;
		}
	}
	true
}

/// Keyword token kind
/// Reserved word type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Keyword {
	Func,
	Var,
	Const,
	Data,
	Loop,
	Jump,
	JumpIf,
}
impl FromStr for Keyword {
	type Err = ();

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		match s {
			"fun" => Ok(Self::Func),
			"var" => Ok(Self::Var),
			"const" => Ok(Self::Const),
			"data" => Ok(Self::Data),
			"loop" => Ok(Self::Loop),
			"jump" => Ok(Self::Jump),
			"jumpif" => Ok(Self::JumpIf),
			_ => Err(()),
		}
	}
}

/// Number token radix
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Radix {
	/// `0-9`
	Decimal,
	/// `0-9` `a-f`
	Hexadecimal,
	/// `0-1`
	Binary,
	/// `0-7`
	Octal,
}
impl Radix {
	pub fn into_num(self) -> u32 {
		match self {
			Self::Decimal => 10,
			Self::Hexadecimal => 16,
			Self::Binary => 2,
			Self::Octal => 8,
		}
	}
}
impl Display for Radix {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Decimal => write!(f, "decimal"),
			Self::Hexadecimal => write!(f, "hexadecimal"),
			Self::Binary => write!(f, "binary"),
			Self::Octal => write!(f, "octal"),
		}
	}
}

/// Token kind
/// Represents the type of a token
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
	/// Reserved word, like `fun`, `var`, `const` and others
	Keyword(Keyword),
	/// Any other non-keyword word
	Ident,
	/// Any numeric word
	/// Guaranteed to be a valid number, but NOT guaranteed that number will not overflow
	Number(Radix),
	/// Anything inside double (`"`) quotes
	String,
	/// Anything inside single (`'`) quotes
	Char,

	/// `(`
	OpenParen,
	/// `)`
	CloseParen,
	/// `{`
	OpenBrace,
	/// `}`
	CloseBrace,
	/// `&`
	Ampersand,
	/// `*`
	Asterisk,
	/// `$`
	Dollar,
	/// `@`
	AtSign,

	/// `--`
	DoubleDash,
	/// `->`
	ArrowRight,

	/// End of file
	Eof,
}
impl Display for TokenKind {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Keyword(_) => write!(f, "keyword"),
			Self::Ident => write!(f, "identifier"),
			Self::Number(r) => write!(f, "{r} number"),
			Self::String => write!(f, "string"),
			Self::Char => write!(f, "char"),

			Self::OpenParen => write!(f, "open paren"),
			Self::CloseParen => write!(f, "close paren"),
			Self::OpenBrace => write!(f, "open brace"),
			Self::CloseBrace => write!(f, "close brace"),
			Self::Ampersand => write!(f, "ampersand"),
			Self::Asterisk => write!(f, "asterisk"),
			Self::Dollar => write!(f, "dollar"),
			Self::AtSign => write!(f, "at sign"),

			Self::DoubleDash => write!(f, "double dash"),
			Self::ArrowRight => write!(f, "arrow right"),

			Self::Eof => write!(f, "end of file (eof)"),
		}
	}
}

/// Token
#[derive(Clone)]
pub struct Token {
	pub kind: TokenKind,
	pub span: Span,
}
impl Token {
	pub const fn new(kind: TokenKind, span: Span) -> Self {
		Self { kind, span }
	}
}
impl PartialEq for Token {
	fn eq(&self, other: &Self) -> bool {
		self.kind == other.kind
	}
}
impl PartialEq<TokenKind> for Token {
	fn eq(&self, other: &TokenKind) -> bool {
		self.kind == *other
	}
}
impl Debug for Token {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Token({:?}, {:?})", self.kind, self.span)
	}
}

/// Lexer
pub struct Lexer<'src> {
	source: &'src str,

	/// Current byte index
	cursor: usize,
	error_span: Span,

	/// Current line index
	line: usize,
	/// Current byte index on the current line
	col: usize,
}
impl<'src> Lexer<'src> {
	pub fn parse(source: &'src str) -> error::Result<Vec<Token>> {
		Self {
			source,

			cursor: 0,
			error_span: Span::default(),

			line: 0,
			col: 0,
		}
		.do_parse()
	}

	fn do_parse(mut self) -> error::Result<Vec<Token>> {
		let mut tokens = Vec::with_capacity(512);

		while let Some(ch) = self.peek_char() {
			self.error_span = self.span(self.cursor, self.cursor);

			if ch == '\n' {
				self.advance(1);
			} else if ch.is_whitespace() {
				self.advance(ch.len_utf8());
			} else {
				let rem = &self.source[self.cursor..];
				if rem.starts_with("//") {
					self.skip_comment();
				} else if rem.starts_with("/(") {
					self.skip_multiline_comment()?;
				} else {
					let token = self.next_token()?;
					tokens.push(token);
				}
			}
		}

		let len = self.source.len();
		tokens.push(Token::new(TokenKind::Eof, self.span(len, len)));

		Ok(tokens)
	}
	fn next_token(&mut self) -> error::Result<Token> {
		let remaining = &self.source[self.cursor..];

		macro_rules! match_start {
			($($prefix:expr => $token:expr,)* else => $else:expr$(,)?) => {
				if false { unreachable!() }
				$(else if remaining.starts_with($prefix) { $token })*
				else { $else }
			};
		}

		match_start! {
			"(" => self.next_punct(1, TokenKind::OpenParen),
			")" => self.next_punct(1, TokenKind::CloseParen),
			"{" => self.next_punct(1, TokenKind::OpenBrace),
			"}" => self.next_punct(1, TokenKind::CloseBrace),
			"&" => self.next_punct(1, TokenKind::Ampersand),
			"*" => self.next_punct(1, TokenKind::Asterisk),
			"$" => self.next_punct(1, TokenKind::Dollar),
			"@" => self.next_punct(1, TokenKind::AtSign),

			"--" => self.next_punct(2, TokenKind::DoubleDash),
			"->" => self.next_punct(2, TokenKind::ArrowRight),

			"\"" => self.next_string('"'),
			"'" => self.next_string('\''),

			else => {
				let token = self.next_number().or_else(|| self.next_symbol());
				match token {
					Some(token) => token,
					None => {
						let len = match self.peek_char() {
							Some(ch) => ch.len_utf8(),
							None => 0
						};
						self.advance(len);
						Err(self.error(ErrorKind::UnknownToken))
					},
				}
			}
		}
	}

	fn next_punct(&mut self, len: usize, kind: TokenKind) -> error::Result<Token> {
		let span = self.span(self.cursor, self.cursor + len);
		self.advance(len);
		Ok(Token::new(kind, span))
	}
	fn next_string(&mut self, quote: char) -> error::Result<Token> {
		let mut span = self.span(self.cursor, self.cursor);

		// Consume opening quote
		self.advance(1);

		while let Some(ch) = self.peek_char() {
			if ch == quote {
				break;
			} else if ch == '\\' {
				let rem = &self.source[self.cursor..];
				match rem.chars().nth(1) {
					Some('\n') | None => return Err(self.error(ErrorKind::UnclosedString)),
					Some(ch) => self.advance(ch.len_utf8()),
				}
			} else if ch == '\n' {
				return Err(self.error(ErrorKind::UnclosedString));
			}

			self.advance(ch.len_utf8());
		}

		// Consume closing quote
		self.advance(1);

		span.end = self.cursor;

		let kind = if quote == '"' {
			TokenKind::String
		} else {
			TokenKind::Char
		};

		Ok(Token::new(kind, span))
	}
	fn next_number(&mut self) -> Option<error::Result<Token>> {
		let ch = self.peek_char()?;
		if !ch.is_ascii_digit() {
			return None;
		}

		let rem = &self.source[self.cursor..];

		let radix: Radix;
		if rem.starts_with("0x") {
			radix = Radix::Hexadecimal;
		} else if rem.starts_with("0b") {
			radix = Radix::Binary;
		} else if rem.starts_with("0o") {
			radix = Radix::Octal;
		} else {
			radix = Radix::Decimal;
		}

		let mut span = self.span(self.cursor, self.cursor);
		self.skip_while(|c| c.is_ascii_alphanumeric());
		span.end = self.cursor;

		let s = match radix {
			Radix::Decimal => &self.source[span.into_range()],
			_ => &self.source[span.start + 2..span.end], // exclude 0x prefix
		};
		if s.is_empty() || !is_number(s, radix.into_num()) {
			return Some(Err(self.error(ErrorKind::BadNumber(radix))));
		}

		let token = Token::new(TokenKind::Number(radix), span);
		Some(Ok(token))
	}
	fn next_symbol(&mut self) -> Option<error::Result<Token>> {
		let mut span = self.span(self.cursor, self.cursor);
		self.skip_while(is_symbol);
		span.end = self.cursor;

		if span.is_empty() {
			return None;
		}

		let s = &self.source[span.into_range()];
		let kind = match Keyword::from_str(s) {
			Ok(kw) => TokenKind::Keyword(kw),
			Err(_) => TokenKind::Ident,
		};

		Some(Ok(Token::new(kind, span)))
	}

	fn skip_comment(&mut self) {
		// Consume //
		self.advance(2);
		self.skip_while(|c| c != '\n');
	}
	fn skip_multiline_comment(&mut self) -> error::Result<()> {
		// Consume /(
		self.advance(2);

		while let Some(ch) = self.peek_char() {
			let remaining = &self.source[self.cursor..];
			if remaining.starts_with(")/") {
				// Consume )/
				self.advance(2);
				return Ok(());
			}

			self.advance(ch.len_utf8());
		}

		Err(self.error(ErrorKind::UnclosedComment))
	}
	fn skip_while(&mut self, cond: impl Fn(char) -> bool) {
		while let Some(ch) = self.peek_char() {
			if !cond(ch) {
				break;
			}

			self.advance(ch.len_utf8());
		}
	}

	/// Returns current char without consuming
	fn peek_char(&self) -> Option<char> {
		self.source.get(self.cursor..)?.chars().next()
	}

	fn span(&self, start: usize, end: usize) -> Span {
		Span::new(start, end, self.line, self.col)
	}
	fn error(&mut self, kind: ErrorKind) -> Error {
		self.error_span.end = self.cursor;
		Error::new(kind, self.error_span)
	}
	/// Move cursor by N bytes
	fn advance(&mut self, n: usize) {
		if self.peek_char().is_some_and(|c| c == '\n') {
			self.line += 1;
			self.col = 0;
		} else {
			self.col += n;
		}

		self.cursor += n;
	}
}
