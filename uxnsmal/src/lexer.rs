use std::{
	borrow::Borrow,
	fmt::{Debug, Display},
	num::IntErrorKind,
	ops::Range,
	str::FromStr,
};

use crate::{
	error::{self, Error},
	program::{IntrMode, Intrinsic},
};

// TODO: do something with multiline spans (spans with `start` on one line and `end` on another)
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

	/// Calculate span range on the specified string
	/// This function counts each tab (`\t`) as 4 characters
	pub fn range_on_line(&self, line: &str) -> Range<usize> {
		let mut start = 0;
		let mut end = 0;

		let mut offset = 0;
		for (idx, ch) in line.char_indices() {
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
			self.start,
			self.end,
			self.line + 1,
			self.col + 1
		)
	}
}

/// Node with span
#[derive(Clone, Eq)]
pub struct Spanned<T> {
	pub x: T,
	pub span: Span,
}
impl<T> Spanned<T> {
	pub fn new(x: T, span: Span) -> Self {
		Self { x, span }
	}
}
impl<T: Debug> Debug for Spanned<T> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if f.alternate() {
			write!(f, "Spanned({:#?}, {:?})", self.x, self.span)
		} else {
			write!(f, "Spanned({:?}, {:?})", self.x, self.span)
		}
	}
}
impl<T> Borrow<T> for Spanned<T> {
	fn borrow(&self) -> &T {
		&self.x
	}
}
impl<T: PartialEq> PartialEq for Spanned<T> {
	fn eq(&self, other: &Self) -> bool {
		self.x == other.x
	}
}

pub fn is_symbol(ch: char) -> bool {
	ch.is_ascii_alphanumeric() || matches!(ch, '_' | '-')
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
	Return,
	If,
	ElseIf,
	Else,
	While,
	As,
	Type,
	Enum,
	Untyped,
	Struct,
	Rom,
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
			"return" => Ok(Self::Return),
			"if" => Ok(Self::If),
			"elif" => Ok(Self::ElseIf),
			"else" => Ok(Self::Else),
			"while" => Ok(Self::While),
			"as" => Ok(Self::As),
			"type" => Ok(Self::Type),
			"enum" => Ok(Self::Enum),
			"untyped" => Ok(Self::Untyped),
			"struct" => Ok(Self::Struct),
			"rom" => Ok(Self::Rom),
			_ => Err(()),
		}
	}
}
impl Display for Keyword {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Func => write!(f, "func"),
			Self::Var => write!(f, "var"),
			Self::Const => write!(f, "const"),
			Self::Data => write!(f, "data"),
			Self::Loop => write!(f, "loop"),
			Self::Jump => write!(f, "jump"),
			Self::If => write!(f, "if"),
			Self::ElseIf => write!(f, "elif"),
			Self::Else => write!(f, "else"),
			Self::While => write!(f, "while"),
			Self::Return => write!(f, "return"),
			Self::As => write!(f, "as"),
			Self::Type => write!(f, "type"),
			Self::Enum => write!(f, "enum"),
			Self::Untyped => write!(f, "untyped"),
			Self::Struct => write!(f, "struct"),
			Self::Rom => write!(f, "rom"),
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
	// Intrinsic
	Intrinsic(Intrinsic, IntrMode),
	/// Any word starting with '@'
	Label,
	/// Any other non-keyword word
	Ident,
	/// Any numeric word
	/// Guaranteed to be a valid unsigned 16-bit integer
	Number(u16, Radix),
	/// Anything inside double (`"`) quotes
	String,
	/// Anything inside single (`'`) quotes
	Char,
	/// Anything after `//` or inside `/* ... */`
	Comment,

	/// `(`
	OpenParen,
	/// `)`
	CloseParen,
	/// `{`
	OpenBrace,
	/// `}`
	CloseBrace,
	/// `[`
	OpenBracket,
	/// `]`
	CloseBracket,
	/// `&`
	Ampersand,
	/// `*`
	Asterisk,
	/// `$`
	Dollar,
	/// `^`
	Hat,
	/// `:`
	Colon,
	/// `.`
	Dot,

	/// `--`
	DoubleDash,
	/// `->`
	ArrowRight,
	/// `[]`
	Box,

	/// End of file
	Eof,
}
impl Display for TokenKind {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Keyword(k) => write!(f, "\"{k}\" keyword"),
			Self::Intrinsic(_, _) => write!(f, "intrinsic"),
			Self::Label => write!(f, "label"),
			Self::Ident => write!(f, "identifier"),
			Self::Number(_, r) => write!(f, "{r} number"),
			Self::String => write!(f, "string"),
			Self::Char => write!(f, "char"),
			Self::Comment => write!(f, "comment"),

			Self::OpenParen => write!(f, "\"(\""),
			Self::CloseParen => write!(f, "\")\""),
			Self::OpenBrace => write!(f, "\"{{\""),
			Self::CloseBrace => write!(f, "\"}}\""),
			Self::OpenBracket => write!(f, "\"[\""),
			Self::CloseBracket => write!(f, "\"]\""),
			Self::Ampersand => write!(f, "\"&\""),
			Self::Asterisk => write!(f, "\"*\""),
			Self::Dollar => write!(f, "\"$\""),
			Self::Hat => write!(f, "\"^\""),
			Self::Colon => write!(f, "\":\""),
			Self::Dot => write!(f, "\".\""),

			Self::DoubleDash => write!(f, "\"--\""),
			Self::ArrowRight => write!(f, "\"->\""),
			Self::Box => write!(f, "\"[]\""),

			Self::Eof => write!(f, "end of file"),
		}
	}
}

fn parse_num(s: &str, radix: Radix, span: Span) -> error::Result<u16> {
	match u16::from_str_radix(s, radix.into_num()) {
		Ok(num) => Ok(num),
		Err(e) => match e.kind() {
			IntErrorKind::Empty => Err(Error::InvalidNumber(radix, span)),
			IntErrorKind::InvalidDigit => Err(Error::InvalidNumber(radix, span)),
			IntErrorKind::PosOverflow => Err(Error::NumberIsTooBig(span)),
			IntErrorKind::NegOverflow => Err(Error::InvalidNumber(radix, span)),
			IntErrorKind::Zero => unreachable!("u16 can be == 0"),
			_ => unreachable!("no more errors in rust 1.88.0"),
		},
	}
}

fn parse_intrinsic(s: &str) -> Option<(Intrinsic, IntrMode)> {
	let Some((name, flags)) = s.split_once('-') else {
		let kind = Intrinsic::from_str(s).ok()?;
		return Some((kind, IntrMode::NONE));
	};

	let kind = Intrinsic::from_str(name).ok()?;

	let mut mode = IntrMode::NONE;
	for ch in flags.chars() {
		match ch {
			'r' if !mode.contains(IntrMode::RETURN) => mode |= IntrMode::RETURN,
			'k' if !mode.contains(IntrMode::KEEP) => mode |= IntrMode::KEEP,
			_ => return None,
		}
	}

	Some((kind, mode))
}

/// Token
#[derive(Debug, Clone, Copy, Eq)]
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

// TODO: handle non-ASCII characters
// Currently these characters produce unknown results

/// Lexer
pub struct Lexer<'src> {
	source: &'src str,

	/// Current byte index
	cursor: usize,
	incomplete_error_span: Span,

	/// Current line index
	line: usize,
	/// Current byte index on the current line
	col: usize,

	/// Skip first N bytes of the source code
	pub skip_n: usize,
}
impl<'src> Lexer<'src> {
	fn new(source: &'src str) -> Self {
		Self {
			source,

			cursor: 0,
			incomplete_error_span: Span::default(),

			line: 0,
			col: 0,

			skip_n: 0,
		}
	}

	pub fn lex(source: &'src str) -> error::Result<Vec<Token>> {
		Self::new(source).do_lex()
	}
	pub fn lex_with_skip(source: &'src str, skip_n: usize) -> error::Result<Vec<Token>> {
		let mut lexer = Self::new(source);
		lexer.skip_n = skip_n;
		lexer.do_lex()
	}

	fn do_lex(mut self) -> error::Result<Vec<Token>> {
		let mut tokens = Vec::with_capacity(512);

		while let Some(ch) = self.peek_char() {
			self.incomplete_error_span = self.span(self.cursor, self.cursor);

			if self.skip_n > 0 {
				self.advance(1);
				self.skip_n -= 1;
				continue;
			}

			if ch == '\n' {
				self.advance(1);
			} else if ch.is_whitespace() {
				self.advance(ch.len_utf8());
			} else {
				let token = self.next_token()?;
				tokens.push(token);
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
			"//" => self.next_comment(),
			"/*" => self.next_multiline_comment(),

			"--" => self.next_punct(2, TokenKind::DoubleDash),
			"->" => self.next_punct(2, TokenKind::ArrowRight),
			"[]" => self.next_punct(2, TokenKind::Box),

			"(" => self.next_punct(1, TokenKind::OpenParen),
			")" => self.next_punct(1, TokenKind::CloseParen),
			"{" => self.next_punct(1, TokenKind::OpenBrace),
			"}" => self.next_punct(1, TokenKind::CloseBrace),
			"[" => self.next_punct(1, TokenKind::OpenBracket),
			"]" => self.next_punct(1, TokenKind::CloseBracket),
			"&" => self.next_punct(1, TokenKind::Ampersand),
			"*" => self.next_punct(1, TokenKind::Asterisk),
			"$" => self.next_punct(1, TokenKind::Dollar),
			"^" => self.next_punct(1, TokenKind::Hat),
			":" => self.next_punct(1, TokenKind::Colon),
			"." => self.next_punct(1, TokenKind::Dot),

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
						Err(Error::UnknownToken(self.error_span()))
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
					Some('\n') | None => return Err(Error::UnclosedString(self.error_span())),
					Some(ch) => self.advance(ch.len_utf8()),
				}
			} else if ch == '\n' {
				return Err(Error::UnclosedString(self.error_span()));
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

		match parse_num(s, radix, span) {
			Ok(num) => {
				let token = Token::new(TokenKind::Number(num, radix), span);
				Some(Ok(token))
			}
			Err(e) => Some(Err(e)),
		}
	}
	fn next_symbol(&mut self) -> Option<error::Result<Token>> {
		let is_label = self.peek_char()? == '@';
		if is_label {
			self.advance(1);
		}

		let mut span = self.span(self.cursor, self.cursor);
		self.skip_while(is_symbol);
		span.end = self.cursor;

		if span.is_empty() {
			return None;
		}

		let slice = &self.source[span.into_range()];

		let kind = if is_label {
			// Try parse label
			span.start -= 1;
			span.col -= 1;
			TokenKind::Label
		} else if let Ok(kw) = Keyword::from_str(slice) {
			// Try parse keyword
			TokenKind::Keyword(kw)
		} else if let Some((intr, mode)) = parse_intrinsic(slice) {
			// Try parse intrinsic
			TokenKind::Intrinsic(intr, mode)
		} else {
			// Identifier
			TokenKind::Ident
		};

		Some(Ok(Token::new(kind, span)))
	}

	fn next_comment(&mut self) -> error::Result<Token> {
		// Consume //
		self.advance(2);
		let mut span = self.span(self.cursor, self.cursor);
		self.skip_while(|c| c != '\n');
		span.end = self.cursor; // -1 to exclude '\n'

		return Ok(Token::new(TokenKind::Comment, span));
	}
	fn next_multiline_comment(&mut self) -> error::Result<Token> {
		// Consume /(
		self.advance(2);
		let mut span = self.span(self.cursor, self.cursor);

		while let Some(ch) = self.peek_char() {
			let remaining = &self.source[self.cursor..];
			if remaining.starts_with("*/") {
				span.end = self.cursor;
				// Consume )/
				self.advance(2);
				return Ok(Token::new(TokenKind::Comment, span));
			}

			self.advance(ch.len_utf8());
		}

		Err(Error::UnclosedComment(self.error_span()))
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
	fn error_span(&mut self) -> Span {
		self.incomplete_error_span.end = self.cursor;
		self.incomplete_error_span
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
