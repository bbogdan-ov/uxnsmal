use std::{num::IntErrorKind, str::FromStr};

use crate::{
	ast::{Ast, ConstDef, DataDef, Definition, FuncArgs, FuncDef, Name, NodeOp, VarDef},
	error::{self, Error, ErrorKind},
	lexer::{Keyword, Radix, Span, Spanned, Token, TokenKind},
	program::{Intrinsic, IntrinsicMode},
	typechecker::Type,
};

#[inline(always)]
fn escape_char(ch: char, span: Span) -> error::Result<char> {
	match ch {
		'0' => Ok('\0'),
		'a' => Ok('\x07'),
		'b' => Ok('\x08'),
		't' => Ok('\t'),
		'n' => Ok('\n'),
		'v' => Ok('\x0B'),
		'f' => Ok('\x0C'),
		'r' => Ok('\r'),
		'\\' => Ok('\\'),
		'\'' => Ok('\''),
		'"' => Ok('"'),
		ch => Err(ErrorKind::UnknownCharEscape(ch).err(span)),
	}
}

/// AST parser
pub struct Parser<'a> {
	pub source: &'a str,
	pub tokens: &'a [Token],
	pub ast: Ast,

	/// Current token index
	pub cursor: usize,
}
impl<'a> Parser<'a> {
	pub fn parse(source: &'a str, tokens: &'a [Token]) -> error::Result<Ast> {
		// <= 1 because Eof token is always here
		if tokens.len() <= 1 {
			return Err(Error::everywhere(ErrorKind::EmptyFile));
		}

		let mut parser = Self {
			source,
			tokens,
			ast: Ast::default(),

			cursor: 0,
		};

		parser.parse_tokens()?;
		Ok(parser.ast)
	}

	fn parse_tokens(&mut self) -> error::Result<()> {
		while self.cursor < self.tokens.len() {
			let token = self.next();
			match token.kind {
				TokenKind::Keyword(Keyword::Func) => {
					let func = self.parse_func()?;
					self.ast.definitions.push(func);
				}
				TokenKind::Keyword(Keyword::Var) => {
					let var = self.parse_var()?;
					self.ast.definitions.push(var);
				}
				TokenKind::Keyword(Keyword::Const) => {
					let cnst = self.parse_const()?;
					self.ast.definitions.push(cnst);
				}
				TokenKind::Keyword(Keyword::Data) => {
					let data = self.parse_data()?;
					self.ast.definitions.push(data);
				}

				TokenKind::Eof => break,

				_ => return Err(ErrorKind::UnexpectedToken.err(token.span)),
			}
		}

		Ok(())
	}

	// ==============================
	// Parsing
	// ==============================

	fn parse_func(&mut self) -> error::Result<Spanned<Definition>> {
		let name = self.parse_name()?;
		let span = self.span();
		let args = self.parse_func_args()?;
		let body = self.parse_body()?;

		let func = FuncDef { name, args, body };
		Ok(Spanned(Definition::Function(func), span))
	}
	fn parse_func_args(&mut self) -> error::Result<FuncArgs> {
		self.expect(TokenKind::OpenParen)?;

		if self.optional(TokenKind::ArrowRight).is_some() {
			self.expect(TokenKind::CloseParen)?;
			return Ok(FuncArgs::Vector);
		}

		let inputs = self.parse_seq_of(TokenKind::Ident, Self::parse_type)?;
		self.expect(TokenKind::DoubleDash)?;
		let outputs = self.parse_seq_of(TokenKind::Ident, Self::parse_type)?;

		self.expect(TokenKind::CloseParen)?;

		Ok(FuncArgs::Proc { inputs, outputs })
	}

	fn parse_var(&mut self) -> error::Result<Spanned<Definition>> {
		let typ = self.parse_type()?;
		let name = self.parse_name()?;
		let span = self.span();

		let var = VarDef { name, typ };
		Ok(Spanned(Definition::Variable(var), span))
	}

	fn parse_const(&mut self) -> error::Result<Spanned<Definition>> {
		let typ = self.parse_type()?;
		let name = self.parse_name()?;
		let span = self.span();

		let body = self.parse_body()?;

		let cnst = ConstDef { name, typ, body };
		Ok(Spanned(Definition::Constant(cnst), span))
	}

	fn parse_data(&mut self) -> error::Result<Spanned<Definition>> {
		let name = self.parse_name()?;
		let span = self.span();
		let body = self.parse_body()?;

		let data = DataDef { name, body };
		Ok(Spanned(Definition::Data(data), span))
	}

	/// Parse operations inside `{ ... }`
	fn parse_body(&mut self) -> error::Result<Box<[Spanned<NodeOp>]>> {
		self.expect(TokenKind::OpenBrace)?;

		let mut nodes: Vec<Spanned<NodeOp>> = Vec::with_capacity(64);
		let mut brace_depth: u16 = 0;

		while self.cursor < self.tokens.len() {
			let cur_token = self.peek();
			match cur_token.kind {
				TokenKind::OpenBrace => {
					self.advance();
					brace_depth += 1;
				}
				TokenKind::CloseBrace => {
					if brace_depth == 0 {
						break;
					}

					self.advance();
					brace_depth -= 1;
				}

				TokenKind::Eof => break,

				_ => nodes.push(self.parse_op()?),
			}
		}

		self.expect(TokenKind::CloseBrace)?;

		Ok(nodes.into_boxed_slice())
	}

	fn parse_op(&mut self) -> error::Result<Spanned<NodeOp>> {
		let token = self.next();
		let start_span = token.span;

		fn parse_num(source: &str, radix: Radix, span: Span) -> error::Result<u16> {
			let slice = match radix {
				Radix::Decimal => &source[span.into_range()],
				_ => &source[span.start + 2..span.end], // exclude 0x prefix
			};

			match u16::from_str_radix(slice, radix.into_num()) {
				Ok(num) => Ok(num),
				Err(e) => match e.kind() {
					IntErrorKind::PosOverflow => Err(ErrorKind::NumberIsTooLarge.err(span)),
					_ => unreachable!("number tokens must be valid u16 numbers, but got error {e}"),
				},
			}
		}

		let (op, end_span): (NodeOp, Span) = match token.kind {
			// Number literal
			TokenKind::Number(radix) => {
				let span = token.span;
				let num = parse_num(self.source, radix, span)?;
				let op = match self.optional(TokenKind::Asterisk) {
					Some(_) => NodeOp::Short(num),
					None if num > 255 => return Err(ErrorKind::ByteIsTooLarge.err(span)),
					None => NodeOp::Byte(num as u8),
				};
				(op, self.span())
			}
			// Char literal
			TokenKind::Char => {
				let span = token.span;
				let mut range = span.into_range();
				range.start += 1; // exclude opening quote
				range.end -= 1; // exclude closing quote
				if range.is_empty() {
					return Err(ErrorKind::InvalidCharLiteral.err(span));
				}

				let slice = &self.source[range];
				let mut byte = 0;
				let mut chars = slice.chars();
				let mut escape = false;
				for ch in chars.by_ref() {
					if ch == '\\' && !escape {
						escape = true;
						continue;
					}

					byte = if escape {
						escape_char(ch, span)? as u8
					} else {
						ch as u8
					};
					break;
				}

				if chars.next().is_some() {
					return Err(ErrorKind::InvalidCharLiteral.err(span));
				}

				(NodeOp::Byte(byte), self.span())
			}
			TokenKind::String => {
				let span = token.span;
				let mut range = span.into_range();
				range.start += 1; // exclude opening quote
				range.end -= 1; // exclude closing quote

				let mut string = String::with_capacity(128);

				let slice = &self.source[range];
				let mut escape = false;
				for mut ch in slice.chars() {
					if ch == '\\' && !escape {
						escape = true;
						continue;
					}

					if escape {
						ch = escape_char(ch, span)?;
						escape = false;
					}

					string.push(ch);
				}

				(NodeOp::String(string.into_boxed_str()), self.span())
			}

			// Padding
			TokenKind::Dollar => {
				let next_token = self.next();
				let span = next_token.span;
				match next_token.kind {
					TokenKind::Number(radix) => {
						let num = parse_num(self.source, radix, span)?;
						(NodeOp::Padding(num), self.span())
					}
					found => {
						return Err(ErrorKind::ExpectedNumber { found }.err(span));
					}
				}
			}

			// Intrinsics or other symbols
			TokenKind::Ident => {
				let op = match self.parse_intrinsic() {
					Some((kind, mode)) => NodeOp::Intrinsic(kind, mode),
					None => NodeOp::Symbol(Name::new(self.slice())),
				};
				(op, self.span())
			}

			// Pointer to a symbol
			TokenKind::Ampersand => {
				let name = self.parse_name()?;
				(NodeOp::PtrTo(name), self.span())
			}

			// Loop block
			TokenKind::Keyword(Keyword::Loop) => {
				self.expect(TokenKind::AtSign)?;
				let label = self.parse_name()?;
				let span = self.span();
				let body = self.parse_body()?;
				(
					NodeOp::Block {
						looping: true,
						label: Spanned(label, span),
						body,
					},
					span,
				)
			}

			// Block
			TokenKind::AtSign => {
				let label = self.parse_name()?;
				let span = self.span();
				let body = self.parse_body()?;
				(
					NodeOp::Block {
						looping: false,
						label: Spanned(label, span),
						body,
					},
					span,
				)
			}

			// Jump
			TokenKind::Keyword(kw @ Keyword::Jump) | TokenKind::Keyword(kw @ Keyword::JumpIf) => {
				self.expect(TokenKind::AtSign)?;
				let label = self.parse_name()?;
				let span = self.span();
				let conditional = kw == Keyword::JumpIf;

				(
					NodeOp::Jump {
						label: Spanned(label, span),
						conditional,
					},
					self.span(),
				)
			}

			// Bind
			TokenKind::ArrowRight => {
				self.expect(TokenKind::OpenParen)?;
				let names = self.parse_seq_of(TokenKind::Ident, Self::parse_spanned_name)?;
				self.expect(TokenKind::CloseParen)?;
				(NodeOp::Bind(names), self.span())
			}

			_ => return Err(ErrorKind::UnexpectedToken.err(start_span)),
		};

		Ok(Spanned(op, Span::from_to(start_span, end_span)))
	}
	// Examples:
	//     add
	//     inc-2
	//     swap-rk
	//     over-2rk
	fn parse_intrinsic(&mut self) -> Option<(Intrinsic, IntrinsicMode)> {
		let slice = self.slice();

		match slice.split_once('-') {
			Some((name, flags)) => {
				let kind = Intrinsic::from_str(name).ok()?;

				// SHORT mode is determined at the typecheck stage based on intrinsic inputs
				let mut mode = IntrinsicMode::NONE;
				for ch in flags.chars() {
					match ch {
						'r' => mode |= IntrinsicMode::RETURN,
						'k' => mode |= IntrinsicMode::KEEP,
						_ => return None,
					}
				}

				Some((kind, mode))
			}
			None => {
				let kind = Intrinsic::from_str(slice).ok()?;
				Some((kind, IntrinsicMode::NONE))
			}
		}
	}

	fn parse_type(&mut self) -> error::Result<Spanned<Type>> {
		let token = self.expect(TokenKind::Ident)?;
		let start = token.span;

		let typ = match self.slice() {
			"byte" => Type::Byte,
			"short" => Type::Short,
			"ptr" => Type::BytePtr(Box::new(self.parse_type()?.0)),
			"ptr2" => Type::ShortPtr(Box::new(self.parse_type()?.0)),
			"funptr" => {
				let sig = self.parse_func_args()?.to_signature();
				Type::FuncPtr(sig)
			}
			_ => return Err(ErrorKind::NoCustomTypesYet.err(start)),
		};

		let end = self.span();

		Ok(Spanned(typ, Span::from_to(start, end)))
	}

	fn parse_name(&mut self) -> error::Result<Name> {
		self.expect(TokenKind::Ident)?;
		Ok(Name::new(self.slice()))
	}
	fn parse_spanned_name(&mut self) -> error::Result<Spanned<Name>> {
		self.expect(TokenKind::Ident)?;
		Ok(Spanned(Name::new(self.slice()), self.span()))
	}

	fn parse_seq_of<T>(
		&mut self,
		kind: TokenKind,
		parse: fn(&mut Parser<'a>) -> error::Result<T>,
	) -> error::Result<Box<[T]>> {
		if self.peek().kind != kind {
			return Ok(Box::default());
		}

		let mut nodes = Vec::with_capacity(16);
		nodes.push(parse(self)?);

		loop {
			let cur_token = self.peek();
			if cur_token.kind != kind {
				break;
			}

			nodes.push(parse(self)?);
		}

		Ok(nodes.into_boxed_slice())
	}

	// ==============================
	// Helper functions
	// ==============================

	/// Returns `Ok(())` and consume the current token if its kind is equal to the specified one,
	/// otherwise returns `Err`
	fn expect(&mut self, kind: TokenKind) -> error::Result<&Token> {
		let cur_token = self.peek();
		if cur_token.kind == kind {
			Ok(self.next())
		} else {
			let kind = ErrorKind::Expected {
				expected: kind,
				found: cur_token.kind,
			};
			Err(kind.err(cur_token.span))
		}
	}
	/// Returns `Some(())` and consume the current token if its kind is equal to the specified one
	fn optional(&mut self, kind: TokenKind) -> Option<&Token> {
		if self.peek().kind == kind {
			Some(self.next())
		} else {
			None
		}
	}

	/// Returns and consumes the current token
	pub fn next(&mut self) -> &Token {
		let token = &self.tokens[self.cursor];
		self.cursor += 1;
		token
	}
	/// Returns the current token without consuming
	pub fn peek(&mut self) -> &Token {
		&self.tokens[self.cursor]
	}
	/// Move cursor to the next token
	pub fn advance(&mut self) {
		self.cursor += 1;
	}
	/// Returns previous token string span
	pub fn span(&self) -> Span {
		if self.cursor == 0 {
			Span::default()
		} else {
			self.tokens[self.cursor - 1].span
		}
	}
	/// Returns previous token string slice
	pub fn slice(&self) -> &str {
		&self.source[self.span().into_range()]
	}
}
