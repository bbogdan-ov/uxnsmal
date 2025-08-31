use std::{num::IntErrorKind, str::FromStr};

use crate::{
	ast::{Ast, ConstDef, DataDef, Definition, Expr, FuncArgs, FuncDef, Name, Node, VarDef},
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
	source: &'a str,
	tokens: &'a [Token],
	ast: Ast,

	/// Current token index
	cursor: usize,
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
			let token = self.peek();
			match token.kind {
				TokenKind::Eof => break,

				_ => {
					let node = self.parse_next_node()?;
					self.ast.nodes.push(node);
				}
			}
		}

		Ok(())
	}

	// ==============================
	// Parsing
	// ==============================

	// TODO: add hint 'while parsing' (when an error occurs) to the token that started node parsing
	fn parse_next_node(&mut self) -> error::Result<Spanned<Node>> {
		let token = self.next();
		let start_span = token.span;

		fn parse_num(source: &str, radix: Radix, span: Span) -> error::Result<u16> {
			let slice = match radix {
				Radix::Decimal => &source[span.into_range()],
				_ => &source[span.start + 2..span.end], // exclude 0x prefix
			};

			// TODO: make lexer to NOT guarantee number tokens validity, check it only here
			match u16::from_str_radix(slice, radix.into_num()) {
				Ok(num) => Ok(num),
				Err(e) => match e.kind() {
					IntErrorKind::PosOverflow => Err(ErrorKind::NumberIsTooLarge.err(span)),
					_ => unreachable!(
						"number tokens must be valid u16 numbers, but got an error for {slice:?}: {e}"
					),
				},
			}
		}

		let (node, node_span): (Node, Span) = match token.kind {
			TokenKind::Keyword(Keyword::Func) => self.parse_func()?,
			TokenKind::Keyword(Keyword::Var) => self.parse_var()?,
			TokenKind::Keyword(Keyword::Const) => self.parse_const()?,
			TokenKind::Keyword(Keyword::Data) => self.parse_data()?,

			// Number literal
			TokenKind::Number(radix) => {
				let num = parse_num(self.source, radix, start_span)?;
				let expr = match self.optional(TokenKind::Asterisk) {
					Some(_) => Expr::Short(num),
					None if num > 255 => return Err(ErrorKind::ByteIsTooLarge.err(start_span)),
					None => Expr::Byte(num as u8),
				};
				(expr.into(), Span::from_to(start_span, self.span()))
			}
			// Char literal
			// TODO: add ability to mark char as short just like with numbers
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

				(Expr::Byte(byte).into(), span)
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

				(Expr::String(string.into_boxed_str()).into(), span)
			}

			// Padding
			TokenKind::Dollar => {
				let num_token = self.next();
				let num_span = num_token.span;
				match num_token.kind {
					TokenKind::Number(radix) => {
						let num = parse_num(self.source, radix, num_span)?;
						(
							Expr::Padding(num).into(),
							Span::from_to(start_span, num_span),
						)
					}
					found => {
						return Err(ErrorKind::ExpectedNumber { found }.err(num_span));
					}
				}
			}

			// Intrinsics or other symbols
			TokenKind::Ident => {
				let expr = match self.parse_intrinsic() {
					Some((kind, mode)) => Expr::Intrinsic(kind, mode),
					None => Expr::unknown_symbol(Name::new(self.slice())),
				};
				(expr.into(), Span::from_to(start_span, self.span()))
			}

			// Pointer to a symbol
			TokenKind::Ampersand => {
				let name = self.parse_name()?;
				(
					Expr::unknown_ptr_to(name).into(),
					Span::from_to(start_span, self.span()),
				)
			}

			// Loop block
			TokenKind::Keyword(Keyword::Loop) => {
				self.expect(TokenKind::AtSign)?;
				let label = self.parse_name()?;
				let span = self.span();
				let body = self.parse_body()?;
				(
					Expr::Block {
						looping: true,
						label: Spanned::new(label, span),
						body,
					}
					.into(),
					span,
				)
			}

			// Block
			TokenKind::AtSign => {
				let label = self.parse_name()?;
				let span = self.span();
				let body = self.parse_body()?;
				(
					Expr::Block {
						looping: false,
						label: Spanned::new(label, span),
						body,
					}
					.into(),
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
					Expr::Jump {
						label: Spanned::new(label, span),
						conditional,
					}
					.into(),
					self.span(),
				)
			}

			// If
			TokenKind::Keyword(Keyword::If) => {
				let if_body = self.parse_body()?;

				let else_body = match self.optional(TokenKind::Keyword(Keyword::Else)) {
					Some(_) => Some(self.parse_body()?),
					None => None,
				};

				(Expr::If { if_body, else_body }.into(), start_span)
			}

			TokenKind::Keyword(Keyword::While) => {
				let mut condition = Vec::<Spanned<Node>>::with_capacity(16);

				loop {
					let token = self.peek();
					match token.kind {
						found @ TokenKind::OpenBrace | found @ TokenKind::Eof
							if condition.is_empty() =>
						{
							return Err(ErrorKind::ExpectedCondition { found }.err(token.span));
						}

						TokenKind::OpenBrace => break,
						_ => condition.push(self.parse_next_node()?),
					}
				}

				let body = self.parse_body()?;

				(
					Expr::While {
						condition: condition.into_boxed_slice(),
						body,
					}
					.into(),
					start_span,
				)
			}

			_ => return Err(ErrorKind::UnexpectedToken.err(start_span)),
		};

		Ok(Spanned::new(node, node_span))
	}

	/// Parse nodes inside `{ ... }`
	fn parse_body(&mut self) -> error::Result<Box<[Spanned<Node>]>> {
		self.expect(TokenKind::OpenBrace)?;

		let mut nodes: Vec<Spanned<Node>> = Vec::with_capacity(64);
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

				_ => nodes.push(self.parse_next_node()?),
			}
		}

		self.expect(TokenKind::CloseBrace)?;

		Ok(nodes.into_boxed_slice())
	}

	fn parse_func(&mut self) -> error::Result<(Node, Span)> {
		let name = self.parse_name()?;
		let span = self.span();
		let args = self.parse_func_args()?;
		let body = self.parse_body()?;

		let func = FuncDef { name, args, body };
		Ok((Definition::Func(func).into(), span))
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

	fn parse_var(&mut self) -> error::Result<(Node, Span)> {
		let typ = self.parse_type()?;
		let name = self.parse_name()?;
		let span = self.span();

		let var = VarDef { name, typ };
		Ok((Definition::Var(var).into(), span))
	}

	fn parse_const(&mut self) -> error::Result<(Node, Span)> {
		let typ = self.parse_type()?;
		let name = self.parse_name()?;
		let span = self.span();
		let body = self.parse_body()?;

		let cnst = ConstDef { name, typ, body };
		Ok((Definition::Const(cnst).into(), span))
	}

	fn parse_data(&mut self) -> error::Result<(Node, Span)> {
		let name = self.parse_name()?;
		let span = self.span();
		let body = self.parse_body()?;

		let data = DataDef { name, body };
		Ok((Definition::Data(data).into(), span))
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
			"ptr" => Type::BytePtr(Box::new(self.parse_type()?.x)),
			"ptr2" => Type::ShortPtr(Box::new(self.parse_type()?.x)),
			"funptr" => {
				let sig = self.parse_func_args()?.to_signature();
				Type::FuncPtr(sig)
			}
			_ => return Err(ErrorKind::NoCustomTypesYet.err(start)),
		};

		let end = self.span();

		Ok(Spanned::new(typ, Span::from_to(start, end)))
	}

	fn parse_name(&mut self) -> error::Result<Name> {
		self.expect(TokenKind::Ident)?;
		Ok(Name::new(self.slice()))
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
