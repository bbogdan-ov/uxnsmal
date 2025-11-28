use crate::{
	ast::{Ast, ConstDef, DataDef, Def, Expr, FuncArgs, FuncDef, Node, VarDef},
	error::{self, Error},
	lexer::{Keyword, Span, Spanned, Token, TokenKind},
	symbols::{Name, Type},
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
		ch => Err(Error::UnknownCharEscape(ch, span)),
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
			return Ok(Ast::default());
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
			let token = self.peek_token();
			match token.kind {
				TokenKind::Eof => break,

				TokenKind::Comment => self.advance(),

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
		let token = self.next_token();
		let start_span = token.span;

		let (node, node_span): (Node, Span) = match token.kind {
			TokenKind::Keyword(Keyword::Func) => self.parse_func()?,
			TokenKind::Keyword(Keyword::Var) => self.parse_var()?,
			TokenKind::Keyword(Keyword::Const) => self.parse_const()?,
			TokenKind::Keyword(Keyword::Data) => self.parse_data()?,

			// Number literal
			TokenKind::Number(num, _) => {
				let expr = if self.optional(TokenKind::Asterisk).is_some() {
					Expr::Short(num)
				} else if num > u8::MAX as u16 {
					return Err(Error::ByteIsTooBig(start_span));
				} else {
					Expr::Byte(num as u8)
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
					return Err(Error::InvalidCharLiteral(span));
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
					return Err(Error::InvalidCharLiteral(span));
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
				let num_token = self.next_token();
				let num_span = num_token.span;
				match num_token.kind {
					TokenKind::Number(num, _) => (
						Expr::Padding(num).into(),
						Span::from_to(start_span, num_span),
					),
					found => {
						return Err(Error::ExpectedNumber {
							found,
							span: num_span,
						});
					}
				}
			}

			// Store and Bind
			TokenKind::ArrowRight => {
				if self.optional(TokenKind::OpenParen).is_some() {
					// Bind
					let names = self.parse_seq_of(Self::parse_spanned_name_optional)?;
					self.expect(TokenKind::CloseParen)?;
					(
						Expr::Bind(names).into(),
						Span::from_to(start_span, self.span()),
					)
				} else {
					// Store
					let name = self.parse_name()?;
					(
						Expr::Store(name).into(),
						Span::from_to(start_span, self.span()),
					)
				}
			}

			// Expect bind
			TokenKind::OpenParen => {
				let names = self.parse_seq_of(Self::parse_spanned_name_optional)?;
				self.expect(TokenKind::CloseParen)?;
				(
					Expr::ExpectBind(names).into(),
					Span::from_to(start_span, self.span()),
				)
			}

			// Cast
			TokenKind::Keyword(Keyword::As) => {
				self.expect(TokenKind::OpenParen)?;
				let types = self.parse_seq_of(Self::parse_type_optional)?;
				self.expect(TokenKind::CloseParen)?;
				(
					Expr::Cast(types).into(),
					Span::from_to(start_span, self.span()),
				)
			}

			// Intrinsic
			TokenKind::Intrinsic(kind, mode) => (
				Expr::Intrinsic(kind, mode).into(),
				Span::from_to(start_span, self.span()),
			),

			// Symbols
			TokenKind::Ident => {
				let name = Name::new(self.slice());
				(
					Expr::Symbol(name).into(),
					Span::from_to(start_span, self.span()),
				)
			}

			// Pointer to a symbol
			TokenKind::Ampersand => {
				let name = self.parse_name()?;
				(
					Expr::PtrTo(name).into(),
					Span::from_to(start_span, self.span()),
				)
			}

			// Loop block
			TokenKind::Keyword(Keyword::Loop) => {
				let label = self.parse_label_name()?;
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
			TokenKind::Label => {
				let label = Name::new(&self.slice()[1..]);
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
			TokenKind::Keyword(Keyword::Jump) => {
				let label = self.parse_label_name()?;
				let span = self.span();

				(
					Expr::Jump {
						label: Spanned::new(label, span),
					}
					.into(),
					self.span(),
				)
			}

			// Return
			TokenKind::Keyword(Keyword::Return) => (Expr::Return.into(), self.span()),

			// If
			TokenKind::Keyword(Keyword::If) => {
				let if_body = self.parse_body()?;

				let else_body = match self.optional(TokenKind::Keyword(Keyword::Else)) {
					Some(_) => Some(self.parse_body()?),
					None => None,
				};

				(Expr::If { if_body, else_body }.into(), start_span)
			}

			// While
			TokenKind::Keyword(Keyword::While) => {
				let mut condition = Vec::<Spanned<Node>>::with_capacity(16);

				loop {
					let token = self.peek_token();
					let is_unexpected = matches!(token.kind, TokenKind::OpenBrace | TokenKind::Eof);

					if condition.is_empty() && is_unexpected {
						return Err(Error::ExpectedCondition {
							found: token.kind,
							span: token.span,
						});
					} else if token.kind == TokenKind::OpenBrace {
						break;
					} else {
						condition.push(self.parse_next_node()?)
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

			_ => return Err(Error::UnexpectedToken(start_span)),
		};

		Ok(Spanned::new(node, node_span))
	}

	/// Parse nodes inside `{ ... }`
	fn parse_body(&mut self) -> error::Result<Box<[Spanned<Node>]>> {
		self.expect(TokenKind::OpenBrace)?;

		let mut nodes: Vec<Spanned<Node>> = Vec::with_capacity(64);
		let mut brace_depth: u16 = 0;

		while self.cursor < self.tokens.len() {
			let cur_token = self.peek_token();
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

				TokenKind::Comment => self.advance(),

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
		Ok((Def::Func(func).into(), span))
	}
	fn parse_func_args(&mut self) -> error::Result<FuncArgs> {
		self.expect(TokenKind::OpenParen)?;

		if self.optional(TokenKind::ArrowRight).is_some() {
			self.expect(TokenKind::CloseParen)?;
			return Ok(FuncArgs::Vector);
		}

		let inputs = self.parse_seq_of(Self::parse_type_optional)?;
		self.expect(TokenKind::DoubleDash)?;
		let outputs = self.parse_seq_of(Self::parse_type_optional)?;

		self.expect(TokenKind::CloseParen)?;

		Ok(FuncArgs::Proc { inputs, outputs })
	}

	fn parse_var(&mut self) -> error::Result<(Node, Span)> {
		let typ = self.parse_type()?;
		let name = self.parse_name()?;
		let span = self.span();

		let var = VarDef { name, typ };
		Ok((Def::Var(var).into(), span))
	}

	fn parse_const(&mut self) -> error::Result<(Node, Span)> {
		let typ = self.parse_type()?;
		let name = self.parse_name()?;
		let span = self.span();
		let body = self.parse_body()?;

		let cnst = ConstDef { name, typ, body };
		Ok((Def::Const(cnst).into(), span))
	}

	fn parse_data(&mut self) -> error::Result<(Node, Span)> {
		let name = self.parse_name()?;
		let span = self.span();
		let body = self.parse_body()?;

		let data = DataDef { name, body };
		Ok((Def::Data(data).into(), span))
	}

	fn parse_type_optional(&mut self) -> error::Result<Option<Spanned<Type>>> {
		let token = self.peek_token();
		let kind = token.kind;
		let start = token.span;

		let typ = match kind {
			TokenKind::Ident => {
				self.advance();
				match &self.source[start.into_range()] {
					"byte" => Type::Byte,
					"short" => Type::Short,
					_ => return Err(Error::NoCustomTypesYet(start)),
				}
			}
			TokenKind::Keyword(Keyword::Func) => {
				self.advance();
				let sig = self.parse_func_args()?.to_signature();
				Type::FuncPtr(sig)
			}
			TokenKind::Hat => {
				self.advance();
				let typ = self.parse_type()?.x;
				Type::BytePtr(Box::new(typ))
			}
			TokenKind::Asterisk => {
				self.advance();
				let typ = self.parse_type()?.x;
				Type::ShortPtr(Box::new(typ))
			}

			_ => return Ok(None),
		};

		let end = self.span();

		Ok(Some(Spanned::new(typ, Span::from_to(start, end))))
	}
	fn parse_type(&mut self) -> error::Result<Spanned<Type>> {
		let Some(typ) = self.parse_type_optional()? else {
			let token = self.peek_token();
			return Err(Error::ExpectedType {
				found: token.kind,
				span: token.span,
			});
		};

		Ok(typ)
	}

	fn parse_spanned_name_optional(&mut self) -> error::Result<Option<Spanned<Name>>> {
		match self.optional(TokenKind::Ident) {
			Some(_) => {
				let name = Name::new(self.slice());
				Ok(Some(Spanned::new(name, self.span())))
			}
			None => Ok(None),
		}
	}
	fn parse_name(&mut self) -> error::Result<Name> {
		self.expect(TokenKind::Ident)?;
		Ok(Name::new(self.slice()))
	}
	fn parse_label_name(&mut self) -> error::Result<Name> {
		self.expect(TokenKind::Label)?;
		let slice = &self.slice()[1..]; // skip '@'
		Ok(Name::new(slice))
	}

	fn parse_seq_of<T>(
		&mut self,
		parse: fn(&mut Parser<'a>) -> error::Result<Option<T>>,
	) -> error::Result<Box<[T]>> {
		let Some(node) = parse(self)? else {
			return Ok(Box::default());
		};

		let mut nodes = Vec::<T>::with_capacity(16);
		nodes.push(node);

		while let Some(node) = parse(self)? {
			nodes.push(node);
		}

		Ok(nodes.into_boxed_slice())
	}

	// ==============================
	// Helper functions
	// ==============================

	/// Returns `Ok(())` and consume the current token if its kind is equal to the specified one,
	/// otherwise returns `Err`
	fn expect(&mut self, kind: TokenKind) -> error::Result<&Token> {
		let cur_token = self.peek_token();
		if cur_token.kind == kind {
			Ok(self.next_token())
		} else {
			Err(Error::Expected {
				expected: kind,
				found: cur_token.kind,
				span: cur_token.span,
			})
		}
	}
	/// Returns `Some(())` and consume the current token if its kind is equal to the specified one
	fn optional(&mut self, kind: TokenKind) -> Option<&Token> {
		if self.peek_token().kind == kind {
			Some(self.next_token())
		} else {
			None
		}
	}

	/// Returns and consumes the current token
	pub fn next_token(&mut self) -> &Token {
		let token = &self.tokens[self.cursor];
		self.cursor += 1;
		token
	}
	/// Returns the current token without consuming
	pub fn peek_token(&self) -> &Token {
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
