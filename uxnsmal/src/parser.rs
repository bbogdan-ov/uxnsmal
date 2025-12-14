use crate::{
	ast::{
		Ast, ConstDef, DataDef, Def, ElseBlock, ElseIfBlock, EnumDef, EnumDefVariant, Expr,
		FuncDef, Node, StructDef, StructDefField, TypeDef, VarDef,
	},
	error::{self, Error},
	lexer::{Keyword, Radix, Span, Spanned, Token, TokenKind},
	symbols::{FieldAccess, FuncSignature, Name, NamedType, SymbolAccess, UnsizedType},
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
	fn parse_next_node(&mut self) -> error::Result<Node> {
		let token = self.peek_token();

		let node: Node = match token.kind {
			TokenKind::Keyword(Keyword::Func) => {
				let def = self.parse_func_def()?;
				Node::Def(Def::Func(def))
			}
			TokenKind::Keyword(Keyword::Var) => {
				let def = self.parse_var_def(false)?;
				Node::Def(Def::Var(def))
			}
			TokenKind::Keyword(Keyword::Rom) => {
				let def = self.parse_var_def(true)?;
				Node::Def(Def::Var(def))
			}
			TokenKind::Keyword(Keyword::Const) => {
				let def = self.parse_const_def()?;
				Node::Def(Def::Const(def))
			}
			TokenKind::Keyword(Keyword::Data) => {
				let def = self.parse_data_def()?;
				Node::Def(Def::Data(def))
			}
			TokenKind::Keyword(Keyword::Type) => {
				let def = self.parse_type_def()?;
				Node::Def(Def::Type(def))
			}
			TokenKind::Keyword(Keyword::Enum) => {
				let def = self.parse_enum_def(false)?;
				Node::Def(Def::Enum(def))
			}
			TokenKind::Keyword(Keyword::Untyped) => {
				let def = self.parse_enum_def(true)?;
				Node::Def(Def::Enum(def))
			}
			TokenKind::Keyword(Keyword::Struct) => {
				let def = self.parse_struct_def()?;
				Node::Def(Def::Struct(def))
			}

			// Number literal
			TokenKind::Number(value, _) => {
				self.advance();

				let expr = match self.optional(TokenKind::Asterisk) {
					Some(star) => Expr::Short {
						value,
						span: Span::from_to(star.span, token.span),
					},
					None if value <= u8::MAX as u16 => Expr::Byte {
						value: value as u8,
						span: token.span,
					},
					None => {
						return Err(Error::ByteIsTooBig(token.span));
					}
				};

				Node::Expr(expr)
			}
			// Char literal
			// TODO: add ability to mark char as short just like with numbers
			TokenKind::Char => {
				let expr = self.parse_char()?;
				Node::Expr(expr)
			}
			TokenKind::String => {
				let expr = self.parse_string()?;
				Node::Expr(expr)
			}

			// Padding
			TokenKind::Dollar => {
				self.advance();
				let (num, _, num_span) = self.expect_number()?;
				let span = Span::from_to(token.span, num_span);
				Node::Expr(Expr::Padding { value: num, span })
			}

			// Store and Bind
			TokenKind::ArrowRight => {
				let expr = self.parse_store_or_bind()?;
				Node::Expr(expr)
			}

			// Expect bind
			TokenKind::OpenParen => {
				self.advance();
				let names = self.parse_seq_of(Self::parse_spanned_name_optional)?;
				let close = self.expect(TokenKind::CloseParen)?;
				let span = Span::from_to(token.span, close.span);
				Node::Expr(Expr::ExpectBind { names, span })
			}

			// Cast
			TokenKind::Keyword(Keyword::As) => {
				self.advance();
				self.expect(TokenKind::OpenParen)?;
				let types = self.parse_seq_of(Self::parse_named_type_optional)?;
				let close = self.expect(TokenKind::CloseParen)?;
				let span = Span::from_to(token.span, close.span);
				Node::Expr(Expr::Cast { types, span })
			}

			// Intrinsic
			TokenKind::Intrinsic(kind, mode) => {
				self.advance();
				Node::Expr(Expr::Intrinsic {
					kind,
					mode,
					span: token.span,
				})
			}

			// Symbols
			TokenKind::Ident => {
				let access = self.parse_symbol_access()?;
				let span = Span::from_to(token.span, self.span());
				Node::Expr(Expr::Symbol {
					access: access.x,
					span,
				})
			}

			// Pointer to a symbol
			TokenKind::Ampersand => {
				self.advance();
				let access = self.parse_symbol_access()?;
				let span = Span::from_to(token.span, self.span());
				Node::Expr(Expr::PtrTo { access, span })
			}

			// Loop block
			TokenKind::Keyword(Keyword::Loop) => {
				let expr = self.parse_block(true)?;
				Node::Expr(expr)
			}

			// Block
			TokenKind::Label => {
				let expr = self.parse_block(false)?;
				Node::Expr(expr)
			}

			// Jump
			TokenKind::Keyword(Keyword::Jump) => {
				self.advance();
				let label = self.parse_label_name()?;

				let span = Span::from_to(token.span, label.span);
				Node::Expr(Expr::Jump { label, span })
			}

			// Return
			TokenKind::Keyword(Keyword::Return) => {
				self.advance();
				Node::Expr(Expr::Return { span: token.span })
			}

			// If
			TokenKind::Keyword(Keyword::If) => {
				let expr = self.parse_if()?;
				Node::Expr(expr)
			}

			// While
			TokenKind::Keyword(Keyword::While) => {
				self.advance();
				let condition = self.parse_condition()?;
				let body = self.parse_body()?;

				let span = Span::from_to(token.span, condition.span);
				Node::Expr(Expr::While {
					condition,
					body,
					span,
				})
			}

			_ => return Err(Error::UnexpectedToken(token.span)),
		};

		Ok(node)
	}

	fn parse_func_def(&mut self) -> error::Result<FuncDef> {
		let keyword = self.expect(TokenKind::Keyword(Keyword::Func))?;
		let name = self.parse_name()?;
		let signature = self.parse_func_signature()?;
		let body = self.parse_body()?;

		let span = Span::from_to(keyword.span, signature.span);
		Ok(FuncDef {
			name,
			signature,
			body,
			span,
			symbol: None,
		})
	}
	fn parse_func_signature(&mut self) -> error::Result<Spanned<FuncSignature<UnsizedType>>> {
		let open = self.expect(TokenKind::OpenParen)?;

		if self.optional(TokenKind::ArrowRight).is_some() {
			let close = self.expect(TokenKind::CloseParen)?;
			let span = Span::from_to(open.span, close.span);
			return Ok(Spanned::new(FuncSignature::Vector, span));
		}

		let inputs = self.parse_seq_of(Self::parse_named_type_optional)?;
		self.expect(TokenKind::DoubleDash)?;
		let outputs = self.parse_seq_of(Self::parse_named_type_optional)?;

		let close = self.expect(TokenKind::CloseParen)?;

		let span = Span::from_to(open.span, close.span);
		Ok(Spanned::new(FuncSignature::Proc { inputs, outputs }, span))
	}

	fn parse_var_def(&mut self, in_rom: bool) -> error::Result<VarDef> {
		let keyword: Token;
		if in_rom {
			keyword = self.expect(TokenKind::Keyword(Keyword::Rom))?;
			self.expect(TokenKind::Keyword(Keyword::Var))?;
		} else {
			keyword = self.expect(TokenKind::Keyword(Keyword::Var))?;
		}
		let typ = self.parse_type()?;
		let name = self.parse_name()?;

		let span = Span::from_to(keyword.span, name.span);
		Ok(VarDef {
			name,
			in_rom,
			typ,
			span,
			symbol: None,
		})
	}

	fn parse_const_def(&mut self) -> error::Result<ConstDef> {
		let keyword = self.expect(TokenKind::Keyword(Keyword::Const))?;
		let typ = self.parse_type()?;
		let name = self.parse_name()?;
		let body = self.parse_body()?;

		let span = Span::from_to(keyword.span, name.span);
		Ok(ConstDef {
			name,
			typ,
			body,
			span,
			symbol: None,
		})
	}

	fn parse_data_def(&mut self) -> error::Result<DataDef> {
		let keyword = self.expect(TokenKind::Keyword(Keyword::Data))?;
		let name = self.parse_name()?;
		let body = self.parse_body()?;

		let span = Span::from_to(keyword.span, name.span);
		Ok(DataDef {
			name,
			body,
			span,
			symbol: None,
		})
	}

	fn parse_type_def(&mut self) -> error::Result<TypeDef> {
		let keyword = self.expect(TokenKind::Keyword(Keyword::Type))?;
		let inherits = self.parse_type()?;
		let name = self.parse_name()?;

		let span = Span::from_to(keyword.span, name.span);
		Ok(TypeDef {
			name,
			inherits,
			span,
			symbol: None,
		})
	}

	fn parse_enum_def(&mut self, untyped: bool) -> error::Result<EnumDef> {
		let keyword: Token;
		if untyped {
			keyword = self.expect(TokenKind::Keyword(Keyword::Untyped))?;
			self.expect(TokenKind::Keyword(Keyword::Enum))?;
		} else {
			keyword = self.expect(TokenKind::Keyword(Keyword::Enum))?;
		}
		let inherits = self.parse_type()?;
		let name = self.parse_name()?;
		let variants = self.parse_enum_variants_list()?;

		let span = Span::from_to(keyword.span, name.span);
		Ok(EnumDef {
			name,
			inherits,
			variants,
			untyped,
			span,
			symbol: None,
		})
	}
	fn parse_enum_variants_list(&mut self) -> error::Result<Vec<EnumDefVariant>> {
		self.expect(TokenKind::OpenBrace)?;

		let mut variants: Vec<EnumDefVariant> = Vec::default();

		while self.cursor < self.tokens.len() {
			let cur_token = self.peek_token();
			match cur_token.kind {
				TokenKind::Eof | TokenKind::CloseBrace => break,
				_ => variants.push(self.parse_enum_variant()?),
			}
		}

		self.expect(TokenKind::CloseBrace)?;

		Ok(variants)
	}
	fn parse_enum_variant(&mut self) -> error::Result<EnumDefVariant> {
		let name = self.parse_name()?;
		let mut body: Option<Vec<Node>> = None;

		if self.peek_token().kind == TokenKind::OpenBrace {
			body = Some(self.parse_body()?);
		}

		Ok(EnumDefVariant { name, body })
	}

	fn parse_struct_def(&mut self) -> error::Result<StructDef> {
		let keyword = self.expect(TokenKind::Keyword(Keyword::Struct))?;
		let name = self.parse_name()?;

		self.expect(TokenKind::OpenBrace)?;

		let mut fields: Vec<StructDefField> = vec![];

		while self.cursor < self.tokens.len() {
			let cur_token = self.peek_token();
			match cur_token.kind {
				TokenKind::CloseBrace | TokenKind::Eof => {
					break;
				}

				_ => fields.push(self.parse_struct_field()?),
			}
		}

		self.expect(TokenKind::CloseBrace)?;

		let span = Span::from_to(keyword.span, name.span);
		Ok(StructDef {
			name,
			fields,
			span,
			symbol: None,
		})
	}
	fn parse_struct_field(&mut self) -> error::Result<StructDefField> {
		let typ = self.parse_type()?;
		let name = self.parse_name()?;
		let span = Span::from_to(typ.span, name.span);

		Ok(StructDefField { typ, name, span })
	}

	fn parse_char(&mut self) -> error::Result<Expr> {
		let token = self.expect(TokenKind::Char)?;

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

		Ok(Expr::Byte { value: byte, span })
	}

	fn parse_string(&mut self) -> error::Result<Expr> {
		let token = self.expect(TokenKind::String)?;

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

		Ok(Expr::String {
			string: string.into_boxed_str(),
			span,
		})
	}

	fn parse_store_or_bind(&mut self) -> error::Result<Expr> {
		let token = self.expect(TokenKind::ArrowRight)?;

		if self.optional(TokenKind::OpenParen).is_some() {
			// Bind
			let names = self.parse_seq_of(Self::parse_spanned_name_optional)?;
			let close = self.expect(TokenKind::CloseParen)?;
			let span = Span::from_to(token.span, close.span);
			Ok(Expr::Bind { names, span })
		} else {
			// Store
			let access = self.parse_symbol_access()?;
			let span = Span::from_to(token.span, self.span());
			Ok(Expr::Store { access, span })
		}
	}

	fn parse_block(&mut self, looping: bool) -> error::Result<Expr> {
		let start: Span;
		let label = if looping {
			start = self.expect(TokenKind::Keyword(Keyword::Loop))?.span;
			self.parse_label_name()?
		} else {
			let label = self.parse_label_name()?;
			start = label.span;
			label
		};

		let body = self.parse_body()?;

		let span = Span::from_to(start, label.span);
		Ok(Expr::Block {
			looping,
			label,
			body,
			span,
		})
	}

	fn parse_if(&mut self) -> error::Result<Expr> {
		let if_token = self.expect(TokenKind::Keyword(Keyword::If))?;
		let if_body = self.parse_body()?;

		// Parse `elif` sequence
		let mut elif_blocks = Vec::<ElseIfBlock>::default();
		while let Some(elif_token) = self.optional(TokenKind::Keyword(Keyword::ElseIf)) {
			let condition = self.parse_condition()?;
			let body = self.parse_body()?;

			elif_blocks.push(ElseIfBlock {
				condition,
				body,
				span: elif_token.span,
			});
		}

		// Parse `else` block
		let else_block = match self.optional(TokenKind::Keyword(Keyword::Else)) {
			Some(else_token) => Some(ElseBlock {
				body: self.parse_body()?,
				span: else_token.span,
			}),
			None => None,
		};

		let span = if_token.span;
		Ok(Expr::If {
			if_body,
			if_span: if_token.span,
			elif_blocks,
			else_block,
			span,
		})
	}

	/// Parse nodes inside `{ ... }`
	fn parse_body(&mut self) -> error::Result<Vec<Node>> {
		self.expect(TokenKind::OpenBrace)?;

		let mut nodes: Vec<Node> = Vec::with_capacity(64);
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

		Ok(nodes)
	}

	fn parse_symbol_access(&mut self) -> error::Result<Spanned<SymbolAccess>> {
		let mut fields = vec1::vec1![self.parse_field_access()?];
		let span = fields[0].span;
		while self.optional(TokenKind::Dot).is_some() {
			fields.push(self.parse_field_access()?);
		}
		let span = Span::from_to(span, self.span());
		Ok(Spanned::new(SymbolAccess { fields }, span))
	}
	fn parse_field_access(&mut self) -> error::Result<FieldAccess> {
		let name = self.parse_name()?;
		let is_array = self.optional(TokenKind::Box).is_some();
		Ok(FieldAccess {
			name: name.x,
			is_array,
			span: name.span,
		})
	}

	fn parse_condition(&mut self) -> error::Result<Spanned<Vec<Node>>> {
		let mut condition = Vec::<Node>::with_capacity(16);

		let mut span = self.span();

		loop {
			let token = self.peek_token();
			let is_unexpected = matches!(token.kind, TokenKind::OpenBrace | TokenKind::Eof);
			span = Span::from_to(span, token.span);

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

		Ok(Spanned::new(condition, span))
	}

	fn parse_named_type_optional(&mut self) -> error::Result<Option<NamedType<UnsizedType>>> {
		let Some(typ) = self.parse_type_optional()? else {
			return Ok(None);
		};

		if self.optional(TokenKind::Colon).is_some() {
			let name = self.parse_name()?;
			let span = Span::from_to(typ.span, name.span);
			Ok(Some(NamedType {
				typ,
				name: Some(name),
				span,
			}))
		} else {
			Ok(Some(NamedType {
				span: typ.span,
				typ,
				name: None,
			}))
		}
	}
	fn parse_type_optional(&mut self) -> error::Result<Option<Spanned<UnsizedType>>> {
		let token = self.peek_token();
		let span = token.span;

		let (typ, span) = match token.kind {
			TokenKind::Ident => {
				self.advance();
				match self.slice() {
					"byte" => (UnsizedType::Byte, span),
					"short" => (UnsizedType::Short, span),
					n => (UnsizedType::Type(Name::new(n)), span),
				}
			}
			TokenKind::Keyword(Keyword::Func) => {
				self.advance();
				let sig = self.parse_func_signature()?;
				let span = Span::from_to(span, sig.span);
				(UnsizedType::FuncPtr(sig.x), span)
			}
			TokenKind::Hat => {
				self.advance();
				let typ = self.parse_type()?;
				let span = Span::from_to(span, typ.span);
				(UnsizedType::BytePtr(Box::new(typ.x)), span)
			}
			TokenKind::Asterisk => {
				self.advance();
				let typ = self.parse_type()?;
				let span = Span::from_to(span, typ.span);
				(UnsizedType::ShortPtr(Box::new(typ.x)), span)
			}
			TokenKind::OpenBracket => {
				self.advance();
				let (count, _, _) = self.expect_number()?;
				self.expect(TokenKind::CloseBracket)?;

				let typ = self.parse_type()?;
				let span = Span::from_to(span, typ.span);

				let typ = Box::new(typ.x);
				(UnsizedType::Array { typ, count }, span)
			}
			TokenKind::Box => {
				self.advance();

				let typ = self.parse_type()?;
				let span = Span::from_to(span, typ.span);

				(UnsizedType::UnsizedArray { typ: typ.x.into() }, span)
			}

			_ => return Ok(None),
		};

		Ok(Some(Spanned::new(typ, span)))
	}
	fn parse_type(&mut self) -> error::Result<Spanned<UnsizedType>> {
		let Some(typ) = self.parse_type_optional()? else {
			let token = self.peek_token();
			return Err(Error::ExpectedType {
				found: token.kind,
				span: token.span,
			});
		};

		Ok(typ)
	}

	fn parse_name_optional(&mut self) -> error::Result<Option<Name>> {
		match self.optional(TokenKind::Ident) {
			Some(_) => {
				let name = Name::new(self.slice());
				Ok(Some(name))
			}
			None => Ok(None),
		}
	}
	fn parse_spanned_name_optional(&mut self) -> error::Result<Option<Spanned<Name>>> {
		match self.parse_name_optional()? {
			Some(name) => Ok(Some(Spanned::new(name, self.span()))),
			None => Ok(None),
		}
	}
	fn parse_name(&mut self) -> error::Result<Spanned<Name>> {
		let token = self.expect(TokenKind::Ident)?;
		Ok(Spanned::new(Name::new(self.slice()), token.span))
	}
	fn parse_label_name(&mut self) -> error::Result<Spanned<Name>> {
		let token = self.expect(TokenKind::Label)?;
		let slice = &self.source[token.span.into_range()];
		let slice = &slice[1..]; // skip '@'
		Ok(Spanned::new(Name::new(slice), token.span))
	}

	fn parse_seq_of<T>(
		&mut self,
		parse: fn(&mut Parser<'a>) -> error::Result<Option<T>>,
	) -> error::Result<Vec<T>> {
		let Some(node) = parse(self)? else {
			return Ok(Vec::default());
		};

		let mut nodes = Vec::<T>::with_capacity(16);
		nodes.push(node);

		while let Some(node) = parse(self)? {
			nodes.push(node);
		}

		Ok(nodes)
	}

	// ==============================
	// Helper functions
	// ==============================

	fn expect_number(&mut self) -> error::Result<(u16, Radix, Span)> {
		let num_token = self.next_token();
		let TokenKind::Number(value, radix) = num_token.kind else {
			return Err(Error::ExpectedNumber {
				found: num_token.kind,
				span: num_token.span,
			});
		};
		Ok((value, radix, num_token.span))
	}
	/// Returns `Ok(())` and consume the current token if its kind is equal to the specified one,
	/// otherwise returns `Err`
	fn expect(&mut self, kind: TokenKind) -> error::Result<Token> {
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
	fn optional(&mut self, kind: TokenKind) -> Option<Token> {
		if self.peek_token().kind == kind {
			Some(self.next_token())
		} else {
			None
		}
	}

	/// Returns and consumes the current token
	pub fn next_token(&mut self) -> Token {
		let token = self.tokens[self.cursor];
		self.cursor += 1;
		token
	}
	/// Returns the current token without consuming
	pub fn peek_token(&self) -> Token {
		self.tokens[self.cursor]
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
