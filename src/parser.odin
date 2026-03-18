#+vet explicit-allocators

package uxnsmal

import "base:runtime"
import "core:slice"
import "core:strings"

// AST parser.
Parser :: struct {
	source:    string,
	file:      File,
	// List of all tokens in the file. Always includes EOF at the end.
	tokens:    [dynamic]Token,
	// Current token index.
	cursor:    int,
	// Arena allocator for AST nodes and their data.
	arena:     runtime.Arena,
	allocator: runtime.Allocator,
}

// Initializes a `Parser` and parses a source code of a file, spitting file's AST.
@(require_results)
parse :: proc(p: ^Parser, source: string) -> (err: Error) {
	// Init parser.
	p.source = source
	p.allocator = runtime.arena_allocator(&p.arena)
	p.file.nodes = make([dynamic]Node, 0, 32, p.allocator)

	// Init lexer.
	lexer: Lexer
	lexer_init(&lexer, source)

	// Collect all tokens.
	p.tokens = make([dynamic]Token, 0, 32, p.allocator)
	for {
		token := lexer_next(&lexer) or_return
		append(&p.tokens, token) // NOTE: collecting an EOF token too.
		if token.kind == .EOF do break
	}

	// Skip all comments at the beginning of the source code.
	parser_advance(p)
	p.cursor -= 1

	for {
		token := parser_peek_token(p)
		if token.kind == .EOF do break

		node := parse_next_node(p) or_return
		append(&p.file.nodes, node)
	}

	return nil
}

parse_next_node :: proc(p: ^Parser) -> (node: Node, err: Error) {
	token := parser_peek_token(p)

	#partial switch token.kind {
	// Definitions
	case .Keyword_Fun:
		def := parse_func_def(p) or_return
		return def, nil
	case .Keyword_Var, .Keyword_Rom:
		def := parse_var_def(p, token.kind == .Keyword_Rom) or_return
		return def, nil
	case .Keyword_Const:
		def := parse_const_def(p) or_return
		return def, nil
	case .Keyword_Data:
		def := parse_data_def(p) or_return
		return def, nil
	case .Keyword_Type:
		return parse_user_type_def(p)
	case .Keyword_Enum, .Keyword_Struct:
		panic("TODO: show how to correctly define enums and structs")

	case .Ident, .Ampersand:
		expr := parse_symbol(p, token.kind == .Ampersand) or_return
		return Expr(expr), nil
	case .Intr:
		expr := parse_intr(p) or_return
		return Expr(expr), nil
	case .Number:
		return parse_number(p)
	case .String:
		expr := parse_string(p) or_return
		return Expr(expr), nil
	case .Char:
		expr := parse_char(p) or_return
		return Expr(expr), nil

	case .Keyword_If:
		expr := parse_if(p) or_return
		return Expr(expr), nil

	case:
		return {}, problemf(token.span, "unexpected %v", token_name(token))
	}
}

// ------------------------------
// Expressions parsing.
// ------------------------------

// Parse a symbol use (e.g. a function call, variable access, etc).
// symbol = ["&"] name ("." name ["[]"])*
parse_symbol :: proc(p: ^Parser, as_ptr: bool) -> (expr: Expr_Symbol, err: Error) {
	if as_ptr {
		parser_expect(p, .Ampersand) or_return
	}

	// May be we should allocate the array only after we encounter at least one name?
	expr.members = make([dynamic]Member, p.allocator)
	expr.as_ptr = as_ptr

	for {
		name := parse_name(p) or_return
		as_array := false

		// Check if it is an array access (`member[]`).
		open, found := parser_optional(p, .Open_Bracket)
		close: Token
		if found {
			close, found = parser_optional(p, .Close_Bracket)
			if !found {
				tok := parser_peek_token(p)
				// TODO: show an example of accessing an array.
				err = problemf(
					open.span,
					`expected a "]" right after the "[", but got a %v`,
					token_name(tok),
				)
				return {}, err
			}

			as_array = true
		}

		append(&expr.members, Member{name, as_array})

		_, found = parser_optional(p, .Dot)
		if !found do break

		// Collect next members after the dot...
	}

	assert(len(expr.members) >= 1)

	expr.span = slice.first(expr.members[:]).name.span
	expr.span.end = slice.last(expr.members[:]).name.span.end

	return expr, nil
}

// Parse an intrinsic call.
parse_intr :: proc(p: ^Parser) -> (expr: Expr_Intr, err: Error) {
	token := parser_expect(p, .Intr) or_return
	expr.kind = token.value.(Intr) // assert
	expr.modes = token.modes
	expr.span = token.span
	return expr, nil
}

// Parse a byte or a short number literal.
// byte = number
// short = number "*"
parse_number :: proc(p: ^Parser) -> (expr: Expr, err: Error) {
	token := parser_expect(p, .Number) or_return
	star, is_short := parser_optional(p, .Asterisk)
	span := token.span

	num := token.value.(int) // assert

	if is_short {
		span.end = star.span.end

		if num > int(max(u16)) {
			// TODO: "because there is an asterisk" note
			err = problemf(
				span,
				"value of this short literal is %d, but the max is %d",
				num,
				max(u16),
			)
			return {}, err
		}

		return Expr_Short{u16(num), span}, nil
	} else {
		if num > int(max(u8)) {
			// TODO: "consider appending an asterisk" note
			err = problemf(
				span,
				"value of this byte literal is %d, but the max is %d",
				num,
				max(u8),
			)
			return {}, err
		}

		return Expr_Byte{u8(num), span}, nil
	}
}

@(private)
_escaped :: proc(rune: rune) -> (b: u8, ok: bool) {
	// odinfmt: disable
	switch rune {
	case '"', '\'', '\\': b = u8(rune)
	case '0': b = 0
	case 'a': b = '\a'
	case 'b': b = '\b'
	case 't': b = '\t'
	case 'n': b = '\n'
	case 'v': b = '\v'
	case 'f': b = '\f'
	case 'r': b = '\r'
	case: return 0, false
	}
	// odinfmt: enable

	return b, true
}

// Parse a string literal.
parse_string :: proc(p: ^Parser) -> (expr: Expr_String, err: Error) {
	token := parser_expect(p, .String) or_return

	// Exclude the opening and closing quotes.
	span := token.span
	span.start += 1
	span.end -= 1
	s := parser_slice(p, span)

	expr.bytes = make([dynamic]u8, 0, len(s), p.allocator)
	expr.span = token.span

	escape := false
	for rune in s {
		// TODO: add `\xFF` syntax to insert an arbitrary byte into the string.

		if escape {
			escape = false
			b, ok := _escaped(rune)
			if !ok {
				err = problemf(expr.span, `unknown escape "\%v"`, rune)
				return {}, err
			}
			append(&expr.bytes, b)
		} else if rune == '\\' {
			escape = true
		} else {
			append(&expr.bytes, u8(rune))
		}
	}

	return expr, nil
}

// Parse a character literal.
parse_char :: proc(p: ^Parser) -> (expr: Expr_Char, err: Error) {
	token := parser_expect(p, .Char) or_return

	// Exclude the opening and closing quotes.
	span := token.span
	span.start += 1
	span.end -= 1
	s := parser_slice(p, span)

	expr.span = token.span

	escape := s[0] == '\\'

	if len(s) > (2 if escape else 1) {
		// NOTE: this condition also catches whether a non-ascii char is
		// inside the literal.
		err = problemf(expr.span, `character literals can only contain one ASCII character`)
		return {}, err
	}

	if escape {
		ch := rune(s[1])
		ok: bool
		expr.byte, ok = _escaped(ch)
		if !ok {
			err = problemf(expr.span, `unknown escape "\%v"`, ch)
			return {}, err
		}
	} else {
		expr.byte = s[0]
	}

	return expr, nil
}

// Parse an "if" block.
// if = "if" body ("elif" condition body)* ["else" body]
parse_if :: proc(p: ^Parser) -> (expr: Expr_If, err: Error) {
	// TODO: show `if` example syntax on error.

	// Parse `if` block.
	{
		keyword := parser_expect(p, .Keyword_If) or_return
		body, found := parse_optional_body(p) or_return
		if !found {
			err = problem(keyword.span, "this `if` doesn't have a body")
			return {}, err
		}
		expr.if_block.body = body
		expr.if_block.keyword_span = keyword.span
	}

	// May be we should allocate the array only after we encounter at least one `elif` block?
	expr.elifs_blocks = make([dynamic]Elif_Block, p.allocator)

	// Parse optional `elif` blocks.
	for {
		keyword, found := parser_optional(p, .Keyword_Elif)
		if !found do break

		elif_block: Elif_Block
		elif_block.condition = make([dynamic]Node, p.allocator)

		cond_span: Span
		cond_span, found = parse_optional_condition(p, &elif_block.condition) or_return
		if !found {
			err = problem(keyword.span, "this `elif` doesn't have a condition")
			return {}, err
		}

		elif_block.body, found = parse_optional_body(p) or_return
		if !found {
			err = problem(keyword.span, "this `elif` doesn't have a body")
			return {}, err
		}

		elif_block.condition_span = cond_span
		elif_block.keyword_span = keyword.span

		append(&expr.elifs_blocks, elif_block)
	}

	// Parse optional `else` block.
	else_parse: {
		keyword, found := parser_optional(p, .Keyword_Else)
		if !found do break else_parse

		else_block: If_Block
		else_block.keyword_span = keyword.span

		else_block.body, found = parse_optional_body(p) or_return
		if !found {
			err = problem(keyword.span, "this `else` doesn't have a body")
			return {}, err
		}

		expr.else_block = else_block
	}

	return expr, nil
}

// ------------------------------
// Definitions parsing.
// ------------------------------

// Parse function definition.
// func_def = "fun" name signature body
parse_func_def :: proc(p: ^Parser) -> (def: Func_Def, err: Error) {
	// TODO: show function definition example on error.

	keyword := parser_expect(p, .Keyword_Fun) or_return

	// Parse name.
	{
		found: bool
		def.name, found = parse_optional_name(p)
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				keyword.span,
				"expected a function name after the `fun` keyword, but got a %v",
				token_name(tok),
			)
			return {}, err
		}
	}

	// Parse signature.
	found: bool
	def.signature, found = parse_optional_signature(p) or_return
	if !found {
		span := keyword.span
		span.end = def.name.span.end

		tok := parser_peek_token(p)
		err = problemf(
			span,
			"expected a signature after the function name, but got a %v",
			token_name(tok),
		)
		return {}, err
	}

	// Parse body
	def.body, found = parse_optional_body(p) or_return
	if !found {
		span := keyword.span
		span.end = def.signature.span.end
		return {}, problemf(span, "`%v` function doesn't have a body", def.name.s)
	}

	return def, nil
}

// Parse a function signature.
// signature = "(" "->" | ([arg*] "--" [arg*]) ")"
parse_optional_signature :: proc(p: ^Parser) -> (signature: Signature, found: bool, err: Error) {
	paren: Token
	paren, found = parser_optional(p, .Open_Paren)
	if !found {
		return {}, false, nil
	}

	signature.span = paren.span

	_, is_vec := parser_optional(p, .Skinny_Arrow)
	if is_vec {
		signature.kind = Signature_Vector{}
	} else {
		prc := Signature_Proc{}
		parse_seq(p, &prc.inputs, parse_optional_arg) or_return

		// TODO: "expected a -- after the inputs" error.
		parser_expect(p, .Stick) or_return

		parse_seq(p, &prc.outputs, parse_optional_arg) or_return
		signature.kind = prc
	}

	paren = parser_expect(p, .Close_Paren) or_return

	signature.span.end = paren.span.end
	return signature, true, nil
}

// Optionally parse a stack or function signature argument.
// arg = type [":" name]
parse_optional_arg :: proc(p: ^Parser) -> (arg: Arg, found: bool, err: Error) {
	type: Type
	name: Maybe(Name)

	type, found = parse_optional_type(p) or_return
	if !found {
		return {}, false, nil
	}

	span := type.span

	if _, found := parser_optional(p, .Colon); found {
		n := parse_name(p) or_return

		span.end = n.span.end
		name = n
	}

	return Arg{type, name, span}, true, nil
}

// Parse a variable definition.
// var_def = ["rom"] "var" type name
parse_var_def :: proc(p: ^Parser, in_rom: bool) -> (def: Var_Def, err: Error) {
	if in_rom {
		parser_expect(p, .Keyword_Rom) or_return
	}

	parser_expect(p, .Keyword_Var) or_return

	def.in_rom = in_rom
	def.type = parse_type(p) or_return
	def.name = parse_name(p) or_return

	return def, nil
}

// Parse a constant definition.
// const_def = "const" type name body
parse_const_def :: proc(p: ^Parser) -> (def: Const_Def, err: Error) {
	keyword := parser_expect(p, .Keyword_Const) or_return

	def.type = parse_type(p) or_return
	def.name = parse_name(p) or_return

	found: bool
	def.body, found = parse_optional_body(p) or_return
	if !found {
		span := keyword.span
		span.end = def.name.span.end
		err = problemf(span, "`%v` const doesn't have a body", def.name.s)
		return {}, err
	}

	return def, nil
}

// Parse a data definition.
// data_def = "data" name body
parse_data_def :: proc(p: ^Parser) -> (def: Data_Def, err: Error) {
	keyword := parser_expect(p, .Keyword_Data) or_return

	def.name = parse_name(p) or_return

	found: bool
	def.body, found = parse_optional_body(p) or_return
	if !found {
		span := keyword.span
		span.end = def.name.span.end
		err = problemf(span, "`%v` data doesn't have a body", def.name.s)
		return {}, err
	}

	return def, nil
}

// Parse a user-type definition.
// user_type_def = "type" name type | enum_def | ("struct" "{" field* "}")
parse_user_type_def :: proc(p: ^Parser) -> (def: Node, err: Error) {
	parser_expect(p, .Keyword_Type) or_return
	name := parse_name(p) or_return

	token := parser_peek_token(p)
	#partial switch token.kind {
	case .Keyword_Enum:
		return parse_enum_def(p, name)
	case .Keyword_Struct:
		return parse_struct_def(p, name)
	case:
		base, found := parse_optional_type(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				name.span,
				"expected a type, `enum` or `struct` keyword after the name, but got a %v",
				token_name(tok),
			)
			return {}, err
		}

		alias_def := Type_Alias_Def{name, base}
		return alias_def, nil
	}
}

// Parse enum type definition.
// enum_def = "enum" [type] "{" variant* "}"
parse_enum_def :: proc(p: ^Parser, name: Name) -> (def: Enum_Def, err: Error) {
	keyword := parser_expect(p, .Keyword_Enum) or_return

	def.name = name

	// Parse type
	found: bool
	def.base, found = parse_optional_type(p) or_return
	if !found do def.base.kind = .Byte // enums default to a `byte` as the base type.

	// Parse variants.
	def.variants, found = parse_optional_enum_variants(p) or_return
	if !found {
		// TODO: show enum definition example.
		err = problemf(keyword.span, "`%v` enum type doesn't have a list of variants", name.s)
		return {}, err
	}

	return def, nil
}
parse_optional_enum_variants :: proc(
	p: ^Parser,
) -> (
	variants: [dynamic]Enum_Variant,
	found: bool,
	err: Error,
) {
	_, found = parser_optional(p, .Open_Brace)
	if !found {
		return {}, false, nil
	}

	variants = make([dynamic]Enum_Variant, 0, 4, p.allocator)
	for {
		variant, found := parse_optional_enum_variant(p) or_return
		if !found do break

		append(&variants, variant)
	}

	// TODO: point to the opening brace on error.
	parser_expect(p, .Close_Brace) or_return

	return variants, true, nil
}
// Parse a enum definition variant.
// variant = name [body]
parse_optional_enum_variant :: proc(
	p: ^Parser,
) -> (
	variant: Enum_Variant,
	found: bool,
	err: Error,
) {
	variant.name, found = parse_optional_name(p)
	if !found {
		return {}, false, nil
	}

	variant.body, found = parse_optional_body(p) or_return
	if !found {
		variant.body = nil
	}

	return variant, true, nil
}

parse_struct_def :: proc(p: ^Parser, name: Name) -> (def: Struct_Def, err: Error) {
	keyword := parser_expect(p, .Keyword_Struct) or_return

	_, found := parser_optional(p, .Open_Brace)
	if !found {
		// TODO: show struct definition example.
		err = problemf(keyword.span, "`%v` struct doesn't have a list of fields", name.s)
		return {}, err
	}

	def.name = name
	def.fields = make([dynamic]Struct_Field, 0, 8, p.allocator)

	// Index within the fields array from which fields don't have a type yet and
	// has to update their types according to the nearest ": <type>" syntax. I
	// hope my words make sense...
	untyped_idx := -1
	for {
		field_name, found := parse_optional_name(p)
		if !found do break

		field_idx := len(def.fields)
		field_type: Type

		_, found = parser_optional(p, .Colon)
		if found {
			field_type = parse_type(p) or_return

			if untyped_idx >= 0 {
				// Update type of the previous fields without a type.
				for idx in untyped_idx ..< len(def.fields) {
					// NOTE: it is fine if pointers inside `field_type` struct
					// will point to the same data after copying.
					def.fields[idx].type = field_type
				}
				untyped_idx = -1
			}
		} else if untyped_idx < 0 {
			untyped_idx = field_idx
		}

		field := Struct_Field{field_name, field_type}
		append(&def.fields, field)
	}

	if untyped_idx >= 0 {
		n := len(def.fields) - untyped_idx
		last := slice.last(def.fields[:])

		// TODO: show an example on struct field types.
		err = problemf(
			last.name.span,
			"%d of the fields in the `%s` struct are left untyped",
			n,
			name.s,
		)
		return {}, err
	}

	// TODO: point to the opening brace on error.
	parser_expect(p, .Close_Brace) or_return

	return def, nil
}

// ------------------------------
// Misc nodes.
// ------------------------------

// Parse a type.
// type = "byte" | "short"
//        | ("fun" signature) | ("*" type) | ("^" type)
//        | ("[" [number] "]" type)
//        | ident
parse_optional_type :: proc(p: ^Parser) -> (type: Type, found: bool, err: Error) {
	prev_cursor := p.cursor

	token := parser_next_token(p)
	sliced := parser_slice(p, token.span)
	span := token.span

	#partial switch token.kind {
	case .Ident:
		switch sliced {
		case "byte":
			return Type{.Byte, nil, span}, true, nil
		case "short":
			return Type{.Short, nil, span}, true, nil
		case:
			name := strings.clone(sliced, p.allocator)
			return Type{.User, name, span}, true, nil
		}
	case .Hat:
		ty, found := parse_optional_type(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				token.span,
				`expected a base type for the byte pointer after the "^", but got a %v`,
				token_name(tok),
			)
			return {}, false, err
		}

		base := new_clone(ty, p.allocator)
		span.end = parser_cur_span(p).end
		return Type{.Byte_Ptr, base, span}, true, nil
	case .Asterisk:
		ty, found := parse_optional_type(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				token.span,
				`expected a base type for the short pointer after the "*", but got a %v`,
				token_name(tok),
			)
			return {}, false, err
		}

		base := new_clone(ty, p.allocator)
		span.end = parser_cur_span(p).end
		return Type{.Short_Ptr, base, span}, true, nil
	case .Keyword_Fun:
		sig, found := parse_optional_signature(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				token.span,
				"expected a function signature for the pointer, but got %v",
				token_name(tok),
			)
			return {}, false, err
		}

		base := new_clone(sig, p.allocator)
		span.end = parser_cur_span(p).end
		return Type{.Short_Ptr, base, span}, true, nil
	case:
		p.cursor = prev_cursor
		return {}, false, nil
	}
}
parse_type :: proc(p: ^Parser) -> (type: Type, err: Error) {
	found: bool
	type, found = parse_optional_type(p) or_return
	if !found {
		token := parser_peek_token(p)
		return {}, problemf(token.span, "expected a type, but got a %v", token_name(token))
	}
	return type, nil
}

// Parse a body.
// body = "{" node* "}"
parse_optional_body :: proc(p: ^Parser) -> (body: Body, found: bool, err: Error) {
	brace: Token
	brace, found = parser_optional(p, .Open_Brace)
	if !found {
		return {}, false, nil
	}

	body.nodes = make([dynamic]Node, 0, 32, p.allocator)
	body.start = brace.span

	for {
		token := parser_peek_token(p)
		if token.kind == .EOF || token.kind == .Close_Brace {
			break
		}

		node := parse_next_node(p) or_return
		append(&body.nodes, node)
	}

	brace = parser_expect(p, .Close_Brace) or_return
	body.end = brace.span

	return body, true, nil
}

// Parse a sequence of nodes untill "{"
parse_optional_condition :: proc(
	p: ^Parser,
	nodes: ^[dynamic]Node,
) -> (
	span: Span,
	found: bool,
	err: Error,
) {
	for {
		token := parser_peek_token(p)
		if token.kind == .EOF || token.kind == .Open_Brace {
			break
		}

		if !found {
			found = true
			span.start = token.span.start
		}
		span.end = token.span.end

		node := parse_next_node(p) or_return
		append(nodes, node)
	}

	return span, found, nil
}

// Parse a sequence of nodes.
parse_seq :: proc(
	p: ^Parser,
	list: ^[dynamic]$T,
	f: proc(p: ^Parser) -> (T, bool, Error),
) -> (
	err: Error,
) {
	for {
		node, found := f(p) or_return
		if !found do return nil
		append(list, node)
	}
}

// Parse a symbol name.
// name = ident
parse_name :: proc(p: ^Parser) -> (name: Name, err: Error) {
	token := parser_expect(p, .Ident) or_return
	return parser_new_name(p, token.span), nil
}
parse_optional_name :: proc(p: ^Parser) -> (name: Name, found: bool) {
	token := parser_optional(p, .Ident) or_return
	return parser_new_name(p, token.span), true
}

// ------------------------------
// Helper functions.
// ------------------------------

// Consumes and returns the next token and expect it to be `kind`, otherwise
// returns an error.
parser_expect :: proc(p: ^Parser, kind: Token_Kind) -> (token: Token, err: Error) {
	token = parser_next_token(p)
	if token.kind == kind {
		return token, nil
	} else {
		err = problemf(
			token.span,
			"expected a %v here, but got a %v",
			TOKEN_NAMES[kind],
			token_name(token),
		)
		return {}, err
	}
}
// Consumes and returns the next token if it is `kind`, otherwise does nothing.
parser_optional :: proc(p: ^Parser, kind: Token_Kind) -> (token: Token, found: bool) {
	token = parser_peek_token(p)
	if token.kind == kind {
		parser_advance(p)
		return token, true
	}
	return token, false
}

@(require_results)
parser_slice :: proc(p: ^Parser, span: Span) -> string {
	return span_slice(p.source, span)
}
// Returns the span of the current token.
@(require_results)
parser_cur_span :: proc(p: ^Parser) -> Span {
	return parser_peek_token(p).span
}
// Returns the current token, while skipping comments.
@(require_results)
parser_peek_token :: proc(p: ^Parser) -> Token {
	if p.cursor >= len(p.tokens) {
		// Return the EOF token.
		return slice.last(p.tokens[:])
	}

	for {
		if p.tokens[p.cursor].kind == .Comment {
			parser_advance(p)
			continue
		}
		return p.tokens[p.cursor]
	}
}
// Consumes and returns the current token advancing the cursor, while skipping comments.
parser_next_token :: proc(p: ^Parser) -> Token {
	if p.cursor >= len(p.tokens) {
		// Return the EOF token.
		return slice.last(p.tokens[:])
	}

	token := parser_peek_token(p)
	parser_advance(p)

	return token
}
// Advances the token cursor.
parser_advance :: proc(p: ^Parser) {
	p.cursor += 1
}

// Creates a name from a slice from the source code.
@(require_results)
parser_new_name :: proc(p: ^Parser, span: Span) -> Name {
	sliced := parser_slice(p, span)
	s := strings.clone(sliced, p.allocator)
	return Name{s, span}
}
