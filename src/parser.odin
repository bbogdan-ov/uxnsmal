package uxnsmal

import "core:slice"
import "core:strings"

// TODO: "while parsing ..." note on any parsing error.

// AST parser.
Parser :: struct {
	state:  ^State,
	// List of all tokens in a UXNSMAL source code.
	// Note: Always contains an EOF token at the end.
	tokens: [dynamic]Token,
	// Current token index.
	cursor: int,
}

// Initializes a `Parser` and parses a source code of a file.
// Stores all the parsed nodes into `Parser.nodes`.
//
// Returns `false` if an error has occured and pushes it into the list of problems.
parse :: proc(state: ^State) -> (ok: bool) {
	err := parse_or_err(state)
	if problem, ok := err.(Problem); ok {
		append(&state.problems, problem)
		return false
	}
	return true
}

// Initializes a `Parser` and parses a source code of a file.
// Stores all the parsed nodes into `Parser.nodes`.
@(require_results)
parse_or_err :: proc(state: ^State) -> (err: Error) {
	context.allocator = state.allocator

	// Init parser.
	p: Parser
	p.state = state

	// Init lexer.
	lexer: Lexer
	lexer_init(&lexer, state.source)

	// Collect all tokens.
	p.tokens = make([dynamic]Token, 0, 32)
	for {
		token := lexer_next(&lexer) or_return
		append(&p.tokens, token) // NOTE: collecting an EOF token too.
		if token.kind == .EOF do break
	}

	// Skip all comments at the beginning of the source code.
	parser_advance(&p)
	p.cursor -= 1

	for {
		token := parser_peek_token(&p)
		if token.kind == .EOF do break

		node := parse_next_node(&p) or_return
		append(&state.nodes, node)
	}

	return nil
}

parse_next_node :: proc(p: ^Parser) -> (node: Node, err: Error) {
	token := parser_peek_token(p)

	#partial switch token.kind {
	// Definitions
	case .Keyword_Fun:
		def := parse_def_func(p) or_return
		return def, nil
	case .Keyword_Var, .Keyword_Rom:
		def := parse_def_var(p, token.kind == .Keyword_Rom) or_return
		return def, nil
	case .Keyword_Const:
		def := parse_def_const(p) or_return
		return def, nil
	case .Keyword_Data:
		def := parse_def_data(p) or_return
		return def, nil
	case .Keyword_Type:
		return parse_def_user_type(p)

	case .Ident, .Ampersand:
		return parse_expr_symbol(p, token.kind == .Ampersand)
	case .Intr:
		return parse_expr_intr(p)
	case .Number:
		return parse_expr_number(p)
	case .String:
		return parse_expr_string(p)
	case .Char:
		return parse_expr_char(p)

	case .Skinny_Arrow:
		return parse_expr_store(p)
	case .Colon:
		return parse_expr_bind(p)
	case .Open_Paren:
		return parse_expr_expect(p)
	case .Keyword_As:
		return parse_expr_cast(p)

	case .Label:
		label := parse_label(p) or_return
		token := parser_peek_token(p)
		#partial switch token.kind {
		case .Open_Brace:
			return parse_expr_block(p, label)
		case .Keyword_If:
			return parse_expr_if(p, label)
		case .Keyword_While:
			return parse_expr_while(p, label)
		case:
			// TODO: but what is the right syntax?
			MSG :: "expected either a `{{`, `if` or `while` after the label, but got a %v"
			err = problemf(label.span, MSG, token_name(token))
			return {}, err
		}
	case .Keyword_If:
		return parse_expr_if(p, nil)
	case .Keyword_While:
		return parse_expr_while(p, nil)
	case .Keyword_Break:
		return parse_expr_break(p)

	case .Keyword_Enum, .Keyword_Struct, .Keyword_Else, .Keyword_Elif:
		err = problemf(token.span, "TODO: show how to correctly use %s", token.kind)
		return {}, err

	case:
		return {}, problemf(token.span, "unexpected %s", token_name(token))
	}
}

// ------------------------------
// Expressions parsing.
// ------------------------------

// Parse a symbol use (e.g. a function call, variable access, etc).
// symbol = ["&"] name ("." name ["[]"])*
parse_expr_symbol :: proc(p: ^Parser, as_ptr: bool) -> (expr: Expr_Symbol, err: Error) {
	ptr_token: Token
	if as_ptr {
		ptr_token = parser_expect(p, .Ampersand) or_return
	}

	// May be we should allocate the array only after we encounter at least one name?
	members := make([dynamic]Member)

	for {
		name := parse_name(p) or_return
		span := name.span
		as_array_count := 0
		brackets_span: Span

		// Check if it is an array access (`member[]`).
		for {
			open := parser_optional(p, .Open_Bracket) or_break
			close, found := parser_optional(p, .Close_Bracket)
			if !found {
				tok := close
				// TODO: show an example of accessing an array.
				err = problemf(
					open.span,
					"expected a `]` after the `[`, but got a %s",
					token_name(tok),
				)
				return {}, err
			}

			if as_array_count == 0 {
				brackets_span = open.span
			}
			brackets_span.end = close.span.end

			span.end = close.span.end
			as_array_count += 1
		}

		append(&members, Member{name, as_array_count, span, brackets_span})

		_, found := parser_optional(p, .Dot)
		if !found do break

		// Collect next members after the dot...
	}

	assert(len(members) >= 1)

	span := ptr_token.span if as_ptr else members[0].span
	span.end = slice.last(members[:]).span.end

	return {members, as_ptr, span}, nil
}

// Parse an intrinsic call.
parse_expr_intr :: proc(p: ^Parser) -> (expr: Expr_Intr, err: Error) {
	token := parser_expect(p, .Intr) or_return
	kind := token.value.(Intr) // assert
	return {kind, token.modes, token.span}, nil
}

// Parse a byte or a short number literal.
// byte = number
// short = number "*"
parse_expr_number :: proc(p: ^Parser) -> (expr: Node, err: Error) {
	token := parser_expect(p, .Number) or_return
	star, is_short := parser_optional(p, .Asterisk)
	span := token.span

	num := token.value.(u32) // assert

	if is_short {
		span.end = star.span.end

		if num > u32(max(u16)) {
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
		if num > u32(max(u8)) {
			err := problemf(
				span,
				"value of this byte literal is %d, but the max is %d",
				num,
				max(u8),
			)
			// TODO: should probaly say "help:" instead of "note:"
			problem_notef(&err, span, "try adding a `*` after the number to make it a short")
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
parse_expr_string :: proc(p: ^Parser) -> (expr: Expr_String, err: Error) {
	token := parser_expect(p, .String) or_return

	// Exclude the opening and closing quotes.
	str_span := token.span
	str_span.start += 1
	str_span.end -= 1
	s := parser_slice(p, str_span)

	bytes := make([dynamic]u8, 0, len(s))
	span := token.span

	escape := false
	for rune in s {
		// TODO: add `\xFF` syntax to insert an arbitrary byte into the string.

		if escape {
			escape = false
			b, ok := _escaped(rune)
			if !ok {
				err = problemf(span, `unknown escape "\%s"`, rune)
				return {}, err
			}
			append(&bytes, b)
		} else if rune == '\\' {
			escape = true
		} else {
			append(&bytes, u8(rune))
		}
	}

	return {bytes, span}, nil
}

// Parse a character literal.
parse_expr_char :: proc(p: ^Parser) -> (expr: Expr_Byte, err: Error) {
	token := parser_expect(p, .Char) or_return

	// Exclude the opening and closing quotes.
	str_span := token.span
	str_span.start += 1
	str_span.end -= 1
	s := parser_slice(p, str_span)

	span := token.span

	escape := s[0] == '\\'

	if len(s) > (2 if escape else 1) {
		// NOTE: this condition also catches whether a non-ascii char is
		// inside the literal.
		err = problemf(span, "character literals can only contain one ASCII character")
		return {}, err
	}

	value: u8
	if escape {
		ch := rune(s[1])
		ok: bool
		value, ok = _escaped(ch)
		if !ok {
			err = problemf(span, `unknown escape "\%s"`, ch)
			return {}, err
		}
	} else {
		value = s[0]
	}

	return {value, span}, nil
}

// Parse a store expression.
// store = "->" symbol
parse_expr_store :: proc(p: ^Parser) -> (expr: Expr_Store, err: Error) {
	arrow := parser_expect(p, .Skinny_Arrow) or_return

	// This is only for the cool error message. Pointers to a symbol are not
	// allowed in store expressions.
	as_ptr := false

	token, found := parser_optional(p, .Ampersand)
	if found {
		as_ptr = true
	} else if token.kind != .Ident {
		err = problemf(
			arrow.span,
			"expected a symbol after the `->`, but got a %s",
			token_name(token),
		)
		return {}, err
	}

	symbol := parse_expr_symbol(p, as_ptr) or_return
	if symbol.as_ptr {
		MSG :: "expected a symbol here, but got a pointer to a symbol, which is not allowed"
		err := problemf(symbol.span, MSG)
		problem_notef(&err, symbol.span, "try removing the `&`")
		return {}, err
	}

	span := arrow.span
	span.end = symbol.span.end
	return {symbol, span}, nil
}

// Parse a name binding expression
// bind = ":" "(" name* ")"
parse_expr_bind :: proc(p: ^Parser) -> (expr: Expr_Bind, err: Error) {
	// TODO: show a name binding example syntax on error.

	colon := parser_expect(p, .Colon) or_return

	names := make([dynamic]Name)
	span := colon.span

	open, found := parser_optional(p, .Open_Paren)
	if !found {
		tok := open
		err = problemf(
			colon.span,
			"expected a list of binding names after the `:`, but got a %s",
			token_name(tok),
		)
		return {}, err
	}

	for {
		name, found := parse_optional_name(p)
		if !found do break
		append(&names, name)
	}

	close: Token
	close, found = parser_optional(p, .Close_Paren)
	if !found {
		tok := close
		err := problemf(
			tok.span,
			"expected either a `)` or a name here, but got a %s",
			token_name(tok),
		)
		problem_notef(&err, open.span, "while parsing this list of names")
		return {}, err
	}

	span.end = close.span.end

	return {names, span}, nil
}

// Parse binded names expectation expressions.
// expect = "(" name* ")"
parse_expr_expect :: proc(p: ^Parser) -> (expr: Expr_Expect, err: Error) {
	open := parser_expect(p, .Open_Paren) or_return
	span := open.span

	names := make([dynamic]Name)

	for {
		name, found := parse_optional_name(p)
		if !found do break
		append(&names, name)
	}

	close, found := parser_optional(p, .Close_Paren)
	if !found {
		tok := close
		err := problemf(
			tok.span,
			"expected either a `)` or a name here, but got a %s",
			token_name(tok),
		)
		problem_notef(&err, open.span, "while parsing this list of names")
		return {}, err
	}

	span.end = close.span.end

	return {names, span}, nil
}

// Parse a cast expression.
// cast = "as" ["!"] "(" type* ")"
parse_expr_cast :: proc(p: ^Parser) -> (expr: Expr_Cast, err: Error) {
	// TODO: show a cast example syntax on error.

	keyword := parser_expect(p, .Keyword_As) or_return
	span := keyword.span

	_, force := parser_optional(p, .Bang)

	open, found := parser_optional(p, .Open_Paren)
	if !found {
		err = problemf(keyword.span, "this cast is missing a list of types")
		return {}, err
	}

	types := make([dynamic]Spanned(Type))

	for {
		complex, found := parse_optional_type(p) or_return
		if !found do break

		type := to_stack_type(complex.x, complex.span) or_return
		append(&types, Spanned(Type){type, complex.span})
	}

	close: Token
	close, found = parser_optional(p, .Close_Paren)
	if !found {
		MSG :: "expected either a `)` or a type here, but got a %s"
		tok := close
		err := problemf(tok.span, MSG, token_name(tok))
		problem_notef(&err, open.span, "while parsing this list of types")
		return {}, err
	}

	span.end = close.span.end

	return {types, force, span, keyword.span}, nil
}

// Parse a labeled block.
// block = label "{" node* "}"
parse_expr_block :: proc(p: ^Parser, label: Name) -> (expr: Expr_Block, err: Error) {
	body, found := parse_optional_body(p) or_return
	assert(found) // Body existance must be checked when parsing the label.

	return {label, body}, nil
}

// Parse an `if` block.
// if = [label] "if" body ("elif" condition body)* ["else" body]
parse_expr_if :: proc(p: ^Parser, label: Maybe(Name)) -> (expr: Expr_If, err: Error) {
	// TODO: show `if` example syntax on error.

	if_block: If_Block
	else_block: If_Block

	// Parse `if` block.
	{
		keyword := parser_expect(p, .Keyword_If) or_return
		body, found := parse_optional_body(p) or_return
		if !found {
			err = problemf(keyword.span, "this `if` is missing a body")
			return {}, err
		}
		if_block.body = body
		if_block.keyword_span = keyword.span
	}

	// May be we should allocate the array only after we encounter at least one `elif` block?
	elif_blocks := make([dynamic]Elif_Block)

	// Parse optional `elif` blocks.
	elif_parse: for {
		keyword, found := parser_optional(p, .Keyword_Elif)
		if !found do break elif_parse

		elif_block: Elif_Block
		elif_block.condition = make([dynamic]Node)

		cond_span: Span
		cond_span, found = parse_optional_condition(p, &elif_block.condition) or_return
		if !found {
			tok := parser_peek_token(p)
			// TODO: show what a "condition" is.
			err = problemf(
				keyword.span,
				"expected a condition after the keyword `elif`, but got a %s",
				token_name(tok),
			)
			return {}, err
		}

		elif_block.body, found = parse_optional_body(p) or_return
		if !found {
			span := keyword.span
			span.end = cond_span.end
			err = problemf(span, "this `elif` is missing a body")
			return {}, err
		}

		elif_block.condition_span = cond_span
		elif_block.keyword_span = keyword.span

		append(&elif_blocks, elif_block)
	}

	// Parse optional `else` block.
	else_parse: {
		keyword, found := parser_optional(p, .Keyword_Else)
		if !found do break else_parse

		else_block.keyword_span = keyword.span

		else_block.body, found = parse_optional_body(p) or_return
		if !found {
			err = problemf(keyword.span, "this `else` is missing a body")
			return {}, err
		}
	}

	expr = Expr_If{label, if_block, elif_blocks, else_block}
	return expr, nil
}

// Parse a `while` block.
// while = [label] "while" condition body
parse_expr_while :: proc(p: ^Parser, label: Maybe(Name)) -> (expr: Expr_While, err: Error) {
	keyword := parser_expect(p, .Keyword_While) or_return

	condition := make([dynamic]Node)
	cond_span, found := parse_optional_condition(p, &condition) or_return
	if !found {
		tok := parser_peek_token(p)
		// TODO: show what a "condition" is.
		err = problemf(
			keyword.span,
			"expected a condition after the keyword `while`, but got a %s",
			token_name(tok),
		)
		return {}, err
	}

	body: Body
	body, found = parse_optional_body(p) or_return
	if !found {
		// TODO: show `while` syntax example.
		err = problemf(keyword.span, "this `while` is missing a body")
		return {}, err
	}

	expr = Expr_While{label, condition, cond_span, body, keyword.span}
	return expr, nil
}

// Parse a break expression.
// break = "break" label
parse_expr_break :: proc(p: ^Parser) -> (expr: Expr_Break, err: Error) {
	keyword := parser_expect(p, .Keyword_Break) or_return
	label := parse_label(p) or_return
	span := keyword.span
	span.end = label.span.end
	return {label, span}, nil
}

// ------------------------------
// Definitions parsing.
// ------------------------------

// Parse function definition.
// def_func = "fun" name signature body
parse_def_func :: proc(p: ^Parser) -> (def: Def_Func, err: Error) {
	// TODO: show function definition example on error.

	keyword := parser_expect(p, .Keyword_Fun) or_return
	name := parse_name(p) or_return

	head := keyword.span
	head.end = name.span.end

	// Parse signature.
	signature, found := parse_optional_signature(p) or_return
	if !found {
		err = problemf(head, "this function definition is missing a signature")
		return {}, err
	}

	// Parse body
	body: Body
	body, found = parse_optional_body(p) or_return
	if !found {
		err = problemf(head, "this function definition is missing a body")
		return {}, err
	}

	symbol := Symbol_Func {
		id         = make_id(p.state),
		name       = name,
		signature  = signature,
		defined_at = name.span,
	}
	symbol_define(p.state, new_clone(symbol)) or_return

	return Def_Func{name, signature, body}, nil
}

// Parse a function signature.
// signature = "(" "->" | ([pairs] "--" [pairs]) ")"
parse_optional_signature :: proc(p: ^Parser) -> (signature: Signature, found: bool, err: Error) {
	// TODO!!: allow specify whether the arguments names are optional.
	// It is useful for defining function pointers.
	paren: Token
	paren, found = parser_optional(p, .Open_Paren)
	if !found {
		return {}, false, nil
	}

	span := paren.span
	kind: Signature_Kind

	_, is_vec := parser_optional(p, .Skinny_Arrow)
	if is_vec {
		kind = Signature_Vector{}
	} else {
		inputs := make([dynamic]Pair, context.temp_allocator)
		outputs := make([dynamic]Pair, context.temp_allocator)

		parse_optional_pairs(p, &inputs) or_return
		// TODO: "expected a -- after the inputs" error.
		parser_expect(p, .Stick) or_return
		parse_optional_pairs(p, &outputs) or_return

		prc := Signature_Proc {
			inputs  = make([dynamic]Arg, len(inputs)),
			outputs = make([dynamic]Arg, len(outputs)),
		}

		for input, idx in inputs {
			arg := &prc.inputs[idx]
			arg.type.x = to_stack_type(input.type.x, input.type.span) or_return
			arg.type.span = input.type.span
			arg.name = input.name
		}
		for output, idx in outputs {
			arg := &prc.outputs[idx]
			arg.type.x = to_output_type(output.type.x, "output", output.type.span) or_return
			arg.type.span = output.type.span
			arg.name = output.name
		}

		kind = prc
	}

	paren = parser_expect(p, .Close_Paren) or_return

	span.end = paren.span.end
	return Signature{kind, span}, true, nil
}

// Parse a variable definition.
// def_var = ["rom"] "var" (name+ ":" type)+
parse_def_var :: proc(p: ^Parser, in_rom: bool) -> (def: Def_Var, err: Error) {
	if in_rom {
		parser_expect(p, .Keyword_Rom) or_return
	}

	keyword := parser_expect(p, .Keyword_Var) or_return

	pairs := make([dynamic]Pair)
	// TODO!!: variable definition should allow only one `name+ ":" type`.
	parse_optional_pairs(p, &pairs) or_return

	if len(pairs) == 0 {
		tok := parser_peek_token(p)
		err = problemf(
			keyword.span,
			"expected a name after the keyword `var`, but got a %s",
			token_name(tok),
		)
		return {}, err
	}

	for pair in pairs {
		size := complex_type_size(pair.type.x, pair.type.span) or_return
		symbol := Symbol_Var {
			id         = make_id(p.state),
			name       = pair.name,
			type       = pair.type.x,
			size       = size,
			in_rom     = in_rom,
			defined_at = pair.name.span,
		}
		symbol_define(p.state, new_clone(symbol)) or_return
	}

	span := pairs[0].name.span
	span.end = slice.last(pairs[:]).name.span.end
	return Def_Var{pairs, in_rom, span}, nil
}

// Parse a constant definition.
// def_const = "const" name type body
parse_def_const :: proc(p: ^Parser) -> (def: Def_Const, err: Error) {
	keyword := parser_expect(p, .Keyword_Const) or_return
	name := parse_name(p) or_return
	complex := parse_type(p) or_return

	head := keyword.span
	head.end = name.span.end

	body, found := parse_optional_body(p) or_return
	if !found {
		// TODO: show definition example.
		err = problemf(head, "this constant definition is missing a body")
		return {}, err
	}

	type := to_output_type(complex.x, "constant", complex.span) or_return

	symbol := Symbol_Const {
		id         = make_id(p.state),
		name       = name,
		type       = type,
		defined_at = name.span,
	}
	ptr := new_clone(symbol)
	symbol_define(p.state, ptr) or_return

	return Def_Const{ptr, body}, nil
}

// Parse a data definition.
// def_data = "data" name body
parse_def_data :: proc(p: ^Parser) -> (def: Def_Data, err: Error) {
	parser_expect(p, .Keyword_Data) or_return

	name := parse_name(p) or_return

	body, found := parse_optional_body(p) or_return
	if !found {
		// TODO: show definition example.
		err = problemf(name.span, "this data definition is missing a body")
		return {}, err
	}

	symbol := Symbol_Data {
		id         = make_id(p.state),
		name       = name,
		defined_at = name.span,
	}
	symbol_define(p.state, new_clone(symbol)) or_return

	return Def_Data{name, body}, nil
}

// Parse a user-type definition.
// def_user_type = "type" name type | enum_def | struct_def
parse_def_user_type :: proc(p: ^Parser) -> (node: Node, err: Error) {
	keyword := parser_expect(p, .Keyword_Type) or_return
	name := parse_name(p) or_return

	token := parser_peek_token(p)
	#partial switch token.kind {
	case .Keyword_Enum:
		return parse_def_enum(p, name, keyword.span)
	case .Keyword_Struct:
		return parse_def_struct(p, name, keyword.span)
	case:
		derived, found := parse_optional_type(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				name.span,
				"expected a type, `enum` or `struct` keyword after the name, but got a %s",
				token_name(tok),
			)
			return {}, err
		}

		symbol := Symbol_Alias {
			name       = name,
			derived    = derived.x,
			defined_at = name.span,
		}
		symbol_define(p.state, new_clone(symbol)) or_return

		return Def_Alias{name}, nil
	}
}

// Parse enum type definition.
// enum_def = "enum" [type] "{" variant* "}"
parse_def_enum :: proc(p: ^Parser, name: Name, keyword_span: Span) -> (def: Def_Enum, err: Error) {
	enum_kw := parser_expect(p, .Keyword_Enum) or_return

	// Parse type
	derived, found := parse_optional_type(p) or_return
	if !found {
		// Enums default to a byte as a derived type.
		derived = {Type(Type_Byte{}), Span{}}
	}

	// Parse variants.
	open: Token
	open, found = parser_optional(p, .Open_Brace)
	if !found {
		// TODO: show enum definition example.
		span := keyword_span
		span.end = enum_kw.span.end
		err = problemf(span, "this enum definition is missing a list of variants")
		return {}, err
	}

	variants := make(map[string]Enum_Variant)
	for {
		variant, found := parse_optional_enum_variant(p) or_return
		if !found do break

		prev, was_prev := variants[variant.name.s]
		if was_prev {
			err := problemf(
				variant.name.span,
				"variant `%s` redefinition in the enum `%s`",
				variant.name.s,
				name.s,
			)
			problem_notef(&err, prev.name.span, "previously defined here")
			return {}, err
		}

		assert(len(variant.name.s) > 0)
		map_insert(&variants, variant.name.s, variant)
	}

	_, found = parser_optional(p, .Close_Brace)
	if !found {
		err = problemf(open.span, "this list of variants is not closed")
		return {}, err
	}

	// Defining a symbol.
	derived_type, valid := derived.x.(Type)
	valid &= type_is_basic(derived_type)
	if !valid {
		err := problemf(derived.span, "enums can only derive from a byte or a short")
		return {}, err
	}

	symbol := Symbol_Enum {
		id         = make_id(p.state),
		name       = name,
		derived    = derived_type,
		defined_at = name.span,
		variants   = variants,
	}
	ptr := new_clone(symbol)
	symbol_define(p.state, ptr) or_return

	return Def_Enum{ptr}, nil
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

// Parse a struct type definition.
// struct_def = "struct" "{" [pairs] "}"
parse_def_struct :: proc(
	p: ^Parser,
	name: Name,
	keyword_span: Span,
) -> (
	def: Def_Struct,
	err: Error,
) {
	struct_kw := parser_expect(p, .Keyword_Struct) or_return

	open, found := parser_optional(p, .Open_Brace)
	if !found {
		span := keyword_span
		span.end = struct_kw.span.end
		err = problemf(span, "this struct definition is missing a list fields")
		return {}, err
	}

	pairs := make([dynamic]Pair, context.temp_allocator)
	parse_optional_pairs(p, &pairs) or_return

	_, found = parser_optional(p, .Close_Brace)
	if !found {
		err = problemf(open.span, "this list of fields is not closed")
		return {}, err
	}

	size: u32 = 0
	fields := make(map[string]Pair)
	for pair in pairs {
		prev, was_prev := fields[pair.name.s]
		if was_prev {
			err := problemf(
				pair.name.span,
				"field `%s` redefinition in the struct `%s`",
				pair.name.s,
				name.s,
			)
			problem_notef(&err, prev.name.span, "previously defined here")
			return {}, err
		}

		assert(len(pair.name.s) > 0)
		fields[pair.name.s] = pair
		size += complex_type_size(pair.type.x, pair.type.span) or_return
	}

	symbol := Symbol_Struct {
		name       = name,
		defined_at = name.span,
		fields     = fields,
		size       = size,
	}
	ptr := new_clone(symbol)
	symbol_define(p.state, ptr) or_return

	return Def_Struct{ptr}, nil
}

// ------------------------------
// Misc nodes.
// ------------------------------

// Parse a sequence of pairs.
// pairs = (name+ ":" type)*
@(require_results)
parse_optional_pairs :: proc(p: ^Parser, pairs: ^[dynamic]Pair) -> (err: Error) {
	// Index within the pairs array from which pairs don't have a type yet and
	// has to update their types according to the nearest ": <type>" syntax. I
	// hope my words make sense...
	untyped_idx := -1
	for {
		name, found := parse_optional_name(p)
		if !found do break

		idx := len(pairs)
		type: Spanned(Complex_Type)

		_, found = parser_optional(p, .Colon)
		if found {
			type = parse_type(p) or_return

			if untyped_idx >= 0 {
				// Update type of the previous pairs without a type.
				for idx in untyped_idx ..< len(pairs) {
					// NOTE: it is fine if pointers inside `pair_type` struct
					// will point to the same data after copying.
					pairs[idx].type = type
				}
				untyped_idx = -1
			}
		} else if untyped_idx < 0 {
			untyped_idx = idx
		}

		append(pairs, Pair{name, type})
	}

	if untyped_idx >= 0 {
		last := slice.last(pairs[:])
		tok := parser_peek_token(p)
		err = problemf(
			last.name.span,
			"expected a `:` followed by a type after the name, but got a %s",
			token_name(tok),
		)
		return err
	}

	return nil
}

// Parse a type.
// type = "byte" | "short"
//        | ("fun" signature) | ("*" type) | ("^" type)
//        | ("[" [number] "]" type)
//        | ident
parse_optional_type :: proc(p: ^Parser) -> (type: Spanned(Complex_Type), found: bool, err: Error) {
	prev_cursor := p.cursor

	token := parser_next_token(p)
	sliced := parser_slice(p, token.span)

	type.span = token.span
	found = true
	err = nil

	#partial switch token.kind {
	case .Ident:
		switch sliced {
		case "byte":
			type.x = Type(Type_Byte{})
			return
		case "short":
			type.x = Type(Type_Short{})
			return
		case:
			// Parsing a user type.
			symbol, found := &p.state.symbols[sliced]
			if !found {
				// TODO: note that the definitions order matters.
				err := problemf(token.span, "undefined type `%s`", sliced)
				return {}, false, err
			}

			#partial switch s in symbol {
			case ^Symbol_Alias:
				// TODO!: store "a.k.a. AliasName" for better error messages.
				type.x = s.derived
				return
			case ^Symbol_Enum:
				type.x = Type(s)
				return
			case ^Symbol_Struct:
				type.x = s
				return
			case:
				defined := symbol_defined_at(symbol^)
				err := err_symbol(
					token.span,
					defined,
					"expected a type, but got a %s `%s`",
					symbol_kind_str(symbol^),
					sliced,
				)
				return {}, false, err
			}
		}
	case .Hat:
		base, found := parse_optional_type(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				token.span,
				"expected a base type for the byte pointer after the `^`, but got a %s",
				token_name(tok),
			)
			return {}, false, err
		}

		type.x = Type(Type_Byte_Ptr{new_clone(base.x)})
		type.span.end = parser_cur_span(p).end
		return
	case .Asterisk:
		base, found := parse_optional_type(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				token.span,
				"expected a base type for the short pointer after the `*`, but got a %s",
				token_name(tok),
			)
			return {}, false, err
		}

		type.x = Type(Type_Short_Ptr{new_clone(base.x)})
		type.span.end = parser_cur_span(p).end
		return
	case .Keyword_Fun:
		sig, found := parse_optional_signature(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				token.span,
				"expected a signature for the function pointer after the keyword `fun`, but got a %s",
				token_name(tok),
			)
			return {}, false, err
		}

		type.x = Type(Type_Func_Ptr{sig})
		type.span.end = parser_cur_span(p).end
		return
	case .Open_Bracket:
		// Parse array qualifier.
		num_tok, _ := parser_optional(p, .Number)

		nodes := make([dynamic]Node)
		for {
			cur := parser_peek_token(p)
			if cur.kind == .Close_Bracket do break

			node := parse_next_node(p) or_return
			append(&nodes, node)
		}

		open := token
		close := parser_expect(p, .Close_Bracket) or_return

		qualifier_span := open.span
		qualifier_span.end = close.span.end

		if len(nodes) > 0 {
			// TODO: "you can't put expressions here because there is no
			// comp-time evaluation yet" help
			// TODO: span all nodes.
			err = problemf(
				qualifier_span,
				"only a number literal can be used as a count for an array yet...",
			)
			return {}, false, err
		}

		// Parse base type.
		base, found := parse_optional_type(p) or_return
		if !found {
			tok := parser_peek_token(p)
			err = problemf(
				qualifier_span,
				"expected a base type for the array after the qualifier, but got a %s",
				token_name(tok),
			)
			return {}, false, err
		}

		type.span.end = base.span.end

		if num_tok.kind == .Number {
			// NOTE: allow any count, the size of the array will be checked at
			// the compile stage.
			count := num_tok.value.(u32) // assert
			type.x = Type_Array{new_clone(base.x), count}
			return
		} else {
			type.x = Type_Unsized_Array{new_clone(base.x)}
			return
		}
	case:
		p.cursor = prev_cursor
		return {}, false, nil
	}
}
parse_type :: proc(p: ^Parser) -> (type: Spanned(Complex_Type), err: Error) {
	found: bool
	type, found = parse_optional_type(p) or_return
	if !found {
		token := parser_peek_token(p)
		err := problemf(token.span, "expected a type here, but got a %s", token_name(token))
		return {}, err
	}
	return
}

// Parse a body.
// body = "{" node* "}"
parse_optional_body :: proc(p: ^Parser) -> (body: Body, found: bool, err: Error) {
	open: Token
	open, found = parser_optional(p, .Open_Brace)
	if !found {
		return {}, false, nil
	}

	body.nodes = make([dynamic]Node)
	body.start = open.span

	brace_depth := 0

	loop: for {
		token := parser_peek_token(p)
		#partial switch token.kind {
		case .Open_Brace:
			brace_depth += 1
			parser_advance(p)
		case .Close_Brace:
			if brace_depth >= 1 {
				brace_depth -= 1
				parser_advance(p)
			} else {
				break loop
			}
		case .EOF:
			break loop
		case:
			node := parse_next_node(p) or_return
			append(&body.nodes, node)
		}
	}

	close: Token
	close, found = parser_optional(p, .Close_Brace)
	if !found {
		err = problemf(open.span, "this block is not closed")
		return {}, false, err
	}
	body.end = close.span

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

parse_label :: proc(p: ^Parser) -> (name: Name, err: Error) {
	token := parser_expect(p, .Label) or_return
	span := token.span
	span.start += 1 // exclude "@"
	name = parser_make_name(p, span)
	name.span = token.span
	return name, nil
}
// Parse a symbol name.
// name = ident
parse_name :: proc(p: ^Parser) -> (name: Name, err: Error) {
	token := parser_expect(p, .Ident) or_return
	return parser_make_name(p, token.span), nil
}
parse_optional_name :: proc(p: ^Parser) -> (name: Name, found: bool) {
	token := parser_optional(p, .Ident) or_return
	return parser_make_name(p, token.span), true
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
			"expected a %s here, but got a %s",
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
	return span_slice(p.state.source, span)
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

// Create a name from a source code slice.
@(require_results)
parser_make_name :: proc(p: ^Parser, span: Span) -> Name {
	sliced := parser_slice(p, span)
	s := strings.clone(sliced)
	return Name{s, span}
}
