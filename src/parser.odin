#+vet explicit-allocators

package uxnsmal

import "base:runtime"
import "core:slice"
import "core:strings"

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

	for {
		token := parser_peek_token(p)
		if token.kind == .EOF do break

		#partial switch token.kind {
		case .Keyword:
			_parse_keyword(p, token) or_return
		case:
			return problemf(token.span, "unexpected %v", token_name(token))
		}
	}

	return nil
}

@(private, require_results)
_parse_keyword :: proc(p: ^Parser, token: Token) -> (err: Error) {
	switch token.keyword {
	case .None:
		panic("keyword cannot be .None")
	case .Fun:
		def := parse_func_def(p) or_return
		append(&p.file.nodes, def)
		return nil
	case .Var:
		panic("TODO: parse var definition")
	case .Const:
		panic("TODO: parse const definition")
	case .Data:
		panic("TODO: parse data definition")
	case .Alias:
		panic("TODO: parse alias definition")
	}

	unreachable()
}

// Parse function definition.
// func_def = "fun" name signature block
@(require_results)
parse_func_def :: proc(p: ^Parser) -> (def: Func_Def, err: Error) {
	_ = parser_expect_keyword(p, .Fun) or_return
	name := parse_name(p) or_return
	signature := parse_signature(p) or_return

	def = Func_Def {
		name      = name,
		signature = signature,
	}
	return def, nil
}

// Parse a function signature.
// signature = "(" "->" | ([arg*] "--" [arg*]) ")"
@(require_results)
parse_signature :: proc(p: ^Parser) -> (signature: Signature, err: Error) {
	open := parser_expect(p, .Open_Paren) or_return
	signature.span = open.span

	_, is_vec := parser_optional(p, .Skinny_Arrow)
	if is_vec {
		signature.kind = Signature_Vector{}
	} else {
		prc := Signature_Proc{}
		parse_args(p, &prc.inputs) or_return
		_ = parser_expect(p, .Stick) or_return
		parse_args(p, &prc.outputs) or_return
		signature.kind = prc
	}

	close := parser_expect(p, .Close_Paren) or_return

	signature.span.end = close.span.end
	return signature, nil
}
// Parse a list of arguments.
@(require_results)
parse_args :: proc(p: ^Parser, list: ^[dynamic]Arg) -> (err: Error) {
	for {
		arg, found := optional_parse_arg(p) or_return
		if !found {
			return nil
		}

		append(list, arg)
	}
}
// Optionally parse a stack or function signature argument.
// arg = type [":" name]
@(require_results)
optional_parse_arg :: proc(p: ^Parser) -> (arg: Arg, found: bool, err: Error) {
	type: Type
	name: Maybe(Name)

	type, err = parse_type(p)
	if err != nil {
		// If it couldn't parse a type, apparently there is no type.
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

@(require_results)
parse_type :: proc(p: ^Parser) -> (type: Type, err: Error) {
	token := parser_next_token(p)
	word := span_slice(p.source, token.span)
	span := token.span

	#partial switch token.kind {
	case .Ident:
		switch word {
		case "byte":
			return Type{.Byte, nil, span}, nil
		case "short":
			return Type{.Short, nil, span}, nil
		case:
			return {}, problemf(token.span, "unknown type `%v`", word)
		}
	case .Hat:
		ty := parse_type(p) or_return
		base := new_clone(ty, p.allocator)
		span.end = parser_cur_span(p).end
		return Type{.Byte_Ptr, base, span}, nil
	case .Asterisk:
		ty := parse_type(p) or_return
		base := new_clone(ty, p.allocator)
		span.end = parser_cur_span(p).end
		return Type{.Short_Ptr, base, span}, nil
	case .Keyword:
		if token.keyword != .Fun {
			return {}, problemf(token.span, "expected a type, but got a %v", token_name(token))
		}

		sig := parse_signature(p) or_return
		base := new_clone(sig, p.allocator)
		span.end = parser_cur_span(p).end
		return Type{.Short_Ptr, base, span}, nil
	case:
		return {}, problemf(token.span, "expected a type, but got a %v", token_name(token))
	}
}

// Parse a symbol name.
// name = ident
@(require_results)
parse_name :: proc(p: ^Parser) -> (name: Name, err: Error) {
	token := parser_expect(p, .Ident) or_return
	word := span_slice(p.source, token.span)

	s := strings.clone(word, p.allocator)
	return Name{s, token.span}, nil
}

// Consumes and returns the next token and expect it to be `kind`, otherwise
// returns an error.
@(require_results)
parser_expect :: proc(p: ^Parser, kind: Token_Kind) -> (token: Token, err: Error) {
	token = parser_next_token(p)
	if token.kind == kind {
		return token, nil
	} else {
		return {}, problemf(token.span, "expected a %v, but got a %v", TOKEN_NAMES[kind], token_name(token))
	}
}
@(require_results)
parser_expect_keyword :: proc(p: ^Parser, keyword: Keyword_Kind) -> (token: Token, err: Error) {
	found: bool
	token, found = parser_optional(p, .Keyword)
	if !found {
		return {}, problemf(token.span, "expected %v, but got a %v", KEYWORD_NAMES[keyword], token_name(token))
	}
	if token.keyword == keyword {
		return token, nil
	} else {
		return {}, problemf(token.span, "expected %v, but got a %v", KEYWORD_NAMES[keyword], token_name(token))
	}
}

// Consumes and returns the next token if it is `kind`, otherwise does nothing.
@(require_results)
parser_optional :: proc(p: ^Parser, kind: Token_Kind) -> (token: Token, found: bool) {
	token = parser_peek_token(p)
	if token.kind == kind {
		parser_advance(p)
		return token, true
	}
	return token, false
}

// Returns the span of the current token.
parser_cur_span :: proc(p: ^Parser) -> Span {
	return parser_peek_token(p).span
}
// Returns the current token.
@(require_results)
parser_peek_token :: proc(p: ^Parser) -> Token {
	if p.cursor >= len(p.tokens) {
		// Return the EOF token.
		return slice.last(p.tokens[:])
	}

	return p.tokens[p.cursor]
}
// Consumes and returns the current token advancing the cursor, while skipping all comments.
parser_next_token :: proc(p: ^Parser) -> Token {
	for {
		if p.cursor >= len(p.tokens) {
			// Return the EOF token.
			return slice.last(p.tokens[:])
		}

		token := p.tokens[p.cursor]
		parser_advance(p)

		// Skip comments.
		if token.kind == .Comment do continue

		return token
	}
}
// Increments the token cursor by 1.
parser_advance :: proc(p: ^Parser) {
	p.cursor += 1
}
