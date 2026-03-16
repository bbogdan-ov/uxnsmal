package uxnsmal

import "core:strconv"
import "core:strings"
import "core:unicode"
import "core:unicode/utf8"

// TODO!!: count current line and column number.
Lexer :: struct {
	// Immutable reference to a UXNSMAL source code string.
	source: string,

	// Byte index of the current rune within the source code string.
	offset: int,
}

lexer_init :: proc(lexer: ^Lexer, source: string) {
	lexer.source = source
}

// Parses a next token from the source code. You may want to call this function
// in a loop untill token is `Token_Kind.EOF` to iterate over all tokens.
lexer_next :: proc(lexer: ^Lexer) -> (token: Token, err: Error) {
	lexer_skip_whitespaces(lexer)

	found := true

	token.span.start = lexer.offset
	
	// odinfmt: disable
	over: if lexer_consume_str(lexer, "->")        do token.kind = .Skinny_Arrow
	else if lexer_consume_str(lexer, "--")         do token.kind = .Stick
	else if lexer_consume_str(lexer, ".")          do token.kind = .Dot
	else if lexer_consume_str(lexer, ":")          do token.kind = .Colon
	else if lexer_consume_str(lexer, "&")          do token.kind = .Ampersand
	else if lexer_consume_str(lexer, "*")          do token.kind = .Asterisk
	else if lexer_consume_str(lexer, "^")          do token.kind = .Hat
	else if lexer_consume_str(lexer, "$")          do token.kind = .Money
	else if lexer_consume_str(lexer, "(")          do token.kind = .Open_Paren
	else if lexer_consume_str(lexer, ")")          do token.kind = .Close_Paren
	else if lexer_consume_str(lexer, "{")          do token.kind = .Open_Brace
	else if lexer_consume_str(lexer, "}")          do token.kind = .Close_Brace
	else if lexer_consume_str(lexer, "[")          do token.kind = .Open_Bracket
	else if lexer_consume_str(lexer, "]")          do token.kind = .Close_Bracket
	else if lexer_consume_comment(lexer) or_return do token.kind = .Comment
	else {
		found = lexer_next_string(lexer, &token) or_return
		if found do break over

		found = lexer_next_number(lexer, &token) or_return
		if found do break over

		found = lexer_next_ident(lexer, &token) or_return
		if found do break over

		// Consume unknown tokens to correctly update its span.
		lexer_skip_non_whitespace(lexer)
	}
	// odinfmt: enable

	token.span.end = lexer.offset

	if token.kind == .Ident {
		// May be the identifier is a keyword?
		word := span_slice(lexer.source, token.span)

		for name, variant in KEYWORD_NAMES {
			if word == name {
				token.kind = .Keyword
				token.keyword = variant
				break
			}
		}
	} else if !found {
		if lexer_finished(lexer) {
			// End of file.
			token = Token {
				kind = .EOF,
				span = eof_span(lexer.source),
			}
		} else {
			// Unknown token.
			return {}, problem(token.span, "unknown token")
		}
	}

	return token, nil
}

// Skip the next occurrence of `s` if any, otherwise returns false.
lexer_consume_str :: proc(lexer: ^Lexer, s: string) -> bool {
	remain := lexer_remain(lexer)

	if strings.has_prefix(remain, s) {
		lexer_advance(lexer, len(s))
		return true
	}
	return false
}

lexer_consume_comment :: proc(lexer: ^Lexer) -> (found: bool, err: Error) {
	remain := lexer_remain(lexer)
	start := span(lexer.offset, lexer.offset + 2)

	if strings.has_prefix(remain, "//") {
		// Single-line comment.
		lexer_skip_until_newline(lexer)
		return true, nil
	} else if strings.has_prefix(remain, "/*") {
		// Block comment.
		for lexer.offset < len(lexer.source) {
			if strings.starts_with(lexer.source[lexer.offset:], "*/") {
				lexer_advance(lexer, 2) // consume `*/`
				return true, nil
			}

			// NOTE: we can safely interate byte-by-byte because we'll
			// eventually hit an EOF or `*/` and `offset` won't point at the
			// middle of a Unicode char.
			lexer_advance(lexer, 1)
		}

		return false, problem(start, "unclosed block comment")
	}

	return false, nil
}

lexer_next_number :: proc(lexer: ^Lexer, token: ^Token) -> (found: bool, err: Error) {
	if lexer_finished(lexer) {
		return false, nil
	}

	cur := lexer_cur_rune(lexer)
	if !unicode.is_digit(cur) {
		return false, nil
	}

	base: int
	if lexer_consume_str(lexer, "0x") {
		base = 16
	} else if lexer_consume_str(lexer, "0b") {
		base = 2
	} else if lexer_consume_str(lexer, "0o") {
		base = 8
	} else {
		base = 10
	}

	span: Span
	span.start = lexer.offset
	for rune in lexer_remain(lexer) {
		if !(unicode.is_alpha(rune) || unicode.is_digit(rune)) {
			break
		}
		lexer_advance_rune(lexer, rune)
	}
	span.end = lexer.offset

	word := span_slice(lexer.source, span)
	n, ok := strconv.parse_int(word, base)
	if !ok {
		return false, problem(span, "invalid number literal")
	}

	token.kind = .Number
	token.number = n

	return true, nil
}

lexer_next_ident :: proc(lexer: ^Lexer, token: ^Token) -> (found: bool, err: Error) {
	if lexer_finished(lexer) {
		return false, nil
	}

	label_span := span(lexer.offset, lexer.offset)
	if lexer_consume_str(lexer, "@") {
		token.kind = .Label
		label_span.end = lexer.offset
	} else {
		token.kind = .Ident
	}

	if !rune_is_ident_start(lexer_cur_rune(lexer)) {
		if token.kind == .Label {
			return false, problem(label_span, "expected a label name after `@`")
		}

		return false, nil
	}

	for rune in lexer_remain(lexer) {
		if !rune_is_ident(rune) do break

		found = true
		lexer_advance_rune(lexer, rune)
	}

	return found, nil
}

lexer_next_string :: proc(lexer: ^Lexer, token: ^Token) -> (found: bool, err: Error) {
	if lexer_finished(lexer) {
		return false, nil
	}

	start := span(lexer.offset, lexer.offset + 1)
	quote := lexer_cur_rune(lexer)
	if quote == '"' {
		token.kind = .String
	} else if quote == '\'' {
		token.kind = .Char
	} else {
		return false, nil
	}

	lexer_advance(lexer, 1) // consume opening quote

	escaped := false

	for rune in lexer_remain(lexer) {
		if escaped {
			escaped = false
		} else if rune == '\\' {
			escaped = true
		} else if rune == quote {
			lexer_advance(lexer, 1) // consume closing quote
			return true, nil
		}

		lexer_advance_rune(lexer, rune)
	}

	if token.kind == .String {
		err = problem(start, "unclosed string literal")
	} else {
		err = problem(start, "unclosed character literal")
	}
	return false, err
}

// Skip all whitespaces untill a non-whitespace char.
lexer_skip_whitespaces :: proc(lexer: ^Lexer) {
	for rune in lexer_remain(lexer) {
		if !unicode.is_white_space(rune) do break
		lexer_advance_rune(lexer, rune)
	}
}
// Skip all untill a whitespace char.
lexer_skip_non_whitespace :: proc(lexer: ^Lexer) {
	for rune in lexer_remain(lexer) {
		if unicode.is_white_space(rune) do break
		lexer_advance_rune(lexer, rune)
	}
}
// Skip all untill a new line char.
lexer_skip_until_newline :: proc(lexer: ^Lexer) {
	for rune in lexer_remain(lexer) {
		// TODO: not sure how it will act with Windows' stupid new line
		// sequence '\n\r' or whatever.
		if rune == '\n' do break
		lexer_advance_rune(lexer, rune)
	}
}

// Increment `offset` by N
lexer_advance :: proc(lexer: ^Lexer, #any_int n: int) {
	lexer.offset += n
}
// Increment `offset` by rune size in bytes.
lexer_advance_rune :: proc(lexer: ^Lexer, rune: rune) {
	lexer_advance(lexer, utf8.rune_size(rune))
}

lexer_cur_rune :: proc(lexer: ^Lexer) -> rune #no_bounds_check {
	when ODIN_NO_BOUNDS_CHECK {
		return utf8.rune_at(lexer.source, lexer.offset)
	} else {
		if lexer_finished(lexer) {
			return 0
		} else {
			return utf8.rune_at(lexer.source, lexer.offset)
		}
	}
}
// Returns the part of the source code that is can't wait to be parsed!! Returns
// an empty string if there is nothing left to parse.
lexer_remain :: proc(lexer: ^Lexer) -> string {
	when ODIN_NO_BOUNDS_CHECK {
		return lexer.source[lexer.offset:]
	} else {
		#no_bounds_check if lexer_finished(lexer) {
			return ""
		} else {
			return lexer.source[lexer.offset:]
		}
	}
}
lexer_finished :: proc(lexer: ^Lexer) -> bool {
	return lexer.offset >= len(lexer.source)
}
