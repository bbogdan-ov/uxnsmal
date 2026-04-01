package uxnsmal

import "core:strconv"
import "core:strings"
import "core:unicode"
import "core:unicode/utf8"

// All functions in this file don't do any allocations.

Lexer :: struct {
	// Immutable reference to a UXNSMAL source code string.
	source:     string,

	// Byte index of the current rune within the source code string.
	offset:     int,
	// Number of the current line, starting from 0.
	line_num:   int,
	// Number of the current column/character, starting from 0.
	column_num: int,
}

lexer_init :: proc(lexer: ^Lexer, source: string) {
	lexer.source = source
	lexer.offset = 0
	lexer.line_num = 0
	lexer.column_num = 0
}

// Parses a next token from the source code. You may want to call this function
// in a loop untill token is `Token_Kind.EOF` to iterate over all tokens.
@(require_results)
lexer_next :: proc(lexer: ^Lexer) -> (token: Token, err: Error) {
	lexer_skip_whitespaces(lexer)

	found := true

	token.span = lexer_span(lexer, lexer.offset, lexer.offset)
	
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
		found = false
	}
	// odinfmt: enable

	token.span.end = lexer.offset

	if !found {
		if lexer_finished(lexer) {
			// End of file.
			idx := len(lexer.source)
			token = Token {
				kind = .EOF,
				span = lexer_span(lexer, idx, idx),
			}
			return token, nil
		} else {
			// Unknown token.
			return {}, problemf(token.span, "unknown token")
		}
	}

	if token.kind == .Ident {
		// May be the identifier is a keyword?
		sliced := span_slice(lexer.source, token.span)
		kind, ok := keyword_from_str(sliced)
		if ok {
			token.kind = kind
		}
	}

	if token.kind == .Ident {
		// May be the identifier is an intrinsic?
		sliced := span_slice(lexer.source, token.span)

		name := sliced
		modes := ""
		split_idx := strings.index_byte(sliced, '-')
		if split_idx >= 0 {
			name = sliced[:split_idx]
			modes = sliced[split_idx + 1:] // +1 to exclude the "-"
		}

		intr, ok := intr_from_str(name)
		if ok {
			token.kind = .Intr
			token.value = intr

			switch modes {
			case "": // nothing
			case "k":
				token.modes += {.Keep}
			case "r":
				token.modes += {.Return}
			case "kr", "rk":
				token.modes += {.Keep, .Return}
			case:
				// TODO: show valid combinations of intrinsic modes.
				err = problemf(token.span, `invalid intrinsic mode "%s"`, modes)
				return {}, err
			}
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
	start := lexer_span(lexer, lexer.offset, lexer.offset + 2)

	if strings.has_prefix(remain, "//") {
		// Single-line comment.
		lexer_skip_until_newline(lexer)
		return true, nil
	} else if strings.has_prefix(remain, "/*") {
		// Block comment.
		for rune in lexer_remain(lexer) {
			if lexer_consume_str(lexer, "*/") {
				return true, nil
			}

			lexer_advance_rune(lexer, rune)
		}

		return false, problemf(start, "unclosed block comment")
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

	span := lexer_span(lexer, lexer.offset, lexer.offset)
	for rune in lexer_remain(lexer) {
		if !(unicode.is_alpha(rune) || unicode.is_digit(rune)) {
			break
		}
		lexer_advance_rune(lexer, rune)
	}
	span.end = lexer.offset

	word := span_slice(lexer.source, span)
	n, ok := strconv.parse_uint(word, base)
	if !ok || n > uint(max(i32)) {
		return false, problemf(span, "invalid number literal")
	}

	token.kind = .Number
	token.value = u32(n)

	return true, nil
}

lexer_next_ident :: proc(lexer: ^Lexer, token: ^Token) -> (found: bool, err: Error) {
	if lexer_finished(lexer) {
		return false, nil
	}

	atsign_span := lexer_span(lexer, lexer.offset, lexer.offset)
	if lexer_consume_str(lexer, "@") {
		token.kind = .Label
		atsign_span.end = lexer.offset
	} else {
		token.kind = .Ident
	}

	if !rune_is_ident_start(lexer_cur_rune(lexer)) {
		if token.kind == .Label {
			return false, problemf(atsign_span, "expected a label name after the `@`")
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

	start := lexer_span(lexer, lexer.offset, lexer.offset + 1)
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
		err = problemf(start, "unclosed string literal")
	} else {
		err = problemf(start, "unclosed character literal")
	}
	return false, err
}

// Skip all whitespaces untill a non-whitespace char.
lexer_skip_whitespaces :: proc(lexer: ^Lexer) {
	for rune in lexer_remain(lexer) {
		if !unicode.is_space(rune) do break
		lexer_advance_rune(lexer, rune)
	}
}
// Skip all untill a whitespace char.
lexer_skip_non_whitespace :: proc(lexer: ^Lexer) {
	for rune in lexer_remain(lexer) {
		if unicode.is_space(rune) do break
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
	if lexer.offset + n < len(lexer.source) {
		rune := utf8.rune_at(lexer.source, lexer.offset)
		if rune == '\n' {
			lexer.line_num += 1
			lexer.column_num = 0
		} else {
			lexer.column_num += 1
		}
	}

	lexer.offset += n
}
// Increment `offset` by rune size in bytes.
lexer_advance_rune :: proc(lexer: ^Lexer, rune: rune) {
	lexer_advance(lexer, utf8.rune_size(rune))
}

lexer_span :: proc(lexer: ^Lexer, start, end: int) -> Span {
	return Span{start, end, lexer.line_num, lexer.column_num}
}
lexer_cur_rune :: proc(lexer: ^Lexer) -> rune {
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
