package lexer

import "core:fmt"
import "core:strconv"
import "core:strings"
import "core:unicode"
import "core:unicode/utf8"

// TODO!!: count current line and column number.
Lexer :: struct {
	// Immutable reference to a UXNSMAL source code string.
	source: string,

	// Index of the current rune within the source code string.
	offset: int,
}

make :: proc(source: string) -> Lexer {
	return Lexer{source = source}
}

// Parse a next token from the source code. You should call this function in a
// loop untill token kind is `Token_Kind.EOF`.
next_token :: proc(lexer: ^Lexer) -> Token {
	skip_whitespaces(lexer)

	token: Token
	found := true

	token.span.start = lexer.offset
	
	// odinfmt: disable
	over: if consume_str(lexer, "->") do token.kind = .Skinny_Arrow
	else if consume_str(lexer, "--")  do token.kind = .Stick
	else if consume_str(lexer, ".")   do token.kind = .Dot
	else if consume_str(lexer, ":")   do token.kind = .Colon
	else if consume_str(lexer, "&")   do token.kind = .Ampersand
	else if consume_str(lexer, "*")   do token.kind = .Asterisk
	else if consume_str(lexer, "^")   do token.kind = .Hat
	else if consume_str(lexer, "$")   do token.kind = .Money
	else if consume_str(lexer, "(")   do token.kind = .Open_Paren
	else if consume_str(lexer, ")")   do token.kind = .Close_Paren
	else if consume_str(lexer, "{")   do token.kind = .Open_Brace
	else if consume_str(lexer, "}")   do token.kind = .Close_Brace
	else if consume_str(lexer, "[")   do token.kind = .Open_Bracket
	else if consume_str(lexer, "]")   do token.kind = .Close_Bracket
	else if consume_comment(lexer)      do token.kind = .Comment
	else {
		found = next_string_or_char(lexer, &token)
		if found do break over

		found = next_number(lexer, &token)
		if found do break over

		found = next_ident_or_label(lexer, &token)
		if found do break over

		// Consume unknown tokens to correctly update its span.
		skip_non_whitespace(lexer)
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
		if finished(lexer) {
			// End of file.
			token = Token {
				kind = .EOF,
				span = eof_span(lexer.source),
			}
		} else {
			// Unknown token.
			panic(fmt.tprintf("TODO: unknown token '%v'", span_slice(lexer.source, token.span)))
		}
	}

	return token
}

// Skip the next occurrence of `s` if any, otherwise returns false.
consume_str :: proc(lexer: ^Lexer, s: string) -> bool {
	remain := remain_source(lexer)

	if strings.has_prefix(remain, s) {
		advance(lexer, len(s))
		return true
	}
	return false
}

consume_comment :: proc(lexer: ^Lexer) -> bool {
	remain := remain_source(lexer)

	if strings.has_prefix(remain, "//") {
		// Single-line comment.
		skip_until_newline(lexer)
		return true
	} else if strings.has_prefix(remain, "/*") {
		// Block comment.

		// TODO!!: report unclosed block-comments.

		for lexer.offset < len(lexer.source) {
			if strings.starts_with(lexer.source[lexer.offset:], "*/") {
				advance(lexer, 2) // consume `*/`
				return true
			}

			// NOTE: we can safely interate byte-by-byte because we'll
			// eventually hit an EOF or `*/` and `offset` won't point at the
			// middle of a Unicode char.
			advance(lexer, 1)
		}
		return true
	}

	return false
}

next_number :: proc(lexer: ^Lexer, token: ^Token) -> bool {
	if finished(lexer) {
		return false
	}

	cur := cur_rune(lexer)
	if !unicode.is_digit(cur) {
		return false
	}

	base: int
	if consume_str(lexer, "0x") {
		base = 16
	} else if consume_str(lexer, "0b") {
		base = 2
	} else if consume_str(lexer, "0o") {
		base = 8
	} else {
		base = 10
	}

	span: Span
	span.start = lexer.offset
	for rune in remain_source(lexer) {
		if !(unicode.is_alpha(rune) || unicode.is_digit(rune)) {
			break
		}
		advance_rune(lexer, rune)
	}
	span.end = lexer.offset

	word := span_slice(lexer.source, span)
	n, ok := strconv.parse_int(word, base)
	assert(ok) // TODO!!: report invalid number literals.

	token.kind = .Number
	token.number = n

	return true
}

next_ident_or_label :: proc(lexer: ^Lexer, token: ^Token) -> (ok: bool) {
	if finished(lexer) {
		return false
	}

	if consume_str(lexer, "@") {
		token.kind = .Label
	} else {
		token.kind = .Ident
	}

	if !rune_is_ident_start(cur_rune(lexer)) {
		return false
	}

	for rune in remain_source(lexer) {
		if !rune_is_ident(rune) do break

		ok = true
		advance_rune(lexer, rune)
	}

	return ok
}

next_string_or_char :: proc(lexer: ^Lexer, token: ^Token) -> bool {
	if finished(lexer) {
		return false
	}

	// TODO!!: report unclosed string literals.

	quote := cur_rune(lexer)
	if quote == '"' {
		token.kind = .String
	} else if quote == '\'' {
		token.kind = .Char
	} else {
		return false
	}

	advance(lexer, 1) // consume opening quote

	escaped := false

	for rune in remain_source(lexer) {
		if escaped {
			escaped = false
		} else if rune == '\\' {
			escaped = true
		} else if rune == quote {
			advance(lexer, 1) // consume closing quote
			break
		}

		advance_rune(lexer, rune)
	}

	return true
}

// Skip all whitespaces untill a non-whitespace char.
skip_whitespaces :: proc(lexer: ^Lexer) {
	for rune in remain_source(lexer) {
		if !unicode.is_white_space(rune) do break
		advance_rune(lexer, rune)
	}
}
// Skip all untill a whitespace char.
skip_non_whitespace :: proc(lexer: ^Lexer) {
	for rune in remain_source(lexer) {
		if unicode.is_white_space(rune) do break
		advance_rune(lexer, rune)
	}
}
// Skip all untill a new line char.
skip_until_newline :: proc(lexer: ^Lexer) {
	for rune in remain_source(lexer) {
		// TODO: not sure how it will act with Windows' stupid new line
		// sequence '\n\r' or whatever.
		if rune == '\n' do break
		advance_rune(lexer, rune)
	}
}

// Increment `offset` by N
advance :: proc(lexer: ^Lexer, #any_int n: int) {
	lexer.offset += n
}
// Increment `offset` by rune size in bytes.
advance_rune :: proc(lexer: ^Lexer, rune: rune) {
	advance(lexer, utf8.rune_size(rune))
}

cur_rune :: proc(lexer: ^Lexer) -> rune #no_bounds_check {
	when ODIN_NO_BOUNDS_CHECK {
		return utf8.rune_at(lexer.source, lexer.offset)
	} else {
		if finished(lexer) {
			return 0
		} else {
			return utf8.rune_at(lexer.source, lexer.offset)
		}
	}
}
// Returns the part of the source code that is can't wait to be parsed!! Returns
// an empty string if there is nothing left to parse.
remain_source :: proc(lexer: ^Lexer) -> string {
	when ODIN_NO_BOUNDS_CHECK {
		return lexer.source[lexer.offset:]
	} else {
		#no_bounds_check if finished(lexer) {
			return ""
		} else {
			return lexer.source[lexer.offset:]
		}
	}
}
finished :: proc(lexer: ^Lexer) -> bool {
	return lexer.offset >= len(lexer.source)
}
