package uxnsmal

import "core:unicode"

Token :: struct {
	kind:    Token_Kind,
	// Kind of keyword tokens (`Token_Kind.Keyword`).
	keyword: Keyword_Kind,
	// Actual number of number tokens (`Token_Kind.Number`).
	number:  int,
	span:    Span,
}

// TODO: probably these is also should be space and new line tokens.
// This may be useful for formatting or lint tools.

Token_Kind :: enum {
	// An unknown token. Should never be presented to the user, otherwise it is a bug.
	Unknown = 0,

	// Identifier.
	// `hello`, `bye_12`, `hi-AGAIN`
	Ident,
	// Reserved word, like `fun`, `var`, `const`, etc.
	Keyword,
	// Label. Basically an identifier with `@` at the beginning.
	// `@hello`, `@bye_12`, `@hi-AGAIN`
	Label,
	// Number literal.
	// `123`, `0xff`, `0b101`, `0o777`
	Number,
	// String literal inside double quotes.
	// `"Hello guys!!\n\0"`
	String,
	// ASCII character literal inside single quotes.
	// `'a'`, `' '`, `'\n'`
	Char,
	// Single-line or multi-line (block) comment, including `//` and `/* ... */`.
	// `// Comment...`
	// `/* block comment! */`
	Comment,

	//
	Skinny_Arrow, // `->`
	Stick, // `--`
	Dot, // `.`
	Colon, // `:`
	Ampersand, // `&`
	Asterisk, // `*`
	Hat, // `^`
	Money, // `$`
	Open_Paren, // `(`
	Close_Paren, // `)`
	Open_Brace, // `{`
	Close_Brace, // `}`
	Open_Bracket, // `[`
	Close_Bracket, // `]`

	//
	EOF, // End of file.
}

Keyword_Kind :: enum {
	// Should never be presented to the user, otherwise it is a bug.
	None = 0,
	// `fun`
	Fun,
	// `var`
	Var,
	// `const`
	Const,
	// `data`
	Data,
	// `alias`
	Alias,
}

TOKEN_NAMES: [Token_Kind]string = {
	.Unknown       = `unknown`, // user should never see it, but it is here anyway
	.Ident         = `identifier`,
	.Keyword       = `keyword`,
	.Label         = `label`,
	.Number        = `number`,
	.String        = `string`,
	.Char          = `character`,
	.Comment       = `comment`,
	.Skinny_Arrow  = `"->"`,
	.Stick         = `"--"`,
	.Dot           = `"."`,
	.Colon         = `":"`,
	.Ampersand     = `"&"`,
	.Asterisk      = `"*"`,
	.Hat           = `"^"`,
	.Money         = `"$"`,
	.Open_Paren    = `"("`,
	.Close_Paren   = `")"`,
	.Open_Brace    = `"{"`,
	.Close_Brace   = `"}"`,
	.Open_Bracket  = `"["`,
	.Close_Bracket = `"]"`,
	.EOF           = "end of file",
}

KEYWORD_NAMES: [Keyword_Kind]string = {
	.None  = `none`,
	.Fun   = "`fun` keyword",
	.Var   = "`var` keyword",
	.Const = "`const` keyword",
	.Data  = "`data` keyword",
	.Alias = "`alias` keyword",
}

// Returns the string name of a token. If token is a keyword, returns the
// string name of this keyword.
// Used for human-readable output.
token_name :: proc(token: Token) -> string {
	if token.kind == .Keyword {
		return KEYWORD_NAMES[token.keyword]
	} else {
		return TOKEN_NAMES[token.kind]
	}
}

// Returns whether a rune is allowed to be at an identifier beginning.
rune_is_ident_start :: #force_inline proc(rune: rune) -> bool {
	return unicode.is_alpha(rune) || rune == '_' || rune == '-'
}
// Returns whether a rune is an allowed identifier char.
rune_is_ident :: #force_inline proc(rune: rune) -> bool {
	return rune_is_ident_start(rune) || unicode.is_digit(rune)
}

// Byte range in a source code.
Span :: struct {
	start: int,
	end:   int,
}

span :: proc(start: int, end: int) -> Span {
	return Span{start, end}
}
eof_span :: proc(s: string) -> Span {
	return span(len(s), len(s))
}

// Returns a span slice from a string.
span_slice :: proc(s: string, span: Span) -> string {
	return s[span.start:span.end]
}
