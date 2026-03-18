package uxnsmal

import "core:unicode"

Token :: struct {
	kind:  Token_Kind,
	value: union {
		int, // `.Number` token value.
		Intr, // `.Intr` token intrinsic kind.
	},
	// Modes of an intrinsic token.
	modes: Intr_Mode,
	span:  Span,
}

// TODO: probably these is also should be space and new line tokens.
// This may be useful for formatting or lint tools.

Token_Kind :: enum {
	// An unknown token. Should never be presented to the user, otherwise it is a bug.
	Unknown = 0,

	// Identifier.
	// `hello`, `bye_12`, `hi-AGAIN`
	Ident,
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
	// Intrinsic.
	// `add`, `pop-r`, `swap-rk` etc
	Intr,

	//
	Keyword_Fun, // `fun`
	Keyword_Var, // `var`
	Keyword_Const, // `const`
	Keyword_Data, // `data`
	Keyword_Type, // `type`
	Keyword_Enum, // `enum`
	Keyword_Struct, // `struct`
	Keyword_Rom, // `rom`
	Keyword_If, // `if`
	Keyword_Elif, // `elif`
	Keyword_Else, // `else`
	Keyword_While, // `while`
	Keyword_Loop, // `loop`
	Keyword_As, // `as`

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

// Intrinsic kind.
Intr :: enum {
	Add,
	Sub,
	Mul,
	Div,
	Inc,
	Shift,
	And,
	Or,
	Xor,
	Eq,
	Neq,
	Gth,
	Lth,
	Pop,
	Swap,
	Nip,
	Rot,
	Dup,
	Over,
	Sth,
	Load,
	Store,
	Call,
	Input,
	Input2,
	Output,
}
@(private)
_Intr_Mode :: enum {
	Short,
	Keep,
	Return,
}
// Intrinsic modes.
Intr_Mode :: bit_set[_Intr_Mode]

@(rodata)
TOKEN_NAMES: [Token_Kind]string = {
	.Unknown        = `unknown`, // user should never see it, but it is here anyway
	.Ident          = `identifier`,
	.Label          = `label`,
	.Number         = `number`,
	.String         = `string`,
	.Char           = `character`,
	.Comment        = `comment`,
	.Intr           = `intrinsic`,
	.Keyword_Fun    = "`fun` keyword",
	.Keyword_Var    = "`var` kyword",
	.Keyword_Const  = "`const` kyword",
	.Keyword_Data   = "`data` kyword",
	.Keyword_Type   = "`type` kyword",
	.Keyword_Enum   = "`enum` kyword",
	.Keyword_Struct = "`struct` kyword",
	.Keyword_Rom    = "`rom` kyword",
	.Keyword_If     = "`if` keyword",
	.Keyword_Elif   = "`elif` keyword",
	.Keyword_Else   = "`else` keyword",
	.Keyword_While  = "`while` keyword",
	.Keyword_Loop   = "`loop` keyword",
	.Keyword_As     = "`as` keyword",
	.Skinny_Arrow   = `"->"`,
	.Stick          = `"--"`,
	.Dot            = `"."`,
	.Colon          = `":"`,
	.Ampersand      = `"&"`,
	.Asterisk       = `"*"`,
	.Hat            = `"^"`,
	.Money          = `"$"`,
	.Open_Paren     = `"("`,
	.Close_Paren    = `")"`,
	.Open_Brace     = `"{"`,
	.Close_Brace    = `"}"`,
	.Open_Bracket   = `"["`,
	.Close_Bracket  = `"]"`,
	.EOF            = "end of file",
}

@(rodata)
INTR_NAMES: [Intr]string = {
	.Add    = "`add`",
	.Sub    = "`sub`",
	.Mul    = "`mul`",
	.Div    = "`div`",
	.Inc    = "`inc`",
	.Shift  = "`shift`",
	.And    = "`and`",
	.Or     = "`or`",
	.Xor    = "`xor`",
	.Eq     = "`eq`",
	.Neq    = "`neq`",
	.Gth    = "`gth`",
	.Lth    = "`lth`",
	.Pop    = "`pop`",
	.Swap   = "`swap`",
	.Nip    = "`nip`",
	.Rot    = "`rot`",
	.Dup    = "`dup`",
	.Over   = "`over`",
	.Sth    = "`sth`",
	.Load   = "`load`",
	.Store  = "`store`",
	.Call   = "`call`",
	.Input  = "`input`",
	.Input2 = "`input2`",
	.Output = "`output`",
}

// Returns the string name of a token.
// Used for human-readable output.
token_name :: proc(token: Token) -> string {
	if token.kind == .Intr {
		return INTR_NAMES[token.value.(Intr)]
	} else {
		return TOKEN_NAMES[token.kind]
	}
}

// NOTE: `keyword_from_str` and `intr_from_str` are linear-search functions
// which is fine for now, we don't have too many keywords and intrinsics yet.

keyword_from_str :: proc(s: string) -> (kind: Token_Kind, ok: bool) {
	// odinfmt: disable
	switch s {
	case "fun":    kind = .Keyword_Fun
	case "var":    kind = .Keyword_Var
	case "const":  kind = .Keyword_Const
	case "data":   kind = .Keyword_Data
	case "type":   kind = .Keyword_Type
	case "enum":   kind = .Keyword_Enum
	case "struct": kind = .Keyword_Struct
	case "rom":    kind = .Keyword_Rom
	case "if":     kind = .Keyword_If
	case "elif":   kind = .Keyword_Elif
	case "else":   kind = .Keyword_Else
	case "while":  kind = .Keyword_While
	case "loop":   kind = .Keyword_Loop
	case "as":     kind = .Keyword_As
	case:
		return .Unknown, false
	}
	// odinfmt: enable
	return kind, true
}

intr_from_str :: proc(s: string) -> (intr: Intr, ok: bool) {
	// odinfmt: disable
	switch s {
	case "add":    intr = .Add
	case "sub":    intr = .Sub
	case "mul":    intr = .Mul
	case "div":    intr = .Div
	case "inc":    intr = .Inc
	case "shift":  intr = .Shift
	case "and":    intr = .And
	case "or":     intr = .Or
	case "xor":    intr = .Xor
	case "eq":     intr = .Eq
	case "neq":    intr = .Neq
	case "gth":    intr = .Gth
	case "lth":    intr = .Lth
	case "pop":    intr = .Pop
	case "swap":   intr = .Swap
	case "nip":    intr = .Nip
	case "rot":    intr = .Rot
	case "dup":    intr = .Dup
	case "over":   intr = .Over
	case "sth":    intr = .Sth
	case "load":   intr = .Load
	case "store":  intr = .Store
	case "call":   intr = .Call
	case "input":  intr = .Input
	case "input2": intr = .Input2
	case "output": intr = .Output
	case:
		return nil, false
	}
	// odinfmt: enable
	return intr, true
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
Span :: struct #all_or_none {
	start:  int,
	end:    int,
	// Line number of the span beginning, starting from 0.
	line:   int,
	// Column/character number of the span beginning, starting from 0.
	column: int,
}

// Returns a span slice from a string.
span_slice :: proc(s: string, span: Span) -> string {
	return s[span.start:span.end]
}
