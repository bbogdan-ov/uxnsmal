package uxnsmal

// AST node.
Node :: union #no_nil {
	// Definitions.
	Def_Func,
	Def_Var,
	Def_Const,
	Def_Data,
	Def_Alias,
	Def_Enum,
	Def_Struct,

	// Expressions.
	Expr_Symbol,
	Expr_Intr,
	Expr_Byte,
	Expr_Short,
	Expr_String,
	Expr_Store,
	Expr_Bind,
	Expr_Expect,
	Expr_Cast,
	Expr_If,
	Expr_While,
	Expr_Break,
}

node_span :: proc(node: Node) -> Span {
	// odinfmt: disable
	switch n in node {
	case Def_Func:    return n.name.span
	case Def_Var:     return n.names_span
	case Def_Const:   return n.symbol.defined_at
	case Def_Data:    return n.name.span
	case Def_Alias:   return n.name.span
	case Def_Enum:    return n.symbol.defined_at
	case Def_Struct:  return n.symbol.defined_at
	case Expr_Symbol: return n.span
	case Expr_Intr:   return n.span
	case Expr_Byte:   return n.span
	case Expr_Short:  return n.span
	case Expr_String: return n.span
	case Expr_Store:  return n.span
	case Expr_Bind:   return n.span
	case Expr_Expect: return n.span
	case Expr_Cast:   return n.span
	case Expr_If:     return n.if_block.keyword_span
	case Expr_While:  return n.keyword_span
	case Expr_Break:  return n.span
	}
	// odinfmt: enable
	unreachable()
}

Spanned :: struct($T: typeid) {
	x:    T,
	span: Span,
}

// ------------------------------
// Expressions.
// ------------------------------

// Symbol member access.
Member :: struct #all_or_none {
	name:           Name,
	// Depth of array access. 0 - no array access
	// Example: `my_var.field[]`, `my_2d_array[][]`
	// It is not allowed to load variables with more than 1 array access, but
	// this is used for better error messages.
	as_array_count: int,
	// Span of name and "[]" if present.
	span:           Span,
	// Span of "[]" if present.
	brackets_span:  Span,
}
// Symbol use.
Expr_Symbol :: struct #all_or_none {
	// Members access of a symbol, e.g. a struct field or an enum variant.
	// There is always at least one element and the first one is always the
	// name of the symbol itself.
	// For example if there is only one element, it may be a variable load,
	// function call, etc; if 2, a struct variable field access or a enum
	// variant use.
	members: [dynamic]Member,
	// Whether is taking a pointer to this symbol.
	as_ptr:  bool,
	span:    Span,
}
// Intrinsic call.
Expr_Intr :: struct #all_or_none {
	kind:  Intr,
	modes: Intr_Mode,
	span:  Span,
}
// Byte number literal, pushes a byte onto the working stack.
Expr_Byte :: struct #all_or_none {
	value: u8,
	span:  Span,
}
// Short short literal, pushes a short onto the working stack.
Expr_Short :: struct #all_or_none {
	value: u16,
	span:  Span,
}
// String literal, pushes a string address (`*[]byte`) onto the working stack.
Expr_String :: struct #all_or_none {
	bytes: [dynamic]byte,
	span:  Span,
}

// Stor expression.
Expr_Store :: struct #all_or_none {
	symbol: Expr_Symbol,
	span:   Span,
}
// Name binding expression.
Expr_Bind :: struct #all_or_none {
	// List of names, may be empty.
	names: [dynamic]Name,
	span:  Span,
}
// Binded names expectation expression.
Expr_Expect :: struct #all_or_none {
	// List of names, may be empty.
	names: [dynamic]Name,
	span:  Span,
}
Expr_Cast :: struct #all_or_none {
	// List of types, may be empty.
	types: [dynamic]Spanned(Complex_Type),
	span:  Span,
}

// If or else block.
If_Block :: struct #all_or_none {
	body:         Body,
	keyword_span: Span,
}
// Elif block.
Elif_Block :: struct #all_or_none {
	condition:      [dynamic]Node,
	body:           Body,
	condition_span: Span,
	keyword_span:   Span,
}
// If, elif and else block.
Expr_If :: struct #all_or_none {
	if_block:     If_Block,
	elifs_blocks: [dynamic]Elif_Block,
	else_block:   Maybe(If_Block),
}

// While block.
Expr_While :: struct #all_or_none {
	condition:      [dynamic]Node,
	label:          Maybe(Name),
	body:           Body,
	keyword_span:   Span,
	condition_span: Span,
}

// Break, breaks from a block or loop.
Expr_Break :: struct #all_or_none {
	label: Name,
	span:  Span,
}

// ------------------------------
// Definitions.
// ------------------------------

// Function definition.
Def_Func :: struct #all_or_none {
	name:      Name,
	signature: Signature,
	body:      Body,
}

// Variable definition.
Def_Var :: struct #all_or_none {
	pairs:      [dynamic]Pair,
	// Whether this variable should be allocated in the ROM address space.
	in_rom:     bool,
	names_span: Span,
}

// Constant definition.
Def_Const :: struct #all_or_none {
	symbol: ^Symbol_Const,
	body:   Body,
}

// Data definition.
Def_Data :: struct #all_or_none {
	name: Name,
	// Should only contain number, string and character literals.
	body: Body,
}

// Type alias definition to different a type.
Def_Alias :: struct {
	name: Name,
}

// Enum definition.
Def_Enum :: struct #all_or_none {
	symbol: ^Symbol_Enum,
}

// Struct definition.
Def_Struct :: struct #all_or_none {
	symbol: ^Symbol_Struct,
}

// ------------------------------
// Misc
// ------------------------------

// Name of a symbol.
Name :: struct #all_or_none {
	s:    string,
	span: Span,
}

// Name and type pair.
Pair :: struct #all_or_none {
	name: Name,
	type: Spanned(Complex_Type),
}

// Nodes inside `{ ... }`.
Body :: struct {
	nodes: [dynamic]Node,
	// Span of the opening brace `{`.
	start: Span,
	// Span of the closing brace `}`.
	end:   Span,
}
