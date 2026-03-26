package uxnsmal

// AST node.
Node :: union {
	// Definitions.
	Func_Def,
	Var_Def,
	Const_Def,
	Data_Def,
	Type_Alias_Def,
	Enum_Def,
	Struct_Def,

	// Expressions.
	Expr_Symbol,
	Expr_Intr,
	Expr_Byte,
	Expr_Short,
	Expr_String,
	Expr_Char,
	Expr_Store,
	Expr_Bind,
	Expr_Expect,
	Expr_Cast,
	Expr_If,
	Expr_While,
	Expr_Break,
}

// ------------------------------
// Expressions.
// ------------------------------

// Symbol member access.
Member :: struct #all_or_none {
	name:     Name,
	// Whether accession this member as an array.
	// Example: `my_var.field[]`
	as_array: bool,
	span:     Span,
}
// Symbol use.
Expr_Symbol :: struct #all_or_none {
	// Members access of a symbol, e.g. a struct or an enum.
	// There is always at least one item and the first one is always the name
	// of the symbol itself.
	members: [dynamic]Member,
	// Whether a pointer is taken to this symbol.
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
// Character literal, pushes a byte associated with this ASCII char.
Expr_Char :: struct #all_or_none {
	byte: u8,
	span: Span,
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
	types: [dynamic]Type,
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
Func_Def :: struct #all_or_none {
	name:      Name,
	signature: Signature,
	body:      Body,
}

// Variable definition.
Var_Def :: struct #all_or_none {
	pairs:  [dynamic]Pair,
	// Whether this variable should be allocated in the ROM address space.
	in_rom: bool,
}

// Constant definition.
Const_Def :: struct #all_or_none {
	name: Name,
	type: Type,
	body: Body,
}

// Data definition.
Data_Def :: struct #all_or_none {
	name: Name,
	// Should only contain number, string and character literals.
	body: Body,
}

// User-defined alias to a type definition.
Type_Alias_Def :: struct #all_or_none {
	name: Name,
	base: Type,
}

// Enum definition variant.
Enum_Variant :: struct #all_or_none {
	name: Name,
	body: Maybe(Body),
}
// Enum definition.
Enum_Def :: struct #all_or_none {
	name:     Name,
	base:     Type,
	// NOTE: names of the variants may be the same, name colliding should be
	// resolved at the symbol collection stage.
	variants: [dynamic]Enum_Variant,
}

// Struct definition.
Struct_Def :: struct #all_or_none {
	name:   Name,
	// NOTE: names of the fields may be the same, name colliding should be
	// resolved at the symbol collection stage.
	fields: [dynamic]Pair,
}

// ------------------------------
// Misc
// ------------------------------

// Name of a symbol.
Name :: struct #all_or_none {
	s:    string,
	span: Span,
}

Type_Kind :: enum {
	Byte,
	Short,
	Byte_Ptr,
	Short_Ptr,
	Func_Ptr,
	Array,
	Unsized_Array,
	User,
}
Type :: struct #all_or_none {
	kind:  Type_Kind,
	base:  union {
		// Type this pointer points to.
		^Type,
		// Signature of this function pointer.
		^Signature,
		// Name of this user-type.
		string,
	},
	// Count of this array type.
	count: i32,
	span:  Span,
}

// Name and type pair.
Pair :: struct #all_or_none {
	name: Name,
	type: Type,
}

Signature_Vector :: struct {}
Signature_Proc :: struct #all_or_none {
	inputs:  [dynamic]Pair,
	outputs: [dynamic]Pair,
}
// Function signature.
Signature :: struct {
	kind: union {
		Signature_Vector,
		Signature_Proc,
	},
	span: Span,
}

// Nodes inside `{ ... }`.
Body :: struct {
	nodes: [dynamic]Node,
	// Span of the opening brace `{`.
	start: Span,
	// Span of the closing brace `}`.
	end:   Span,
}
