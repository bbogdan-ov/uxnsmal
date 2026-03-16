package uxnsmal

// File AST.
File :: struct {
	// Immutable reference to a UXNSMAL source code string.
	source: string,
	nodes:  [dynamic]Node,
}

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
	User,
}
Type :: struct #all_or_none {
	kind: Type_Kind,
	base: union {
		// Type this pointer points to.
		^Type,
		// Signature of this function pointer.
		^Signature,
		// Name of this user-type.
		string,
	},
	span: Span,
}

// Argument of a stack signature.
Arg :: struct #all_or_none {
	type: Type,
	name: Maybe(Name),
	span: Span,
}

Signature_Vector :: struct {}
Signature_Proc :: struct #all_or_none {
	inputs:  [dynamic]Arg,
	outputs: [dynamic]Arg,
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

// Function definition.
Func_Def :: struct #all_or_none {
	name:      Name,
	signature: Signature,
	body:      Body,
}

// Variable definition.
Var_Def :: struct #all_or_none {
	name:   Name,
	type:   Type,
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

// Struct definition field.
Struct_Field :: struct #all_or_none {
	name: Name,
	type: Type,
}
// Struct definition.
Struct_Def :: struct #all_or_none {
	name:   Name,
	// NOTE: names of the fields may be the same, name colliding should be
	// resolved at the symbol collection stage.
	fields: [dynamic]Struct_Field,
}

// AST node.
Node :: union {
	Func_Def,
	Var_Def,
	Const_Def,
	Data_Def,
	Type_Alias_Def,
	Enum_Def,
	Struct_Def,
}
