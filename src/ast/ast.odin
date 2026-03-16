package ast

import lexer "../lexer"

// File AST.
File :: struct {
	// Immutable reference to a UXNSMAL source code string.
	source: string,
}

// Name of a symbol.
Name :: struct #all_or_none {
	s:    string,
	span: lexer.Span,
}

Type_Kind :: enum {
	Byte,
	Short,
	Byte_Ptr,
	Short_Ptr,
	Func_Ptr,
}
Type :: struct #all_or_none {
	kind: Type_Kind,
	// Type this pointer points to (if this is a pointer type).
	base: union {
		^Type,
		^Signature,
	},
	span: lexer.Span,
}

// Argument of a stack signature.
Arg :: struct #all_or_none {
	type: Type,
	name: Maybe(Name),
	span: lexer.Span,
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
	span: lexer.Span,
}
