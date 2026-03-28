package uxnsmal

import "core:fmt"
import "core:reflect"
import "core:strings"
// AST node.
Node :: union #no_nil {
	// Definitions.
	Def_Func,
	Def_Var,
	Def_Const,
	Def_Data,
	Def_Type_Alias,
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
Def_Func :: struct #all_or_none {
	id:        ID,
	name:      Name,
	signature: Signature,
	body:      Body,
}

// Variable definition.
Def_Var :: struct #all_or_none {
	pairs:  [dynamic]Pair,
	// Whether this variable should be allocated in the ROM address space.
	in_rom: bool,
}

// Constant definition.
Def_Const :: struct #all_or_none {
	id:   ID,
	name: Name,
	type: Type,
	body: Body,
}

// Data definition.
Def_Data :: struct #all_or_none {
	id:   ID,
	name: Name,
	// Should only contain number, string and character literals.
	body: Body,
}

// User-defined alias to a type definition.
Def_Type_Alias :: struct #all_or_none {
	id:   ID,
	name: Name,
	base: Type,
}

// Enum definition variant.
Enum_Variant :: struct #all_or_none {
	name: Name,
	body: Maybe(Body),
}
// Enum definition.
Def_Enum :: struct #all_or_none {
	id:       ID,
	name:     Name,
	base:     Type,
	// NOTE: names of the variants may be the same, name colliding should be
	// resolved at the symbol collection stage.
	variants: [dynamic]Enum_Variant,
}

// Struct definition.
Def_Struct :: struct #all_or_none {
	id:     ID,
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

// Unique symbol definition ID.
// Should never be <= 0.
ID :: distinct u32

Type_Byte :: struct {}
Type_Short :: struct {}
Type_Byte_Ptr :: struct {
	// Type this pointer (e.g. `^[10]short`) points to.
	// An immutable pointer.
	base: ^Type,
}
Type_Short_Ptr :: struct {
	// Type this pointer (e.g. `*byte`) points to.
	// An immutable pointer.
	base: ^Type,
}
Type_Func_Ptr :: struct {
	// Signature of this function pointer.
	// An immutable pointer.
	signature: ^Signature,
}
Type_Array :: struct {
	// Type of the elements in the array.
	// An immutable pointer.
	base:  ^Type,
	count: i32,
}
Type_Unsized_Array :: struct {
	// Type of the elements in the array.
	// An immutable pointer.
	base: ^Type,
}
Type_User :: struct {
	// Name of this user-type.
	name: string,
}

// NOTE: may be nil which means it is an unknown type.
Type_Kind :: union {
	Type_Byte,
	Type_Short,
	Type_Byte_Ptr,
	Type_Short_Ptr,
	Type_Func_Ptr,
	Type_Array,
	Type_Unsized_Array,
	Type_User,
}

// Type.
// Can freely be copied without deep cloning, it is ok if `base` of different
// `Type` instances point to the same value, because these pointers are immutable.
Type :: struct #all_or_none {
	kind: Type_Kind,
	span: Span,
}

make_type :: proc(kind: Type_Kind, span := Span{}) -> Type {
	return Type{kind, span}
}
make_short_ptr :: proc(
	base: Type,
	allocator := context.allocator,
	loc := #caller_location,
) -> Type {
	b := new_clone(base, allocator, loc)
	return make_type(Type_Short_Ptr{b})
}
make_unsized_arr :: proc(
	base: Type,
	allocator := context.allocator,
	loc := #caller_location,
) -> Type {
	b := new_clone(base, allocator, loc)
	return make_type(Type_Unsized_Array{b})
}

// Return whether two types are equal.
// Sized and unsized arrays with the same base type are equal.
type_eq :: proc(a: Type, b: Type) -> bool {
	switch k in a.kind {
	case Type_Byte, Type_Short:
		a_tag := reflect.get_union_variant_raw_tag(a.kind)
		b_tag := reflect.get_union_variant_raw_tag(b.kind)
		return a_tag == b_tag
	case Type_Byte_Ptr:
		bp, ok := b.kind.(Type_Byte_Ptr)
		return ok && k.base == bp.base
	case Type_Short_Ptr:
		bp, ok := b.kind.(Type_Short_Ptr)
		return ok && k.base == bp.base
	case Type_Func_Ptr:
		bp, ok := b.kind.(Type_Func_Ptr)
		return ok && k.signature == bp.signature
	case Type_Array:
		if bp, ok := b.kind.(Type_Array); ok {
			return k.base == bp.base && k.count == bp.count
		} else if bp, ok := b.kind.(Type_Unsized_Array); ok {
			return k.base == bp.base
		}
	case Type_Unsized_Array:
		if bp, ok := b.kind.(Type_Array); ok {
			return k.base == bp.base
		} else if bp, ok := b.kind.(Type_Unsized_Array); ok {
			return k.base == bp.base
		}
	case Type_User:
		bp, ok := b.kind.(Type_User)
		return ok && k.name == bp.name
	}

	unreachable()
}

type_sbprint :: proc(sb: ^strings.Builder, t: Type, loc := #caller_location) {
	switch k in t.kind {
	case Type_Byte:
		fmt.sbprint(sb, "byte")
	case Type_Short:
		fmt.sbprint(sb, "short")
	case Type_Byte_Ptr:
		fmt.sbprint(sb, "^")
		type_sbprint(sb, k.base^)
	case Type_Short_Ptr:
		fmt.sbprint(sb, "*")
		type_sbprint(sb, k.base^)
	case Type_Func_Ptr:
		fmt.sbprint(sb, "fun")
		signature_sbprint(sb, k.signature^)
	case Type_Array:
		fmt.sbprintf(sb, "[%d]", k.count)
		type_sbprint(sb, k.base^)
	case Type_Unsized_Array:
		fmt.sbprint(sb, "[]")
		type_sbprint(sb, k.base^)
	case Type_User:
		fmt.sbprint(sb, k.name)
	}
}
// Formats and returns a string representation of a type allocated in the
// `context.temp_allocator`.
type_tprint :: proc(t: Type, loc := #caller_location) -> string {
	sb := strings.builder_make(context.temp_allocator, loc)
	type_sbprint(&sb, t, loc)
	return strings.to_string(sb)
}

// Name and type pair.
Pair :: struct #all_or_none {
	// ID is only used for a variable definition. Enums variants, structs
	// fields, and function arguments don't need it.
	id:   ID,
	name: Name,
	type: Type,
}

Signature_Vector :: struct {}
Signature_Proc :: struct #all_or_none {
	inputs:  [dynamic]Pair,
	outputs: [dynamic]Pair,
}
Signature_Kind :: union #no_nil {
	Signature_Vector,
	Signature_Proc,
}
// Function signature.
Signature :: struct {
	kind: Signature_Kind,
	span: Span,
}

signature_sbprint :: proc(sb: ^strings.Builder, sig: Signature) {
	fmt.sbprint(sb, "( ")
	switch k in sig.kind {
	case Signature_Vector:
		fmt.sbprint(sb, "-> ")
	case Signature_Proc:
		for input in k.inputs {
			fmt.sbprintf(sb, "%s:", input.name.s)
			type_sbprint(sb, input.type)
			fmt.sbprint(sb, " ")
		}
		fmt.sbprint(sb, "-- ")
		for output in k.outputs {
			fmt.sbprintf(sb, "%s:", output.name.s)
			type_sbprint(sb, output.type)
			fmt.sbprint(sb, " ")
		}
	}
	fmt.sbprint(sb, ")")
}

// Nodes inside `{ ... }`.
Body :: struct {
	nodes: [dynamic]Node,
	// Span of the opening brace `{`.
	start: Span,
	// Span of the closing brace `}`.
	end:   Span,
}
