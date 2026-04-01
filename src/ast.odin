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

node_span :: proc(node: Node) -> Span {
	// odinfmt: disable
	switch n in node {
	case Def_Func:       return n.name.span
	case Def_Var:        return n.names_span
	case Def_Const:      return n.name.span
	case Def_Data:       return n.name.span
	case Def_Type_Alias: return n.name.span
	case Def_Enum:       return n.name.span
	case Def_Struct:     return n.name.span
	case Expr_Symbol:    return n.span
	case Expr_Intr:      return n.span
	case Expr_Byte:      return n.span
	case Expr_Short:     return n.span
	case Expr_String:    return n.span
	case Expr_Store:     return n.span
	case Expr_Bind:      return n.span
	case Expr_Expect:    return n.span
	case Expr_Cast:      return n.span
	case Expr_If:        return n.if_block.keyword_span
	case Expr_While:     return n.keyword_span
	case Expr_Break:     return n.span
	}
	// odinfmt: enable
	unreachable()
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
	pairs:      [dynamic]Pair,
	// Whether this variable should be allocated in the ROM address space.
	in_rom:     bool,
	names_span: Span,
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
	id:      ID,
	name:    Name,
	derived: Type,
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
	derived:  Type,
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
	signature: Signature,
}
Type_Array :: struct {
	// Type of the elements in the array.
	// An immutable pointer.
	base:  ^Type,
	count: u32,
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
make_byte_ptr :: proc(
	base: Type,
	allocator := context.allocator,
	loc := #caller_location,
) -> Type {
	b := new_clone(base, allocator, loc)
	return make_type(Type_Byte_Ptr{b})
}
make_unsized_arr :: proc(
	base: Type,
	allocator := context.allocator,
	loc := #caller_location,
) -> Type {
	b := new_clone(base, allocator, loc)
	return make_type(Type_Unsized_Array{b})
}

type_eq_downcasted :: proc(t: ^Typechecker, a, b: Type, loc := #caller_location) -> bool {
	ad := type_downcast(t, a, loc)
	bd := type_downcast(t, b, loc)
	return type_eq(ad, bd)
}
type_similar_downcasted :: proc(t: ^Typechecker, a, b: Type, loc := #caller_location) -> bool {
	ad := type_downcast(t, a, loc)
	bd := type_downcast(t, b, loc)
	return type_similar(ad, bd)
}

// Return whether two types are equal.
// Sized and unsized arrays with the same base type are equal.
type_eq :: proc(a, b: Type) -> bool {
	switch k in a.kind {
	case Type_Byte, Type_Short:
		a_tag := reflect.get_union_variant_raw_tag(a.kind)
		b_tag := reflect.get_union_variant_raw_tag(b.kind)
		return a_tag == b_tag
	case Type_Byte_Ptr:
		bp, ok := b.kind.(Type_Byte_Ptr)
		return ok && type_eq(k.base^, bp.base^)
	case Type_Short_Ptr:
		bp, ok := b.kind.(Type_Short_Ptr)
		return ok && type_eq(k.base^, bp.base^)
	case Type_Func_Ptr:
		bp, ok := b.kind.(Type_Func_Ptr)
		return ok && signature_eq(k.signature, bp.signature)
	case Type_Array:
		if bp, ok := b.kind.(Type_Array); ok {
			return type_eq(k.base^, bp.base^) && k.count == bp.count
		} else if bp, ok := b.kind.(Type_Unsized_Array); ok {
			return type_eq(k.base^, bp.base^)
		}
	case Type_Unsized_Array:
		if bp, ok := b.kind.(Type_Array); ok {
			return type_eq(k.base^, bp.base^)
		} else if bp, ok := b.kind.(Type_Unsized_Array); ok {
			return type_eq(k.base^, bp.base^)
		}
	case Type_User:
		bp, ok := b.kind.(Type_User)
		return ok && k.name == bp.name
	}

	return false
}

// Returns whether two types are "similar".
// The difference from `type_eq` is that this function doesn't compare base
// types of pointers.
type_similar :: proc(a, b: Type) -> bool {
	switch k in a.kind {
	case Type_Byte, Type_Short:
		a_tag := reflect.get_union_variant_raw_tag(a.kind)
		b_tag := reflect.get_union_variant_raw_tag(b.kind)
		return a_tag == b_tag
	case Type_Byte_Ptr:
		_, ok := b.kind.(Type_Byte_Ptr)
		return ok
	case Type_Short_Ptr:
		_, ok := b.kind.(Type_Short_Ptr)
		return ok
	case Type_Func_Ptr:
		_, ok := b.kind.(Type_Func_Ptr)
		return ok
	case Type_Array, Type_Unsized_Array:
		_, sized := b.kind.(Type_Array)
		_, unsized := b.kind.(Type_Unsized_Array)
		return sized || unsized
	case Type_User:
		bp, ok := b.kind.(Type_User)
		return ok && k.name == bp.name
	}
	return false
}

// Returns whether a type is a byte or a short.
type_is_basic :: proc(type: Type) -> bool {
	#partial switch _ in type.kind {
	case Type_Byte:
		return true
	case Type_Short:
		return true
	case:
		return false
	}
}

// Returns size of a type in bytes.
// Should never return a value different from 1 or 2.
type_size :: proc(t: ^Typechecker, type: Type, loc := #caller_location) -> u32 {
	// odinfmt: disable
	switch k in type.kind {
	case Type_Byte:      return 1
	case Type_Short:     return 2
	case Type_Byte_Ptr:  return 1
	case Type_Short_Ptr: return 2
	case Type_Func_Ptr:  return 2
	case Type_Array:
		return type_size(t, k.base^, loc) * k.count
	case Type_User:
		user_type := symbol_get_user_type(t, k.name, loc)
		enum_type, is_enum := user_type.(User_Type_Enum)
		assert(is_enum, loc = loc)
		assert(type_is_basic(enum_type.derived), loc = loc)

		return type_size(t, enum_type.derived, loc)
	case Type_Unsized_Array:
		panic("uxnsmal.type_size: can't be an unsized array", loc)
	case:
		unreachable()
	}
	// odinfmt: enable
}
type_is_short :: proc(t: ^Typechecker, type: Type, loc := #caller_location) -> bool {
	return type_size(t, type, loc) == 2
}

// Downcasts user types to their derived types "simple" types.
type_downcast :: proc(t: ^Typechecker, type: Type, loc := #caller_location) -> Type {
	#partial switch k in type.kind {
	case Type_Array, Type_Unsized_Array:
		panic("uxnsmal.type_downcast: can't be an array", loc)
	case Type_User:
		user_type := symbol_get_user_type(t, k.name, loc)
		enum_type, is_enum := user_type.(User_Type_Enum)
		assert(is_enum, loc = loc)
		assert(type_is_basic(enum_type.derived), loc = loc)
		return enum_type.derived
	case:
		return type
	}
}

type_valid :: proc(type: Type) -> bool {
	return type.kind != nil
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
		signature_sbprint(sb, k.signature)
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

signature_eq :: proc(a, b: Signature) -> bool {
	a_proc, a_is_proc := a.kind.(Signature_Proc)
	b_proc, b_is_proc := b.kind.(Signature_Proc)
	if a_is_proc != b_is_proc {
		return false
	}
	if !a_is_proc && !b_is_proc {
		return true
	}

	for idx in 0 ..< len(a_proc.inputs) {
		if !type_eq(a_proc.inputs[idx].type, b_proc.inputs[idx].type) {
			return false
		}
	}
	for idx in 0 ..< len(a_proc.outputs) {
		if !type_eq(a_proc.outputs[idx].type, b_proc.outputs[idx].type) {
			return false
		}
	}

	return true
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
