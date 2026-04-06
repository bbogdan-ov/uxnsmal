#+vet explicit-allocators

package uxnsmal

import "core:fmt"
import "core:reflect"
import "core:strings"

Type_Byte :: struct {}
Type_Short :: struct {}
Type_Byte_Ptr :: struct {
	// Type this pointer (e.g. `^[10]short`) points to.
	// An immutable pointer.
	base: ^Complex_Type,
}
Type_Short_Ptr :: struct {
	// Type this pointer (e.g. `*byte`) points to.
	// An immutable pointer.
	base: ^Complex_Type,
}
Type_Func_Ptr :: struct {
	// Signature of this function pointer.
	// An immutable pointer.
	signature: Signature,
}
Type_Array :: struct {
	// Type of the elements in the array.
	// An immutable pointer.
	base:  ^Complex_Type,
	count: u32,
}
Type_Unsized_Array :: struct {
	// Type of the elements in the array.
	// An immutable pointer.
	base: ^Complex_Type,
}

// Can freely be copied without deep cloning, it is ok if `base` of different
// `Type` instances point to the same value, because these pointers are immutable.
Type :: union #no_nil {
	Type_Byte,
	Type_Short,
	Type_Byte_Ptr,
	Type_Short_Ptr,
	Type_Func_Ptr,
	^Symbol_Enum,
}

Complex_Type :: union #no_nil {
	Type,
	Type_Array,
	Type_Unsized_Array,
	^Symbol_Struct,
}

// ------------------------------
// Type.
// ------------------------------

type_make_complex :: proc(type: Type) -> Complex_Type {
	return Complex_Type(type)
}
type_make_short_ptr :: proc(
	base: Complex_Type,
	allocator := context.allocator,
	loc := #caller_location,
) -> Complex_Type {
	b := new_clone(base, allocator, loc)
	return Complex_Type(Type(Type_Short_Ptr{b}))
}
type_make_byte_ptr :: proc(
	base: Complex_Type,
	allocator := context.allocator,
	loc := #caller_location,
) -> Complex_Type {
	b := new_clone(base, allocator, loc)
	return Complex_Type(Type(Type_Byte_Ptr{b}))
}

// Returns whether two types are equal.
// Sized and unsized arrays with the same base type are equal.
type_eq :: proc(a, b: Type) -> bool {
	switch ty in a {
	case Type_Byte, Type_Short:
		a_tag := reflect.get_union_variant_raw_tag(a)
		b_tag := reflect.get_union_variant_raw_tag(b)
		return a_tag == b_tag
	case Type_Byte_Ptr:
		bp, ok := b.(Type_Byte_Ptr)
		return ok && complex_type_eq(ty.base^, bp.base^)
	case Type_Short_Ptr:
		bp, ok := b.(Type_Short_Ptr)
		return ok && complex_type_eq(ty.base^, bp.base^)
	case Type_Func_Ptr:
		bp, ok := b.(Type_Func_Ptr)
		return ok && signature_eq(ty.signature, bp.signature)
	case ^Symbol_Enum:
		bp, ok := b.(^Symbol_Enum)
		return ok && ty.name == bp.name
	case:
		unreachable()
	}
}

complex_type_eq :: proc(a, b: Complex_Type) -> bool {
	switch ty in a {
	case Type:
		bp, ok := b.(Type)
		return ok && type_eq(ty, bp)
	case Type_Array:
		if bp, ok := b.(Type_Array); ok {
			return complex_type_eq(ty.base^, bp.base^) && ty.count == bp.count
		} else if bp, ok := b.(Type_Unsized_Array); ok {
			return complex_type_eq(ty.base^, bp.base^)
		}
		return false
	case Type_Unsized_Array:
		if bp, ok := b.(Type_Array); ok {
			return complex_type_eq(ty.base^, bp.base^)
		} else if bp, ok := b.(Type_Unsized_Array); ok {
			return complex_type_eq(ty.base^, bp.base^)
		}
		return false
	case ^Symbol_Struct:
		bp, ok := b.(^Symbol_Struct)
		return ok && ty.name == bp.name
	case:
		unreachable()
	}
}

// ------------------------------
// Type.
// ------------------------------

type_eq_downcasted :: proc(a, b: Type) -> bool {
	ad := type_downcast(a)
	bd := type_downcast(b)
	return type_eq(ad, bd)
}
type_similar_downcasted :: proc(a, b: Type) -> bool {
	ad := type_downcast(a)
	bd := type_downcast(b)
	return type_similar(ad, bd)
}

// Returns whether two types are "similar".
// The difference from `type_eq` is that this function doesn't compare base
// types of pointers.
type_similar :: proc(a, b: Type) -> bool {
	switch ty in a {
	case Type_Byte, Type_Short:
		a_tag := reflect.get_union_variant_raw_tag(a)
		b_tag := reflect.get_union_variant_raw_tag(b)
		return a_tag == b_tag
	case Type_Byte_Ptr:
		_, ok := b.(Type_Byte_Ptr)
		return ok
	case Type_Short_Ptr:
		_, ok := b.(Type_Short_Ptr)
		return ok
	case Type_Func_Ptr:
		_, ok := b.(Type_Func_Ptr)
		return ok
	case ^Symbol_Enum:
		bp, ok := b.(^Symbol_Enum)
		return ok && ty.name == bp.name
	case:
		unreachable()
	}
}

complex_type_similar :: proc(a, b: Complex_Type) -> bool {
	switch ty in a {
	case Type:
		bp, ok := b.(Type)
		return ok && type_similar(ty, bp)
	case Type_Array, Type_Unsized_Array:
		_, is_sized := b.(Type_Array)
		_, is_unsized := b.(Type_Array)
		return is_sized && is_unsized
	case ^Symbol_Struct:
		bp, ok := b.(^Symbol_Struct)
		return ok && ty.name == bp.name
	case:
		unreachable()
	}
}

// Returns a size of a type in bytes.
// Should never return a value different from 1 or 2.
type_size :: proc(type: Type) -> u32 {
	switch ty in type {
	case Type_Byte:
		return 1
	case Type_Short:
		return 2
	case Type_Byte_Ptr:
		return 1
	case Type_Short_Ptr:
		return 2
	case Type_Func_Ptr:
		return 2
	case ^Symbol_Enum:
		return type_size(ty.derived)
	case:
		unreachable()
	}
}
type_is_short :: proc(type: Type) -> bool {
	return type_size(type) == 2
}

complex_type_size :: proc(type: Complex_Type, span: Span) -> (size: u32, err: Error) {
	switch ty in type {
	case Type:
		return type_size(ty), nil
	case Type_Array:
		size = complex_type_size(ty.base^, span) or_return
		return size * ty.count, nil
	case Type_Unsized_Array:
		// TODO: but why?
		MSG :: "can only take a pointer to an unsized array, got `%s`"
		err = problemf(span, MSG, type_tprint(type))
		return 0, err
	case ^Symbol_Struct:
		return ty.size, nil
	case:
		unreachable()
	}
}

// Downcasts user types to their derived types.
type_downcast :: proc(type: Type) -> Type {
	#partial switch ty in type {
	case ^Symbol_Enum:
		return ty.derived
	case:
		return type
	}
}

complex_type_downcast :: proc(type: Complex_Type) -> Complex_Type {
	#partial switch ty in type {
	case Type:
		#partial switch t in ty {
		case ^Symbol_Enum:
			return Complex_Type(t.derived)
		case:
			return type
		}
	case:
		return type
	}
}

// Returns whether a type is a byte or a short.
type_is_basic :: proc(type: Type) -> bool {
	#partial switch _ in type {
	case Type_Byte, Type_Short:
		return true
	case:
		return false
	}
}

to_stack_type :: proc(complex: Complex_Type, span: Span) -> (type: Type, err: Error) {
	err_impossible :: proc(type: Complex_Type, kind: string, span: Span) -> Problem {
		// TODO: but why?
		MSG :: "can't simply push a value of %s type onto a stack, got `%s`"
		err := problemf(span, MSG, kind, type_tprint(type))
		// TODO: should be a "help".
		problem_notef(&err, span, "may be you wanted to take a pointer?")
		return err
	}

	switch ty in complex {
	case Type:
		return ty, nil
	case Type_Array, Type_Unsized_Array:
		return {}, err_impossible(complex, "an array", span)
	case ^Symbol_Struct:
		return {}, err_impossible(complex, "a struct", span)
	case:
		unreachable()
	}
}

to_output_type :: proc(
	complex: Complex_Type,
	kind: string,
	span: Span,
) -> (
	type: Type,
	err: Error,
) {
	err_impossible :: proc(type: Complex_Type, name, kind: string, span: Span) -> Problem {
		// TODO: but why?
		MSG :: "since %s can't be pushed onto a stack, it is impossible to have such %s, got `%s`"
		err := problemf(span, MSG, name, kind, type_tprint(type))
		// TODO: should be a "help".
		problem_notef(&err, span, "may be you wanted to take a pointer?")
		return err
	}

	switch ty in complex {
	case Type:
		return ty, nil
	case Type_Array, Type_Unsized_Array:
		return {}, err_impossible(complex, "arrays", kind, span)
	case ^Symbol_Struct:
		return {}, err_impossible(complex, "structs", kind, span)
	case:
		unreachable()
	}
}

to_store_type :: proc(complex: Complex_Type, span: Span) -> (type: Type, err: Error) {
	err_impossible :: proc(type: Complex_Type, kind: string, span: Span) -> Problem {
		// TODO: but why?
		MSG :: "since %s can't be pushed onto a stack, it is impossible to store such values, got `%s`"
		return problemf(span, MSG, kind, type_tprint(type))
	}

	switch ty in complex {
	case Type:
		return ty, nil
	case Type_Array, Type_Unsized_Array:
		return {}, err_impossible(complex, "arrays", span)
	case ^Symbol_Struct:
		return {}, err_impossible(complex, "structs", span)
	case:
		unreachable()
	}
}

// ------------------------------
// Signature.
// ------------------------------

Arg :: struct {
	name: Name,
	type: Spanned(Type),
}

Signature_Vector :: struct {}
Signature_Proc :: struct #all_or_none {
	inputs:  [dynamic]Arg,
	outputs: [dynamic]Arg,
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
		if !complex_type_eq(a_proc.inputs[idx].type.x, b_proc.inputs[idx].type.x) {
			return false
		}
	}
	for idx in 0 ..< len(a_proc.outputs) {
		if !complex_type_eq(a_proc.outputs[idx].type.x, b_proc.outputs[idx].type.x) {
			return false
		}
	}

	return true
}

// ------------------------------
// Printing.
// ------------------------------

type_sbprint :: proc(sb: ^strings.Builder, type: Complex_Type) {
	switch ty in type {
	case Type:
		switch &_t in ty {
		case Type_Byte:
			fmt.sbprint(sb, "byte")
		case Type_Short:
			fmt.sbprint(sb, "short")
		case Type_Byte_Ptr:
			fmt.sbprint(sb, "^")
			type_sbprint(sb, _t.base^)
		case Type_Short_Ptr:
			fmt.sbprint(sb, "*")
			type_sbprint(sb, _t.base^)
		case Type_Func_Ptr:
			fmt.sbprint(sb, "fun")
			signature_sbprint(sb, _t.signature)
		case ^Symbol_Enum:
			fmt.sbprint(sb, _t.name.s)
		case:
			unreachable()
		}
	case Type_Array:
		fmt.sbprintf(sb, "[%d]", ty.count)
		type_sbprint(sb, ty.base^)
	case Type_Unsized_Array:
		fmt.sbprint(sb, "[]")
		type_sbprint(sb, ty.base^)
	case ^Symbol_Struct:
		fmt.sbprint(sb, ty.name.s)
	case:
		unreachable()
	}
}

// Formats and returns a string representation of a type allocated in the
// `context.temp_allocator`.
type_tprint :: proc(type: Complex_Type, loc := #caller_location) -> string {
	sb := strings.builder_make(context.temp_allocator, loc)
	type_sbprint(&sb, type)
	return strings.to_string(sb)
}

signature_sbprint :: proc(sb: ^strings.Builder, sig: Signature) {
	fmt.sbprint(sb, "( ")
	switch k in sig.kind {
	case Signature_Vector:
		fmt.sbprint(sb, "-> ")
	case Signature_Proc:
		for input in k.inputs {
			fmt.sbprintf(sb, "%s:", input.name.s)
			type_sbprint(sb, input.type.x)
			fmt.sbprint(sb, " ")
		}
		fmt.sbprint(sb, "-- ")
		for output in k.outputs {
			fmt.sbprintf(sb, "%s:", output.name.s)
			type_sbprint(sb, output.type.x)
			fmt.sbprint(sb, " ")
		}
	}
	fmt.sbprint(sb, ")")
}
