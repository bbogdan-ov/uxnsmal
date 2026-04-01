package uxnsmal

Symbol :: union #no_nil {
	Symbol_Func,
	Symbol_Var,
	Symbol_Const,
	Symbol_Data,
	Symbol_User_Type,
}

Symbol_Func :: struct #all_or_none {
	id:         ID,
	name:       Name,
	signature:  Signature,
	defined_at: Span,
}
Symbol_Var :: struct #all_or_none {
	id:         ID,
	name:       Name,
	type:       Type,
	in_rom:     bool,
	defined_at: Span,
}
Symbol_Const :: struct #all_or_none {
	id:         ID,
	name:       Name,
	type:       Type,
	defined_at: Span,
}
Symbol_Data :: struct #all_or_none {
	id:         ID,
	name:       Name,
	defined_at: Span,
}

Symbol_User_Type :: union #no_nil {
	User_Type_Alias,
	User_Type_Enum,
	User_Type_Struct,
}
User_Type_Alias :: struct #all_or_none {
	id:         ID,
	name:       Name,
	derived:    Type,
	defined_at: Span,
}
User_Type_Enum :: struct #all_or_none {
	id:         ID,
	name:       Name,
	derived:    Type,
	variants:   map[string]Span,
	defined_at: Span,
}
User_Type_Struct :: struct #all_or_none {
	id:         ID,
	name:       Name,
	fields:     map[string]Struct_Field,
	defined_at: Span,
}
Struct_Field :: struct #all_or_none {
	type: Type,
	span: Span,
}

symbol_name :: proc(s: Symbol) -> Name {
	// odinfmt: disable
	switch sym in s {
	case Symbol_Func:  return sym.name
	case Symbol_Var:   return sym.name
	case Symbol_Const: return sym.name
	case Symbol_Data:  return sym.name
	case Symbol_User_Type:
		switch ty in sym {
		case User_Type_Alias:  return ty.name
		case User_Type_Enum:   return ty.name
		case User_Type_Struct: return ty.name
		}
	}
	// odinfmt: enable

	unreachable()
}
symbol_kind_str :: proc(s: Symbol) -> string {
	// odinfmt: disable
	switch sym in s {
	case Symbol_Func:  return "function"
	case Symbol_Var:   return "variable"
	case Symbol_Const: return "constant"
	case Symbol_Data:  return "data"
	case Symbol_User_Type:
		switch ty in sym {
		case User_Type_Alias:  return "user type"
		case User_Type_Enum:   return "enum"
		case User_Type_Struct: return "struct"
		}
	}
	// odinfmt: enable

	unreachable()
}
symbol_defined_at :: proc(s: Symbol) -> Span {
	// odinfmt: disable
	switch sym in s {
	case Symbol_Func:  return sym.defined_at
	case Symbol_Var:   return sym.defined_at
	case Symbol_Const: return sym.defined_at
	case Symbol_Data:  return sym.defined_at
	case Symbol_User_Type:
		switch ty in sym {
		case User_Type_Alias:  return ty.defined_at
		case User_Type_Enum:   return ty.defined_at
		case User_Type_Struct: return ty.defined_at
		}
	}
	// odinfmt: enable

	unreachable()
}

Resolved_Member :: struct {
	symbol:     ^Symbol,
	type:       Type,
	defined_at: Span,
	as_array:   bool,
}

@(require_results)
symbol_resolve_members :: proc(
	t: ^Typechecker,
	members: []Member,
	span: Span,
) -> (
	resolved: Resolved_Member,
	ok: bool,
) {
	first := &members[0]
	accessing_fields := len(members) >= 2

	symbol: ^Symbol
	symbol, ok = &t.symbols[first.name.s]
	if !ok {
		err := problemf(first.name.span, "no symbol `%s` found in this scope", first.name.s)
		return {}, error(t, err)
	}

	switch &s in symbol {
	case Symbol_Func:
		if accessing_fields {
			MSG :: "`%s` is a function, therefore it has no fields"
			err := problemf(span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return {}, error(t, err)
		} else if first.as_array_count > 0 {
			MSG :: "trying to access the function `%s` as an array"
			err := problemf(first.brackets_span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return {}, error(t, err)
		}

		resolved = Resolved_Member{symbol, {}, s.defined_at, false}
		return resolved, true

	case Symbol_Var:
		resolved, ok = _var_resolve_members(t, &s, members)
		resolved.symbol = symbol
		return resolved, ok

	case Symbol_Const:
		if accessing_fields {
			// TODO: but why?
			MSG :: "`%s` is a constant, therefore it has no fields"
			err := problemf(span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return {}, error(t, err)
		} else if first.as_array_count > 0 {
			// TODO: but why?
			MSG :: "can't access a constant as an array"
			err := problemf(span, MSG)
			problem_notef(&err, first.brackets_span, "try removing the `[]`")
			problem_notef(&err, s.defined_at, "defined here")
			return {}, error(t, err)
		}

		resolved = Resolved_Member{symbol, s.type, s.defined_at, false}
		return resolved, true

	case Symbol_Data:
		if accessing_fields {
			// TODO: but why?
			MSG :: "`%s` is a data, therefore it has no fields"
			err := problemf(span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return {}, error(t, err)
		}

		assert(first.as_array_count == 0, "TODO:")

		panic("TODO:")

	case Symbol_User_Type:
		enum_type, is_enum := s.(User_Type_Enum)
		if !is_enum {
			MSG :: "unexpected use of the user type `%s`"
			err := problemf(span, MSG, symbol_name(symbol^).s)
			problem_notef(&err, symbol_defined_at(symbol^), "defined here")
			return {}, error(t, err)
		}


		if len(members) < 2 {
			// TODO: enum usage example.
			err := problemf(span, "variant must be specified for an enum")
			problem_notef(&err, enum_type.defined_at, "defined here")
			return {}, error(t, err)
		} else if len(members) > 2 {
			err := problemf(span, "unexpected multiple enum variants access")
			problem_notef(&err, enum_type.defined_at, "defined here")
			return {}, error(t, err)
		}

		as_array := members[0].as_array_count > 0
		as_array ||= members[1].as_array_count > 0
		if as_array {
			err := problemf(span, "can't access an enum as an array")

			array_member := &members[0]
			if members[1].as_array_count > 0 {
				array_member = &members[1]
			}

			problem_notef(&err, array_member.brackets_span, "try removing the `[]`")
			problem_notef(&err, enum_type.defined_at, "defined here")
			return {}, error(t, err)
		}

		sec := &members[1]
		variant, ok := enum_type.variants[sec.name.s]
		if !ok {
			MSG :: "enum `%s` doesn't have a variant `%s`"
			err := problemf(span, MSG, enum_type.name.s, sec.name.s)
			problem_notef(&err, enum_type.defined_at, "defined here")
			return {}, error(t, err)
		}

		type := make_type(Type_User{enum_type.name.s})
		resolved = Resolved_Member{symbol, type, variant, false}
		return resolved, true
	}

	unreachable()
}
@(private)
_var_resolve_members :: proc(
	t: ^Typechecker,
	symbol: ^Symbol_Var,
	members: []Member,
) -> (
	resolved: Resolved_Member,
	ok: bool,
) {
	idx := 0
	member := &members[0]
	member_type := &symbol.type
	member_defined_at := symbol.defined_at
	as_array := false

	value_span := members[0].span

	// Resolve field access.
	for {
		if member.as_array_count > 0 && as_array || member.as_array_count >= 2 {
			// TODO: example on how to do that right
			MSG :: "can't access nested arrays like this"
			err := problemf(member.brackets_span, MSG)
			return {}, error(t, err)
		}
		if member.as_array_count > 0 {
			as_array = true

			#partial switch k in member_type.kind {
			case Type_Array:
				member_type = k.base
			case Type_Unsized_Array:
				member_type = k.base
			case:
				MSG :: "type of the value is a `%s`, which is not an array"

				// TODO: show how to load a pointer to an array.
				err := problemf(value_span, MSG, type_tprint(member_type^))
				problem_notef(&err, member_defined_at, "defined here")
				return {}, error(t, err)
			}
		}

		// Code below will be executed only when there are more than one member
		// in the symbol expression.
		idx += 1
		if idx >= len(members) {
			break
		}

		// Get a struct type of the current member.
		is_struct := false
		struct_type: ^User_Type_Struct

		type_user, is_user := member_type.kind.(Type_User)
		if is_user {
			user_type := symbol_get_user_type(t, type_user.name)
			struct_type, is_struct = &user_type.(User_Type_Struct)
		}
		if !is_struct {
			MSG :: "type of the value is a `%s`, which is not a struct"

			// TODO: suggest to use "[]" if the type is an array.
			err := problemf(value_span, MSG, type_tprint(member_type^))
			problem_notef(&err, member_defined_at, "defined here")
			return {}, error(t, err)
		}

		assert(struct_type != nil)

		// Getting a struct field for the next iteration.
		member = &members[idx]
		value_span.end = member.span.end

		field, found := &struct_type.fields[member.name.s]
		if !found {
			MSG :: "struct type `%s` doesn't have field `%s`"
			err := problemf(member.name.span, MSG, struct_type.name.s, member.name.s)
			problem_notef(&err, struct_type.defined_at, "defined here")
			return {}, error(t, err)
		}

		member_type = &field.type
		member_defined_at = field.span
	}

	resolved = Resolved_Member{nil, member_type^, member_defined_at, as_array}
	return resolved, true
}
