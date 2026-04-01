package uxnsmal

Symbol :: union #shared_nil {
	^Symbol_Func,
	^Symbol_Var,
	^Symbol_Const,
	^Symbol_Data,
	^Symbol_Alias,
	^Symbol_Enum,
	^Symbol_Struct,
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
	type:       Complex_Type,
	size:       u32,
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
Symbol_Alias :: struct #all_or_none {
	name:       Name,
	derived:    Complex_Type,
	defined_at: Span,
}

Symbol_Enum :: struct #all_or_none {
	id:         ID,
	name:       Name,
	derived:    Type,
	defined_at: Span,
	variants:   map[string]Enum_Variant,
}
Enum_Variant :: struct #all_or_none {
	name: Name,
	body: Maybe(Body),
}

Symbol_Struct :: struct {
	name:       Name,
	defined_at: Span,
	fields:     map[string]Pair,
	size:       u32,
}

@(require_results)
symbol_define :: proc(state: ^State, symbol: Symbol, loc := #caller_location) -> Error {
	name := symbol_name(symbol)
	assert(name.s != "", "defining a symbol with an empty name", loc)

	prev, found := &state.symbols[name.s]
	if found {
		// TODO: "all symbol share the same name space" help.
		MSG :: "name `%s` is already taken by a %s"
		err := problemf(name.span, MSG, name.s, symbol_kind_str(prev^))
		problem_notef(&err, symbol_defined_at(prev^), "previously defined here")
		return err
	}

	map_insert(&state.symbols, name.s, symbol)
	return nil
}

symbol_get :: proc(state: ^State, name: string, span: Span) -> (symbol: Symbol, err: Error) {
	found: bool
	symbol, found = state.symbols[name]
	if !found {
		err = problemf(span, "undefined symbol `%s`", name)
		return nil, err
	}
	return symbol, nil
}

symbol_name :: proc(s: Symbol) -> Name {
	// odinfmt: disable
	switch sym in s {
	case ^Symbol_Func:   return sym.name
	case ^Symbol_Var:    return sym.name
	case ^Symbol_Const:  return sym.name
	case ^Symbol_Data:   return sym.name
	case ^Symbol_Alias:  return sym.name
	case ^Symbol_Enum:   return sym.name
	case ^Symbol_Struct: return sym.name
	}
	// odinfmt: enable

	unreachable()
}
symbol_kind_str :: proc(symbol: Symbol) -> string {
	// odinfmt: disable
	switch s in symbol {
	case ^Symbol_Func:   return "function"
	case ^Symbol_Var:    return "variable"
	case ^Symbol_Const:  return "constant"
	case ^Symbol_Data:   return "data"
	case ^Symbol_Alias:  return "type alias"
	case ^Symbol_Enum:   return "enum"
	case ^Symbol_Struct: return "struct"
	}
	// odinfmt: enable

	unreachable()
}
symbol_defined_at :: proc(s: Symbol) -> Span {
	// odinfmt: disable
	switch sym in s {
	case ^Symbol_Func:   return sym.defined_at
	case ^Symbol_Var:    return sym.defined_at
	case ^Symbol_Const:  return sym.defined_at
	case ^Symbol_Data:   return sym.defined_at
	case ^Symbol_Alias:  return sym.defined_at
	case ^Symbol_Enum:   return sym.defined_at
	case ^Symbol_Struct: return sym.defined_at
	}
	// odinfmt: enable

	unreachable()
}

Resolved_Member :: struct {
	symbol:     Symbol,
	type:       Complex_Type,
	defined_at: Span,
	as_array:   bool,
}

@(require_results)
symbol_resolve_members :: proc(
	state: ^State,
	members: []Member,
	span: Span,
) -> (
	resolved: Resolved_Member,
	err: Error,
) {
	first := &members[0]
	accessing_fields := len(members) >= 2

	symbol, ok := state.symbols[first.name.s]
	if !ok {
		err = problemf(first.name.span, "no symbol `%s` found in this scope", first.name.s)
		return {}, err
	}

	err_unexpected_use :: proc(symbol: Symbol, span: Span) -> Error {
		name := symbol_name(symbol).s
		err := problemf(span, "unexpected use of %s `%s`", symbol_kind_str(symbol), name)
		problem_notef(&err, symbol_defined_at(symbol), "defined here")
		return err
	}

	switch s in symbol {
	case ^Symbol_Alias, ^Symbol_Struct:
		return {}, err_unexpected_use(symbol, span)

	case ^Symbol_Var:
		return _var_resolve_members(s, members)

	case ^Symbol_Enum:
		return _resolve_enum_members(s, members)

	case ^Symbol_Func:
		if accessing_fields {
			err = err_symbol(
				span,
				s.defined_at,
				"`%s` is a function, therefore it has no fields",
				s.name.s,
			)
			return {}, err
		} else if first.as_array_count > 0 {
			err = err_symbol(
				span,
				s.defined_at,
				"can't access a function as an array, got function `%s`",
				s.name.s,
			)
			return {}, err
		}

		resolved = Resolved_Member{s, {}, s.defined_at, false}
		return resolved, nil

	case ^Symbol_Const:
		if accessing_fields {
			// TODO: but why?
			MSG :: "`%s` is a constant, therefore it has no fields"
			err := problemf(span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return {}, err
		} else if first.as_array_count > 0 {
			// TODO: but why?
			MSG :: "can't access a constant as an array"
			err := problemf(span, MSG)
			problem_notef(&err, first.brackets_span, "try removing the `[]`")
			problem_notef(&err, s.defined_at, "defined here")
			return {}, err
		}

		resolved = Resolved_Member{s, s.type, s.defined_at, false}
		return resolved, nil

	case ^Symbol_Data:
		if accessing_fields {
			// TODO: but why?
			MSG :: "`%s` is a data, therefore it has no fields"
			err := problemf(span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return {}, err
		} else if first.as_array_count > 1 {
			err := problemf(first.brackets_span, "data can't be accessed as a nested array")

			// Exclude the first occurense of [] from the span.
			span := first.brackets_span
			off := len("[]")
			span.column += off
			span.start += off

			problem_notef(&err, span, "try removing these")
			return {}, err
		}

		as_array := first.as_array_count > 0
		resolved = Resolved_Member{s, {}, s.defined_at, as_array}
		return resolved, nil

	case:
		unreachable()
	}
}
@(private)
_resolve_enum_members :: proc(
	symbol: ^Symbol_Enum,
	members: []Member,
) -> (
	resolved: Resolved_Member,
	err: Error,
) {
	span := members[0].name.span

	if len(members) < 2 {
		// TODO: enum usage example.
		err := problemf(span, "variant must be specified for an enum")
		problem_notef(&err, symbol.defined_at, "defined here")
		return {}, err
	} else if len(members) > 2 {
		err := problemf(span, "unexpected multiple enum variants access")
		problem_notef(&err, symbol.defined_at, "defined here")
		return {}, err
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
		problem_notef(&err, symbol.defined_at, "defined here")
		return {}, err
	}

	sec := &members[1]
	variant, found := symbol.variants[sec.name.s]
	if !found {
		MSG :: "enum `%s` doesn't have a variant `%s`"
		err := problemf(span, MSG, symbol.name.s, sec.name.s)
		problem_notef(&err, symbol.defined_at, "defined here")
		return {}, err
	}

	resolved = Resolved_Member{symbol, type_make_complex(symbol), variant.name.span, false}
	return resolved, nil
}
@(private)
_var_resolve_members :: proc(
	symbol: ^Symbol_Var,
	members: []Member,
) -> (
	resolved: Resolved_Member,
	err: Error,
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
			err := problemf(member.brackets_span, "can't access nested arrays like this")
			return {}, err
		}
		if member.as_array_count > 0 {
			as_array = true

			#partial switch ty in member_type {
			case Type_Array:
				member_type = ty.base
			case Type_Unsized_Array:
				member_type = ty.base
			case:
				MSG :: "type of the value is a `%s`, which is not an array"

				// TODO: show how to load a pointer to an array.
				err := problemf(value_span, MSG, type_tprint(member_type^))
				problem_notef(&err, member_defined_at, "defined here")
				return {}, err
			}
		}

		// Code below will be executed only when there are more than one member
		// in the symbol expression.
		idx += 1
		if idx >= len(members) {
			break
		}

		// Get a struct type of the current member.
		sym_struct, is_struct := member_type.(^Symbol_Struct)
		if !is_struct {
			MSG :: "type of the value is a `%s`, which is not a struct"

			// TODO: suggest to use "[]" if the type is an array.
			err := problemf(value_span, MSG, type_tprint(member_type^))
			problem_notef(&err, member_defined_at, "defined here")
			return {}, err
		}

		assert(sym_struct != nil)

		// Getting a struct field for the next iteration.
		member = &members[idx]
		value_span.end = member.span.end

		field, found := &sym_struct.fields[member.name.s]
		if !found {
			MSG :: "struct type `%s` doesn't have field `%s`"
			err := problemf(member.name.span, MSG, sym_struct.name.s, member.name.s)
			problem_notef(&err, sym_struct.defined_at, "defined here")
			return {}, err
		}

		member_type = &field.type.x
		member_defined_at = field.name.span
	}

	resolved = Resolved_Member{symbol, member_type^, member_defined_at, as_array}
	return resolved, nil
}
