package uxnsmal

import "core:fmt"

Typechecker :: struct {
	state:   ^State,
	symbols: map[string]Symbol,
	errored: bool,
	// Working stack.
	ws:      Stack,
	// Return stack.
	rs:      Stack,
}

// Stack item.
Item :: struct {
	type:      Type,
	pushed_at: Span,
	name:      Maybe(string),
}
Stack_Kind :: enum {
	Working,
	Return,
}
Stack :: struct {
	kind:        Stack_Kind,
	items:       [dynamic]Item,
	keep:        bool,
	keep_cursor: int,
}

stack_push_item :: proc(t: ^Typechecker, s: ^Stack, item: Item, loc := #caller_location) {
	#partial switch k in item.type.kind {
	case Type_Array:
		panic("uxnsmal.stack_push_item: trying to push Type_Array", loc)
	case Type_Unsized_Array:
		panic("uxnsmal.stack_push_item: trying to push Type_Unsized_Array", loc)
	case Type_User:
		user_type := symbol_get_user_type(t, k.name)
		switch type in user_type {
		case User_Type_Enum: // ok
		case User_Type_Alias:
			panic("uxnsmal.stack_push_item: trying to push User_Type_Alias", loc)
		case User_Type_Struct:
			panic("uxnsmal.stack_push_item: trying to push User_Type_Struct", loc)
		}
	}

	// TODO: warn if the size of a stack exceeds the limit (256 bytes by default).
	append(&s.items, item)
	s.keep_cursor = 0
}
stack_push :: proc(
	t: ^Typechecker,
	s: ^Stack,
	type: Type,
	pushed_at: Span,
	name: Maybe(string) = nil,
	loc := #caller_location,
) {
	item := Item{type, pushed_at, name}
	stack_push_item(t, s, item, loc)
}
@(require_results)
stack_pop_safe :: proc(s: ^Stack) -> (item: Item, ok: bool) {
	if s.keep {
		n := len(s.items)
		if s.keep_cursor >= n {
			return {}, false
		}

		item = s.items[n - 1 - s.keep_cursor]
		s.keep_cursor += 1
		return item, true
	} else {
		s.keep_cursor = 0
		return pop_safe(&s.items)
	}
}
@(require_results)
stack_pop :: proc(s: ^Stack, loc := #caller_location) -> Item {
	item, ok := stack_pop_safe(s)
	assert(ok, "uxnsmal.stack_pop: stack is empty", loc)
	return item
}
// Get a slice of the last N items in a stack.
stack_last :: proc(s: ^Stack, n: int, loc := #caller_location) -> []Item {
	assert(n <= len(s.items), loc = loc)

	l := len(s.items)
	return s.items[l - n:]
}
stack_notes_caused_by :: proc(s: ^Stack, p: ^Problem, n: int, loc := #caller_location) {
	if n <= 0 do return

	caused := stack_last(s, n, loc)
	for i in 1 ..= n {
		// TODO: "spits N items" note on function and intrinsic calls.
		problem_notef(p, caused[n - i].pushed_at, "caused by this")
	}
}
stack_name :: proc(kind: Stack_Kind) -> string {
	switch kind {
	case .Working:
		return "working"
	case .Return:
		return "return"
	}
	unreachable()
}

item_name :: proc(item: Item) -> string {
	name, ok := item.name.?
	if ok {
		return name
	} else {
		return "_"
	}
}

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

// Initializes a `Typechecker` and prerforms type-checking on an AST.
@(require_results)
typecheck :: proc(state: ^State) -> (ok: bool) {
	context.allocator = state.allocator

	t: Typechecker
	t.state = state
	t.symbols = make(map[string]Symbol)
	t.ws.kind = .Working
	t.ws.items = make([dynamic]Item)
	t.rs.kind = .Return
	t.rs.items = make([dynamic]Item)

	// Collect symbols.
	err := collect(&t, state.nodes[:])
	if problem, ok := err.(Problem); ok {
		append(&state.problems, problem)
		return false
	}

	// Check top-level nodes.
	check_nodes(&t, state.nodes[:]) or_return

	return !t.errored
}

// Walk an AST and collect all global (TODO: collect local symbols as well)
// symbol definitions.
@(require_results)
collect :: proc(t: ^Typechecker, nodes: []Node) -> (err: Error) {
	for &node in nodes {
		// NOTE: ingore any non-definition nodes.
		#partial switch def in node {
		case Def_Func:
			symbol := Symbol_Func {
				id         = def.id,
				name       = def.name,
				signature  = def.signature,
				defined_at = def.name.span,
			}
			symbol_define(t, symbol) or_return
		case Def_Var:
			for pair in def.pairs {
				symbol := Symbol_Var {
					id         = pair.id,
					name       = pair.name,
					type       = pair.type,
					defined_at = pair.name.span,
				}
				symbol_define(t, symbol) or_return
			}
		case Def_Const:
			symbol := Symbol_Const {
				id         = def.id,
				name       = def.name,
				type       = def.type,
				defined_at = def.name.span,
			}
			symbol_define(t, symbol) or_return
		case Def_Data:
			symbol := Symbol_Data {
				id         = def.id,
				name       = def.name,
				defined_at = def.name.span,
			}
			symbol_define(t, symbol) or_return
		case Def_Type_Alias:
			symbol := User_Type_Alias {
				id         = def.id,
				name       = def.name,
				derived    = def.derived,
				defined_at = def.name.span,
			}
			symbol_define(t, Symbol_User_Type(symbol)) or_return
		case Def_Enum:
			symbol := User_Type_Enum {
				id         = def.id,
				name       = def.name,
				derived    = def.derived,
				variants   = make(map[string]Span),
				defined_at = def.name.span,
			}
			for vari in def.variants {
				_, _, found := map_upsert(&symbol.variants, vari.name.s, vari.name.span)
				if found {
					panic("TODO: 'variant names collision' error")
				}
			}
			symbol_define(t, Symbol_User_Type(symbol)) or_return
		case Def_Struct:
			symbol := User_Type_Struct {
				id         = def.id,
				name       = def.name,
				fields     = make(map[string]Struct_Field),
				defined_at = def.name.span,
			}
			for field in def.fields {
				f := Struct_Field {
					type = field.type,
					span = field.name.span,
				}
				_, _, found := map_upsert(&symbol.fields, field.name.s, f)
				if found {
					panic("TODO: 'field names collision' error")
				}
			}
			symbol_define(t, Symbol_User_Type(symbol)) or_return
		}
	}

	return nil
}

@(require_results)
symbol_define :: proc(t: ^Typechecker, symbol: Symbol, loc := #caller_location) -> (err: Error) {
	name := symbol_name(symbol).s
	assert(name != "", "uxnsmal.define_symbol: defining a symbol with an empty name", loc)

	_, _, found := map_upsert(&t.symbols, name, symbol)
	if found {
		panic("TODO: 'symbol redefinition' error")
	}
	return nil
}

symbol_get_user_type :: proc(
	t: ^Typechecker,
	name: string,
	loc := #caller_location,
) -> ^Symbol_User_Type {
	symbol, ok := &t.symbols[name]
	if !ok {
		msg := fmt.tprintf("uxnsmal.symbol_get_user_type: no symbol `%s`", name)
		panic(msg, loc)
	}

	user_type, is_user := &symbol.(Symbol_User_Type)
	if !is_user {
		msg := fmt.tprintf("uxnsmal.symbol_get_user_type: symbol `%s` is not a user type", name)
		panic(msg, loc)
	}

	return user_type
}

@(require_results)
check_nodes :: proc(t: ^Typechecker, nodes: []Node) -> (ok: bool) {
	for &node in nodes {
		check_node(t, &node) or_return
	}
	return true
}

@(require_results)
check_node :: proc(t: ^Typechecker, node_: ^Node) -> (ok: bool) {
	switch &node in node_ {
	case Def_Type_Alias, Def_Struct, Def_Var: // skip

	// NOTE: ignore return values from the definition check functions because
	// if an error happens it doesn't mess up other definitions state, so
	// we can continue checking other definitions.
	case Def_Func:
		_ = check_def_func(t, &node)
	case Def_Const:
		_ = check_def_const(t, &node)
	case Def_Data:
		_ = check_def_data(t, &node)
	case Def_Enum:
		_ = check_def_enum(t, &node)

	case Expr_Byte:
		stack_push(t, &t.ws, make_type(Type_Byte{}), node.span)
	case Expr_Short:
		stack_push(t, &t.ws, make_type(Type_Short{}), node.span)
	case Expr_String:
		// Push `*[]byte`
		base := make_type(Type_Byte{})
		type := make_short_ptr(make_unsized_arr(base))
		stack_push(t, &t.ws, type, node.span)

		panic("TODO: define a data with this string contents.")

	case Expr_Symbol:
		check_expr_symbol(t, &node) or_return
	case Expr_Intr:
		check_expr_intr(t, &node) or_return
	case Expr_Store:
		check_expr_store(t, &node) or_return

	case Expr_Bind:
		check_expr_bind(t, &node) or_return
	case Expr_Expect:
		check_expr_expect(t, &node) or_return

	case Expr_Cast:
		panic("TODO: check Expr_Cast")

	case Expr_If:
		panic("TODO: check Expr_If")
	case Expr_While:
		panic("TODO: check Expr_While")
	case Expr_Break:
		panic("TODO: check Expr_Break")
	}

	return true
}

@(require_results)
check_def_func :: proc(t: ^Typechecker, def: ^Def_Func) -> (ok: bool) {
	checker_reset(t)

	proc_, is_proc := def.signature.kind.(Signature_Proc)
	if is_proc {
		// Push proc function inputs onto the working stack.
		for input in proc_.inputs {
			stack_push(t, &t.ws, input.type, input.name.span, input.name.s)
		}
	}

	check_nodes(t, def.body.nodes[:]) or_return

	// Check outputs.
	if is_proc {
		return check_proc_func_outputs(t, def, proc_)
	} else {
		err_not_empty :: #force_inline proc(t: ^Typechecker, stack: string, name: Name) -> bool {
			// TODO: "vector function have no outputs" help.
			err := problemf(
				name.span,
				"%v stack is not empty at the end of the function `%v`",
				stack,
				name.s,
			)
			stack_notes_caused_by(&t.ws, &err, len(t.ws.items))
			error(t, err)
			return false
		}

		if len(t.ws.items) > 0 {
			return err_not_empty(t, "working", def.name)
		} else if len(t.rs.items) > 0 {
			return err_not_empty(t, "return", def.name)
		}

		return true
	}
}
check_proc_func_outputs :: proc(
	t: ^Typechecker,
	def: ^Def_Func,
	sig: Signature_Proc,
) -> (
	ok: bool,
) {
	// TODO!: "expected stack ..., got stack ..." note.

	// Check stacks length.
	if len(t.ws.items) > len(sig.outputs) {
		err := problemf(def.name.span, "too many outputs for the function `%s`", def.name.s)
		diff := len(t.ws.items) - len(sig.outputs)
		stack_notes_caused_by(&t.ws, &err, diff)
		return error(t, err)
	}
	if len(t.ws.items) < len(sig.outputs) {
		err := problemf(def.name.span, "not enough outputs for the function `%s`", def.name.s)
		// TODO!: "consumed here" note.
		return error(t, err)
	}
	if len(t.rs.items) > 0 {
		err := problemf(
			def.name.span,
			"return stack is not empty at the end of the function `%v`",
			def.name.s,
		)
		stack_notes_caused_by(&t.rs, &err, len(t.rs.items))
		return error(t, err)
	}

	notes := make([dynamic]Note)

	// Check stack item types.
	for &item, idx in t.ws.items {
		output := &sig.outputs[idx]

		if !type_eq_downcasted(t, item.type, output.type) {
			note := notef(
				item.pushed_at,
				"this is `%v`, expected `%v`",
				type_tprint(item.type),
				type_tprint(output.type),
			)
			append(&notes, note)
		}
	}

	if len(notes) > 0 {
		err := problemf(
			def.name.span,
			"invalid types of the outputs for the function `%v`",
			def.name.s,
		)
		err.notes = notes
		return error(t, err)
	}

	return true
}

@(require_results)
check_def_const :: proc(t: ^Typechecker, def: ^Def_Const) -> (ok: bool) {
	checker_reset(t)
	check_nodes(t, def.body.nodes[:]) or_return

	// Check body outputs.
	if len(t.ws.items) != 1 {
		// TODO: show expected and actual working stack signatures.
		err := problemf(
			def.name.span,
			"constants must output exactly 1 value, but the constant `%s` outputs %s",
			def.name.s,
			msg_n_values(len(t.ws.items)),
		)
		stack_notes_caused_by(&t.ws, &err, len(t.ws.items) - 1)
		return error(t, err)
	}
	if len(t.rs.items) != 0 {
		MSG :: "constants can't output values into the return stack, but the constant `%s` outputs %s"
		err := problemf(def.name.span, MSG, def.name.s, msg_n_values(len(t.rs.items)))
		// TODO: should propably point at `sth` operations.
		stack_notes_caused_by(&t.rs, &err, len(t.rs.items))
		return error(t, err)
	}

	// TODO!: would be cool to infer the type of the const.
	output := t.ws.items[0]
	if !type_eq_downcasted(t, output.type, def.type) {
		got_str := type_tprint(output.type)
		expected_str := type_tprint(def.type)
		err := problemf(
			def.name.span,
			"constant `%s` of type `%s` outputs an invalid type `%s`",
			def.name.s,
			expected_str,
			got_str,
		)
		problem_notef(&err, output.pushed_at, "this is `%s`, expected `%s`", got_str, expected_str)
		return error(t, err)
	}

	return true
}

@(require_results)
check_def_data :: proc(t: ^Typechecker, def: ^Def_Data) -> (ok: bool) {
	data := make([dynamic]u8)

	for node in def.body.nodes {
		#partial switch n in node {
		case Expr_Byte:
			append(&data, n.value)
		case Expr_Short:
			append(&data, u8(n.value >> 8))
			append(&data, u8(n.value & 0xff))
		case Expr_String:
			start := len(data)
			non_zero_resize(&data, start + len(n.bytes))
			copy_slice(data[start:], n.bytes[:])
		case:
			// TODO: show data definition example.
			// TODO: show why this is not allowed.
			err := problemf(
				node_span(node),
				"only bytes, shorts and strings are allowed inside `data` definitions",
			)
			return error(t, err)
		}
	}

	return true
}

@(require_results)
check_def_enum :: proc(t: ^Typechecker, def: ^Def_Enum) -> (ok: bool) {
	ok = true
	for vari in def.variants {
		ok &= check_enum_variant(t, def, vari)
	}
	return
}
check_enum_variant :: proc(t: ^Typechecker, def: ^Def_Enum, vari: Enum_Variant) -> (ok: bool) {
	body: Body
	body, ok = vari.body.?
	if !ok do return true

	checker_reset(t)
	check_nodes(t, body.nodes[:]) or_return

	// Check outputs.
	if len(t.ws.items) != 1 {
		// TODO: show expected and actual working stack signatures.
		err := problemf(
			vari.name.span,
			"enum variants must output exactly 1 value, but the variant `%s.%s` outputs %s",
			def.name.s,
			vari.name.s,
			msg_n_values(len(t.ws.items)),
		)
		stack_notes_caused_by(&t.ws, &err, len(t.ws.items) - 1)
		return error(t, err)
	}
	if len(t.rs.items) != 0 {
		err := problemf(
			vari.name.span,
			"enum variants can't output values into the return stack, but the variant `%s.%s` outputs %s",
			def.name.s,
			vari.name.s,
			msg_n_values(len(t.rs.items)),
		)
		// TODO: should propably point at `sth` operations.
		stack_notes_caused_by(&t.rs, &err, len(t.rs.items))
		return error(t, err)
	}

	output := t.ws.items[0]
	if !type_eq_downcasted(t, output.type, def.derived) {
		got_str := type_tprint(output.type)
		expected_str := type_tprint(def.derived)
		// TODO: note that the default type of enums is byte.
		err := problemf(
			vari.name.span,
			"enum variant `%s.%s` of type `%s` outputs an invalid type `%s`",
			def.name.s,
			vari.name.s,
			expected_str,
			got_str,
		)
		problem_notef(&err, output.pushed_at, "this is `%s`, expected `%s`", got_str, expected_str)
		return error(t, err)
	}

	return true
}

@(require_results)
check_expr_symbol :: proc(t: ^Typechecker, expr: ^Expr_Symbol) -> (ok: bool) {
	assert(len(expr.members) >= 1)

	first := expr.members[0]
	accessing_fields := len(expr.members) >= 2

	symbol: ^Symbol
	symbol, ok = &t.symbols[first.name.s]
	if !ok {
		err := problemf(first.name.span, "no symbol `%s` found in this scope", first.name.s)
		return error(t, err)
	}

	switch &s in symbol {
	case Symbol_Var:
		_check_expr_symbol_var(t, expr, &s) or_return

	case Symbol_Func:
		if accessing_fields {
			MSG :: "`%s` is a function, therefore it has no fields"
			err := problemf(expr.span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return error(t, err)
		} else if first.as_array_count > 0 {
			MSG :: "trying to access the function `%s` as an array"
			err := problemf(first.brackets_span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return error(t, err)
		}

		// Taking a pointer to a function.
		if expr.as_ptr {
			type := make_type(Type_Func_Ptr{s.signature})
			stack_push(t, &t.ws, type, expr.span)
			return true
		}

		// Calling a function.
		proc_, is_proc := s.signature.kind.(Signature_Proc)
		if !is_proc {
			// TODO: but why?
			// TODO: how to take a pointer?
			MSG :: "can't call vector functions, may be you wanted to take a pointer?"

			err := problemf(expr.span, MSG)
			problem_notef(&err, s.defined_at, "defined here")
			return error(t, err)
		}

		// Push function outputs onto the working stack.
		for output in proc_.outputs {
			stack_push(t, &t.ws, output.type, expr.span)
		}

	case Symbol_Const:
		if accessing_fields {
			MSG :: "`%s` is a constant, therefore it has no fields"
			err := problemf(expr.span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return error(t, err)
		} else if first.as_array_count > 0 {
			MSG :: "trying to access the constant `%s` as an array"
			err := problemf(first.brackets_span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return error(t, err)
		}

		stack_push(t, &t.ws, s.type, expr.span)

	case Symbol_Data:
		if accessing_fields {
			MSG :: "`%s` is a data, therefore it has no fields"
			err := problemf(expr.span, MSG, s.name.s)
			problem_notef(&err, s.defined_at, "defined here")
			return error(t, err)
		}

		assert(first.as_array_count == 0, "TODO:")

		if !expr.as_ptr && first.as_array_count == 0 {
			// TODO: but why?
			MSG :: "consider taking a pointer or accessing a single byte of the data"
			err := problemf(expr.span, MSG)
			return error(t, err)
		}

		if expr.as_ptr {
			base := make_type(Type_Byte{})
			arr := make_unsized_arr(base)
			stack_push(t, &t.ws, make_short_ptr(arr), expr.span)
		}

	case Symbol_User_Type:
		enum_type, is_enum := s.(User_Type_Enum)
		if !is_enum {
			MSG :: "unexpected use of the user type `%s`"
			err := problemf(expr.span, MSG, symbol_name(symbol^).s)
			problem_notef(&err, symbol_defined_at(symbol^), "defined here")
			return error(t, err)
		}

		if len(expr.members) < 2 {
			// TODO: enum usage example.
			err := problemf(expr.span, "variant must be specified for an enum")
			problem_notef(&err, enum_type.defined_at, "defined here")
			return error(t, err)
		} else if len(expr.members) > 2 {
			err := problemf(expr.span, "unexpected multiple enum variants access")
			problem_notef(&err, enum_type.defined_at, "defined here")
			return error(t, err)
		}

		sec := &expr.members[1]
		_, ok := enum_type.variants[sec.name.s]
		if !ok {
			MSG :: "enum `%s` doesn't have variant `%s`"
			err := problemf(expr.span, MSG, enum_type.name.s, sec.name.s)
			problem_notef(&err, enum_type.defined_at, "defined here")
			return error(t, err)
		}

		stack_push(t, &t.ws, make_type(Type_User{enum_type.name.s}), expr.span)
	}

	return true
}
@(private)
_check_expr_symbol_var :: proc(
	t: ^Typechecker,
	expr: ^Expr_Symbol,
	symbol: ^Symbol_Var,
) -> (
	ok: bool,
) {
	idx := 0
	member := &expr.members[0]
	member_type := &symbol.type
	member_defined_at := symbol.defined_at
	as_array := false

	value_span := expr.members[0].span

	// Resolve field access.
	for {
		if member.as_array_count > 0 && as_array || member.as_array_count >= 2 {
			// TODO: example on how to do that right
			MSG :: "can't access nested arrays like this"
			err := problemf(member.brackets_span, MSG)
			return error(t, err)
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
				return error(t, err)
			}
		}

		// Code below will be executed only when there are more than one member
		// in the symbol expression.
		idx += 1
		if idx >= len(expr.members) {
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
			return error(t, err)
		}

		assert(struct_type != nil)

		// Getting a struct field for the next iteration.
		member = &expr.members[idx]
		value_span.end = member.span.end

		field, found := &struct_type.fields[member.name.s]
		if !found {
			MSG :: "struct type `%s` doesn't have field `%s`"
			err := problemf(member.name.span, MSG, struct_type.name, member.name.s)
			problem_notef(&err, struct_type.defined_at, "defined here")
			return error(t, err)
		}

		member_type = &field.type
		member_defined_at = field.span
	}

	output_type: Type

	#partial switch k in member_type.kind {
	case Type_Array, Type_Unsized_Array:
		// TODO: but why?
		// TODO: show how to load array elements.
		MSG :: "can't simply load a value of an array type `%s`"
		err := problemf(expr.span, MSG, type_tprint(member_type^))
		problem_notef(&err, member_defined_at, "defined here")
		return error(t, err)
	case Type_User:
		user_type := symbol_get_user_type(t, k.name)
		#partial switch type in user_type {
		case User_Type_Alias:
			output_type = type.derived
		case User_Type_Enum:
			output_type = member_type^
		case User_Type_Struct:
			// TODO: but why?
			MSG :: "can't simply load a value of a struct type `%s`"
			err := problemf(expr.span, MSG, type.name.s)
			problem_notef(&err, member_defined_at, "defined here")
			return error(t, err)
		}
	}

	stack_push(t, &t.ws, output_type, expr.span)

	return true
}

@(require_results)
check_expr_store :: proc(t: ^Typechecker, expr: ^Expr_Store) -> (ok: bool) {
	panic("TODO: check_expr_store")
}

@(require_results)
check_expr_bind :: proc(t: ^Typechecker, expr: ^Expr_Bind) -> (ok: bool) {
	n := len(expr.names)
	if len(t.ws.items) < n {
		// TODO: show the working stack signature.
		err := problemf(
			expr.span,
			"trying to name %s, but %s",
			msg_n_values(n),
			msg_there_n_values_on_stack(&t.ws),
		)
		return error(t, err)
	}

	for name, idx in expr.names {
		t.ws.items[len(t.ws.items) - n + idx].name = name.s
	}
	return true
}

@(require_results)
check_expr_expect :: proc(t: ^Typechecker, expr: ^Expr_Expect) -> (ok: bool) {
	n := len(expr.names)

	if len(t.ws.items) < n {
		// TODO: show the working stack signature.
		err := problemf(
			expr.span,
			"expected at least %s, but %s",
			msg_n_values(n),
			msg_there_n_values_on_stack(&t.ws),
		)
		return error(t, err)
	}

	notes := make([dynamic]Note)

	for name, idx in expr.names {
		item := t.ws.items[len(t.ws.items) - n + idx]
		item_name := item_name(item)
		if item_name != name.s {
			// TODO: show a place of the last rename of the item.
			note := notef(item.pushed_at, `name is "%s", expected "%s"`, item_name, name.s)
			append(&notes, note)
		}
	}

	if len(notes) > 0 {
		// TODO: show the expected and actual working stack signatures.
		err := problemf(
			expr.span,
			"%d of %d names are mismatched on the working stack",
			len(notes),
			n,
		)
		err.notes = notes
		return error(t, err)
	}

	return true
}

checker_reset :: proc(t: ^Typechecker) {
	clear(&t.ws.items)
	clear(&t.rs.items)
	t.ws.keep = false
	t.rs.keep = false
}

// Convenience function, pushes a problem and always returns `false`.
@(private)
error :: proc(t: ^Typechecker, problem: Problem) -> (ok: bool) {
	t.errored = true
	append(&t.state.problems, problem)
	return false
}
