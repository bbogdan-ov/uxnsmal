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
	assert(type_valid(item.type), loc = loc)
	assert(span_valid(item.pushed_at), loc = loc)

	line := item.pushed_at.line + 1
	col := item.pushed_at.column + 1
	#partial switch k in item.type.kind {
	case Type_User:
		user_type := symbol_get_user_type(t, k.name)
		_, is_enum := user_type.(User_Type_Enum)
		if !is_enum {
			MSG :: "uxnsmal.stack_push_item: trying to push %T at %d:%d"
			panic(fmt.tprintf(MSG, k, line, col), loc)
		}
	case:
		MSG :: "uxnsmal.stack_push_item: trying to push %T at %d:%d"
		panic(fmt.tprintf(MSG, k, line, col), loc)
	}

	// TODO: warn if the size of a stack exceeds the limit (256 bytes by default).
	append(&s.items, item)
	s.keep_cursor = 0
}

// Tries to push an item onto a stack.
// If type of the items is a struct or an array, an error is returned.
@(require_results)
stack_push_item_safe :: proc(
	t: ^Typechecker,
	s: ^Stack,
	item: Item,
	defined_at := Span{},
	loc := #caller_location,
) -> Error {
	item := item

	#partial switch k in item.type.kind {
	case Type_Array, Type_Unsized_Array:
		// TODO: but why?
		// TODO: show how to load array elements.
		MSG :: "can't simply push a value of an array type `%s` onto a stack"
		err := problemf(item.pushed_at, MSG, type_tprint(item.type))
		if span_valid(defined_at) {
			problem_notef(&err, defined_at, "defined here")
		}
		return err
	case Type_User:
		user_type := symbol_get_user_type(t, k.name)
		#partial switch ty in user_type {
		case User_Type_Enum: // ok
		case User_Type_Alias:
			item.type = ty.derived
		case User_Type_Struct:
			// TODO: but why?
			MSG :: "can't simply push a value of a struct type `%s` onto a stack"
			err := problemf(item.pushed_at, MSG, ty.name.s)
			if span_valid(defined_at) {
				problem_notef(&err, defined_at, "defined here")
			}
			return err
		}
	}

	stack_push_item(t, s, item, loc = loc)
	return nil
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

item_make :: proc(type: Type, pushed_at: Span, name: Maybe(string) = nil) -> Item {
	return Item{type = type, pushed_at = pushed_at, name = name}
}

item_name :: proc(item: Item) -> string {
	name, ok := item.name.?
	if ok {
		return name
	} else {
		return "_"
	}
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
					in_rom     = def.in_rom,
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
			if !type_is_basic(def.derived) {
				MSG :: "enums can only be derived from a `byte` or a `short`, but got `%s`"
				err := problemf(def.name.span, MSG, type_tprint(def.derived))
				problem_notef(&err, def.derived.span, "expected `byte` or `short` here")
				return err
			}

			symbol := User_Type_Enum {
				id         = def.id,
				name       = def.name,
				derived    = def.derived,
				variants   = make(map[string]Span),
				defined_at = def.name.span,
			}
			for vari in def.variants {
				prev, found := symbol.variants[vari.name.s]
				if found {
					MSG :: "variant `%s` already defined inside the enum `%s`"
					err := problemf(vari.name.span, MSG, vari.name.s, def.name.s)
					problem_notef(&err, prev, "previously defined here")
					return err
				}
				map_insert(&symbol.variants, vari.name.s, vari.name.span)
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
				prev, found := symbol.fields[field.name.s]
				if found {
					MSG :: "field `%s` already defined inside the struct `%s`"
					err := problemf(field.name.span, MSG, field.name.s, def.name.s)
					problem_notef(&err, prev.span, "previously defined here")
					return err
				}
				map_insert(&symbol.fields, field.name.s, f)
			}
			symbol_define(t, Symbol_User_Type(symbol)) or_return
		}
	}

	return nil
}

@(require_results)
symbol_define :: proc(t: ^Typechecker, symbol: Symbol, loc := #caller_location) -> (err: Error) {
	name := symbol_name(symbol)
	assert(name.s != "", "uxnsmal.define_symbol: defining a symbol with an empty name", loc)

	prev, found := &t.symbols[name.s]
	if found {
		// TODO: "all symbol share the same name space" help.
		MSG :: "name `%s` is already taken by a %s"
		err := problemf(name.span, MSG, name.s, symbol_kind_str(prev^))
		problem_notef(&err, symbol_defined_at(prev^), "previously defined here")
		return err
	}
	map_insert(&t.symbols, name.s, symbol)
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
		NOTE :: "may be you wanted to take a pointer?"

		// Push proc function inputs onto the working stack.
		for input in proc_.inputs {
			item := item_make(input.type, input.name.span, input.name.s)
			err := stack_push_item_safe(t, &t.ws, item)
			if problem, erred := err.?; erred {
				// TODO: how to do that?
				problem_notef(&problem, input.type.span, NOTE)
				return error(t, problem)
			}
		}

		// Validate outputs.
		for output in proc_.outputs {
			#partial block: switch k in output.type.kind {
			case Type_Array, Type_Unsized_Array:
				// TODO: but why?
				MSG :: "as arrays can't be pushed onto a stack, it is impossible to have such output"
				err := problemf(output.name.span, MSG)
				// TODO: how to do that?
				problem_notef(&err, output.type.span, NOTE)
				return error(t, err)
			case Type_User:
				user_type := symbol_get_user_type(t, k.name)
				// TODO!!!: i need to do something with type alises.
				_, is_enum := user_type.(User_Type_Enum)
				if is_enum do break block

				// TODO: but why?
				MSG :: "as structs can't be pushed onto a stack, it is impossible to have such output"
				err := problemf(output.name.span, MSG)
				// TODO: how to do that?
				problem_notef(&err, output.type.span, NOTE)
				return error(t, err)
			}
		}
	}

	check_nodes(t, def.body.nodes[:]) or_return

	// Check outputs.
	if is_proc {
		return _check_proc_func_outputs(t, def, proc_)
	} else {
		err_not_empty :: #force_inline proc(t: ^Typechecker, stack: string, name: Name) -> bool {
			// TODO: but why?
			err := problemf(
				name.span,
				"%s stack is not empty at the end of the function `%s`",
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
@(private, require_results)
_check_proc_func_outputs :: proc(
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
			"return stack is not empty at the end of the function `%s`",
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
				"this is `%s`, expected `%s`",
				type_tprint(item.type),
				type_tprint(output.type),
			)
			append(&notes, note)
		}
	}

	if len(notes) > 0 {
		err := problemf(
			def.name.span,
			"invalid types of the outputs for the function `%s`",
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

	resolved := symbol_resolve_members(t, expr.members[:], expr.span) or_return

	switch &s in resolved.symbol {
	case Symbol_Var:
		type: Type

		if s.in_rom && expr.as_ptr {
			type = make_short_ptr(resolved.type)
		} else if expr.as_ptr {
			type = make_byte_ptr(resolved.type)
		} else {
			type = resolved.type
		}

		if resolved.as_array {
			_check_array_access(t, type, s.in_rom, expr.span) or_return
		} else {
			item := item_make(type, expr.span)
			err := stack_push_item_safe(t, &t.ws, item, resolved.defined_at)
			maybe_error(t, err) or_return
		}
		return true

	case Symbol_Data:
		item: Item

		if expr.as_ptr && resolved.as_array {
			base := make_type(Type_Byte{})
			item = item_make(make_short_ptr(base), expr.span)
		} else if expr.as_ptr {
			base := make_type(Type_Byte{})
			arr := make_unsized_arr(base)
			item = item_make(make_short_ptr(arr), expr.span)
		} else if resolved.as_array {
			item = item_make(make_type(Type_Byte{}), expr.span)
		} else {
			// TODO: but why?
			MSG :: "consider taking a pointer or accessing a single byte of the data"
			err := problemf(expr.span, MSG)
			return error(t, err)
		}

		panic("TODO: array access")

	case Symbol_Const:
		assert(!resolved.as_array)
		assert(len(expr.members) == 1)

		if expr.as_ptr {
			// TODO: but why?
			err := problemf(expr.span, "can't take a pointer to a constant")
			problem_notef(&err, s.defined_at, "defined here")
			return error(t, err)
		}

		stack_push(t, &t.ws, resolved.type, expr.span)
		return true

	case Symbol_User_Type:
		assert(!resolved.as_array)
		assert(len(expr.members) == 2)

		if expr.as_ptr {
			// TODO: but why?
			err := problemf(expr.span, "can't take a pointer to an enum")
			problem_notef(&err, symbol_defined_at(resolved.symbol^), "defined here")
			return error(t, err)
		}

		stack_push(t, &t.ws, resolved.type, expr.span)
		return true

	case Symbol_Func:
		assert(!resolved.as_array)
		assert(len(expr.members) == 1)

		// Taking a pointer to a function.
		if expr.as_ptr {
			type := make_type(Type_Func_Ptr{s.signature})
			stack_push(t, &t.ws, type, expr.span)
			return true
		} else {
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
			return true
		}

	case:
		unreachable()
	}
}
@(private, require_results)
_check_array_access :: proc(
	t: ^Typechecker,
	type: Type,
	short_addr: bool,
	span: Span,
) -> (
	ok: bool,
) {
	// TODO: array access example on error.
	// TODO: why is the index of this exact type (byte or short)?

	index_name := "byte"
	if short_addr do index_name = "short"

	if len(t.ws.items) < 1 {
		MSG :: "expected a `%s` index on the working stack, but got nothing"
		err := problemf(span, MSG, index_name)
		return error(t, err)
	}

	index := stack_pop(&t.ws)
	_, is_byte := index.type.kind.(Type_Byte)
	_, is_short := index.type.kind.(Type_Short)
	if is_byte != !short_addr || is_short != short_addr {
		MSG :: "index must be a `%s`, but got a `%s` on the working stack"

		idx_str := type_tprint(index.type)
		err := problemf(span, MSG, index_name, idx_str)
		problem_notef(&err, index.pushed_at, "this is `%s`, expected `%s`", idx_str, index_name)
		return error(t, err)
	}

	item := item_make(type, span)
	// TODO: "base type of the array ..." note on error.
	err := stack_push_item_safe(t, &t.ws, item)
	if problem, ok := err.?; ok {
		MSG :: "base type is `%s`"
		problem_notef(&problem, item.pushed_at, MSG, type_tprint(item.type))
		return error(t, problem)
	}
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
maybe_error :: proc(t: ^Typechecker, err: Error) -> (ok: bool) {
	if problem, errored := err.(Problem); errored {
		return error(t, problem)
	} else {
		return true
	}
}
