#+vet explicit-allocators

package uxnsmal

import "base:runtime"
import "core:slice"
import "core:math"

Typechecker :: struct {
	state:          ^State,
	errored:        bool,
	// Working stack.
	ws:             Stack,
	// Return stack.
	rs:             Stack,
	temp_arena:     runtime.Arena,
	// Temporary allocator for objects with life-time within a global
	// definition body.
	temp_allocator: runtime.Allocator,
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

// Push an item on top of a stack.
stack_push_item :: proc(t: ^Typechecker, s: ^Stack, item: Item, loc := #caller_location) {
	assert(span_valid(item.pushed_at), loc = loc)

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
stack_pop_safe :: proc(s: ^Stack) -> (item: Item, found: bool) {
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

// Pops and returns the top-most (last) item on a stack.
// Panics if the stack is empty.
@(require_results)
stack_pop :: proc(s: ^Stack, loc := #caller_location) -> Item {
	item, found := stack_pop_safe(s)
	assert(found, "stack is empty", loc)
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
	case:
		unreachable()
	}
}

item_make :: proc(type: Type, pushed_at: Span, name: Maybe(string) = nil) -> Item {
	return Item{type = type, pushed_at = pushed_at, name = name}
}

item_name :: proc(item: Item) -> string {
	name, found := item.name.?
	if found {
		return name
	} else {
		return "_"
	}
}

// Initializes a `Typechecker` and prerforms type-checking on an AST.
@(require_results)
typecheck :: proc(state: ^State) -> (ok: bool) {
	t: Typechecker
	t.state = state
	t.ws.kind = .Working
	t.rs.kind = .Return
	t.ws.items = make([dynamic]Item, state.allocator)
	t.rs.items = make([dynamic]Item, state.allocator)

	t.temp_allocator = runtime.arena_allocator(&t.temp_arena)
	defer {
		free_all(t.temp_allocator)
		runtime.arena_destroy(&t.temp_arena)
	}

	// Check top-level nodes.
	err := check_nodes(&t, state.nodes[:], true)
	maybe_error(&t, err) or_return

	return !t.errored
}

@(require_results)
check_nodes :: proc(t: ^Typechecker, nodes: []Node, toplevel := false) -> (err: Error) {
	for &node in nodes {
		check_node(t, &node, toplevel) or_return
	}
	return nil
}

@(require_results)
check_node :: proc(t: ^Typechecker, node_: ^Node, toplevel := false) -> (err: Error) {
	defer if toplevel do free_all(t.temp_allocator)

	switch &node in node_ {
	case Def_Alias, Def_Struct, Def_Var:
		// skip
		return nil

	// NOTE: ignore or consume return values from the definition check
	// functions because if an error happens it doesn't mess up other
	// definitions state, so we can continue checking other definitions
	// or/and expressions.
	case Def_Func:
		if !toplevel do panic("TODO: 'no local definitions yet' error")

		err := check_def_func(t, &node)
		maybe_error(t, err)
		return nil
	case Def_Const:
		if !toplevel do panic("TODO: 'no local definitions yet' error")

		err := check_def_const(t, &node)
		maybe_error(t, err)
		return nil
	case Def_Data:
		if !toplevel do panic("TODO: 'no local definitions yet' error")

		_ = check_def_data(t, &node)
		return nil
	case Def_Enum:
		if !toplevel do panic("TODO: 'no local definitions yet' error")

		_ = check_def_enum(t, &node)
		return nil

	case Expr_Byte:
		stack_push(t, &t.ws, Type_Byte{}, node.span)
		return nil
	case Expr_Short:
		stack_push(t, &t.ws, Type_Short{}, node.span)
		return nil
	case Expr_String:
		// Push `*[]byte`
		// TODO!!: refactor to a helper function.
		base := Complex_Type(Type(Type_Byte{}))
		arr := Complex_Type(Type_Unsized_Array{new_clone(base, t.state.allocator)})
		type := Type_Short_Ptr{new_clone(arr, t.state.allocator)}
		stack_push(t, &t.ws, type, node.span)

		panic("TODO: define a data with this string contents.")

	case Expr_Symbol:
		return check_expr_symbol(t, &node)
	case Expr_Intr:
		return check_expr_intr(t, &node)
	case Expr_Store:
		return check_expr_store(t, &node)

	case Expr_Bind:
		return check_expr_bind(t, &node)
	case Expr_Expect:
		return check_expr_expect(t, &node)
	case Expr_Cast:
		return check_expr_cast(t, &node)

	case Expr_Block:
		panic("TODO: check Expr_Block")
	case Expr_If:
		return check_expr_if(t, &node)
	case Expr_While:
		panic("TODO: check Expr_While")
	case Expr_Break:
		panic("TODO: check Expr_Break")

	case:
		unreachable()
	}
}

@(require_results)
check_def_func :: proc(t: ^Typechecker, def: ^Def_Func) -> (err: Error) {
	checker_reset(t)

	proc_, is_proc := def.signature.kind.(Signature_Proc)
	if is_proc {
		// Push proc function inputs onto the working stack.
		for input in proc_.inputs {
			item := item_make(input.type.x, input.name.span, input.name.s)
			stack_push_item(t, &t.ws, item)
		}
	}

	check_nodes(t, def.body.nodes[:]) or_return

	// Check outputs.
	if is_proc {
		return _check_proc_func_outputs(t, def, proc_)
	} else {
		err_not_empty :: #force_inline proc(
			t: ^Typechecker,
			stack: string,
			name: Name,
		) -> Problem {
			// TODO: but why?
			MSG :: "%s stack is not empty at the end of the function `%s`"
			err := problemf(name.span, MSG, stack, name.s)
			stack_notes_caused_by(&t.ws, &err, len(t.ws.items))
			return err
		}

		if len(t.ws.items) > 0 {
			return err_not_empty(t, "working", def.name)
		} else if len(t.rs.items) > 0 {
			return err_not_empty(t, "return", def.name)
		}

		return nil
	}
}
@(private, require_results)
_check_proc_func_outputs :: proc(t: ^Typechecker, def: ^Def_Func, sig: Signature_Proc) -> Error {
	// TODO!: "expected stack ..., got stack ..." note.

	// Check stacks length.
	if len(t.ws.items) > len(sig.outputs) {
		err := problemf(def.name.span, "too many outputs for the function `%s`", def.name.s)
		diff := len(t.ws.items) - len(sig.outputs)
		stack_notes_caused_by(&t.ws, &err, diff)
		return err
	}
	if len(t.ws.items) < len(sig.outputs) {
		// TODO!: "consumed here" note.
		return problemf(def.name.span, "not enough outputs for the function `%s`", def.name.s)
	}
	if len(t.rs.items) > 0 {
		err := problemf(
			def.name.span,
			"return stack is not empty at the end of the function `%s`",
			def.name.s,
		)
		stack_notes_caused_by(&t.rs, &err, len(t.rs.items))
		return err
	}

	notes := make([dynamic]Note, t.state.allocator)

	// Check stack item types.
	for item, idx in t.ws.items {
		output := &sig.outputs[idx]
		expect := output.type.x
		if !type_eq(expect, item.type) && !type_eq(expect, type_downcast(item.type)) {
			note := notef(
				item.pushed_at,
				"this is `%s`, expected `%s`",
				type_tprint(item.type),
				type_tprint(output.type.x),
			)
			append(&notes, note)
		}
	}

	if len(notes) > 0 {
		err := problemf(
			def.name.span,
			"invalid types of outputs for the function `%s`",
			def.name.s,
		)
		err.notes = notes
		return err
	}

	return nil
}

@(require_results)
check_def_const :: proc(t: ^Typechecker, def: ^Def_Const) -> (err: Error) {
	checker_reset(t)
	check_nodes(t, def.body.nodes[:]) or_return

	symbol := def.symbol

	// Check body outputs.
	if len(t.ws.items) != 1 {
		MSG :: "constants must output exactly 1 value, but the constant `%s` outputs %s"

		// TODO: show expected and actual working stack signatures.
		err := problemf(symbol.name.span, MSG, symbol.name.s, msg_n_values(len(t.ws.items)))
		stack_notes_caused_by(&t.ws, &err, len(t.ws.items) - 1)
		return err
	}
	if len(t.rs.items) != 0 {
		MSG :: "constants can't output values into the return stack, but the constant `%s` outputs %s"
		err := problemf(symbol.name.span, MSG, symbol.name.s, msg_n_values(len(t.rs.items)))
		// TODO: should propably point at `sth` operations.
		stack_notes_caused_by(&t.rs, &err, len(t.rs.items))
		return err
	}

	// TODO!: would be cool to infer the type of the const.
	item := t.ws.items[0]
	expect := symbol.type
	if !type_eq(expect, item.type) && !type_eq(expect, type_downcast(item.type)) {
		MSG :: "constant `%s` of type `%s` outputs an invalid value of type `%s`"

		got_str := type_tprint(item.type)
		expected_str := type_tprint(symbol.type)
		err := problemf(symbol.name.span, MSG, symbol.name.s, expected_str, got_str)
		problem_notef(&err, item.pushed_at, "this is `%s`, expected `%s`", got_str, expected_str)
		return err
	}

	return nil
}

@(require_results)
check_def_data :: proc(t: ^Typechecker, def: ^Def_Data) -> (ok: bool) {
	data := make([dynamic]u8, t.state.allocator)
	errored := false

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
			MSG :: "only bytes, shorts and strings are allowed inside `data` definitions"
			err := problemf(node_span(node), MSG)
			error(t, err)
			errored = true
		// continue checking...
		}
	}

	return errored
}

@(require_results)
check_def_enum :: proc(t: ^Typechecker, def: ^Def_Enum) -> (ok: bool) {
	ok = true
	for _, vari in def.symbol.variants {
		ok &= check_enum_variant(t, def, vari)
	}
	return
}
check_enum_variant :: proc(t: ^Typechecker, def: ^Def_Enum, vari: Enum_Variant) -> (ok: bool) {
	body: Body
	body, ok = vari.body.?
	if !ok do return true

	symbol := def.symbol

	checker_reset(t)
	err := check_nodes(t, body.nodes[:])
	maybe_error(t, err) or_return

	// Check outputs.
	if len(t.ws.items) != 1 {
		// TODO: show expected and actual working stack signatures.
		err := problemf(
			vari.name.span,
			"enum variants must output exactly 1 value, but the variant `%s.%s` outputs %s",
			symbol.name.s,
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
			symbol.name.s,
			vari.name.s,
			msg_n_values(len(t.rs.items)),
		)
		// TODO: should propably point at `sth` operations.
		stack_notes_caused_by(&t.rs, &err, len(t.rs.items))
		return error(t, err)
	}

	item := t.ws.items[0]
	expect := symbol.derived
	if !type_eq(expect, item.type) && !type_eq(expect, type_downcast(item.type)) {
		MSG :: "enum variant `%s.%s` of type `%s` outputs an invalid value of type `%s`"

		got_str := type_tprint(item.type)
		expected_str := type_tprint(symbol.derived)
		err := problemf(vari.name.span, MSG, symbol.name.s, vari.name.s, expected_str, got_str)
		problem_notef(&err, item.pushed_at, "this is `%s`, expected `%s`", got_str, expected_str)
		return error(t, err)
	}

	return true
}

@(require_results)
check_expr_symbol :: proc(t: ^Typechecker, expr: ^Expr_Symbol) -> (err: Error) {
	assert(len(expr.members) >= 1)

	resolved := symbol_resolve_members(t.state, expr.members[:], expr.span) or_return

	switch s in resolved.symbol {
	case ^Symbol_Alias, ^Symbol_Struct:
		panic("`symbol_resolve_members` should've handled this symbol")

	case ^Symbol_Var:
		complex: Complex_Type
		if s.in_rom && expr.as_ptr {
			complex = type_make_short_ptr(resolved.type, t.state.allocator)
		} else if expr.as_ptr {
			complex = type_make_byte_ptr(resolved.type, t.state.allocator)
		} else {
			complex = resolved.type
		}

		if resolved.as_array {
			_check_array_access(t, complex, s.in_rom, expr.span) or_return
		} else {
			type := to_stack_type(complex, expr.span) or_return
			item := item_make(type, expr.span)
			stack_push_item(t, &t.ws, item)
		}
		return nil

	case ^Symbol_Data:
		type: Type

		if expr.as_ptr && resolved.as_array {
			// `*byte`
			base := type_make_complex(Type_Byte{})
			type = Type_Short_Ptr{new_clone(base, t.state.allocator)}
		} else if expr.as_ptr {
			// `*[]byte`
			base := type_make_complex(Type_Byte{})
			arr := Complex_Type(Type_Unsized_Array{new_clone(base, t.state.allocator)})
			type = Type_Short_Ptr{new_clone(arr, t.state.allocator)}
		} else if resolved.as_array {
			// `byte`
			type = Type_Byte{}
		} else {
			// TODO: but why and how?
			MSG :: "consider either taking a pointer or accessing a single byte of the data"
			return problemf(expr.span, MSG)
		}

		if resolved.as_array {
			_check_array_access(t, type, true, expr.span) or_return
		} else {
			stack_push(t, &t.ws, type, expr.span)
		}
		return nil

	case ^Symbol_Const:
		assert(!resolved.as_array)
		assert(len(expr.members) == 1)

		if expr.as_ptr {
			// TODO: but why?
			err := problemf(expr.span, "can't take a pointer to a constant")
			problem_notef(&err, s.defined_at, "defined here")
			return err
		}

		type := resolved.type.(Type) // assert
		stack_push(t, &t.ws, type, expr.span)
		return nil

	case ^Symbol_Enum:
		assert(!resolved.as_array)

		if expr.as_ptr {
			// TODO: but why?
			err := problemf(expr.span, "can't take a pointer to an enum")
			problem_notef(&err, s.defined_at, "defined here")
			return err
		}

		type := resolved.type.(Type) // assert
		stack_push(t, &t.ws, type, expr.span)
		return nil

	case ^Symbol_Func:
		assert(!resolved.as_array)
		assert(len(expr.members) == 1)

		// Taking a pointer to a function.
		if expr.as_ptr {
			type := Type_Func_Ptr{s.signature}
			stack_push(t, &t.ws, type, expr.span)
			return nil
		} else {
			// Calling a function.
			proc_, is_proc := s.signature.kind.(Signature_Proc)
			if !is_proc {
				// TODO: but why?
				// TODO: how to take a pointer?
				MSG :: "can't call vector functions, may be you wanted to take a pointer?"

				err := problemf(expr.span, MSG)
				problem_notef(&err, s.defined_at, "defined here")
				return err
			}

			// Push function outputs onto the working stack.
			for output in proc_.outputs {
				stack_push(t, &t.ws, output.type.x, expr.span)
			}
			return nil
		}

	case:
		unreachable()
	}
}
@(private, require_results)
_check_array_access :: proc(
	t: ^Typechecker,
	complex: Complex_Type,
	short_addr: bool,
	span: Span,
) -> Error {
	// TODO: array access example on error.
	_ = _pop_index(t, short_addr, span) or_return

	type := to_stack_type(complex, span) or_return
	item := item_make(type, span)
	stack_push_item(t, &t.ws, item)
	return nil
}
@(private, require_results)
_pop_index :: proc(t: ^Typechecker, short_addr: bool, span: Span) -> (item: Item, err: Error) {
	// TODO: why is the index of this exact type (byte or short)?

	index_name := "byte"
	if short_addr do index_name = "short"

	if len(t.ws.items) < 1 {
		// TODO: show the expected and the actual stacks.
		MSG :: "expected a `%s` index on the working stack, but got nothing"
		err := problemf(span, MSG, index_name)
		return {}, err
	}

	item = stack_pop(&t.ws)
	_, is_byte := item.type.(Type_Byte)
	_, is_short := item.type.(Type_Short)
	if is_byte != !short_addr || is_short != short_addr {
		// TODO: show the expected and the actual stacks.
		MSG :: "index must be a `%s`, but got a `%s` on the working stack"

		idx_str := type_tprint(item.type)
		err := problemf(span, MSG, index_name, idx_str)
		problem_notef(&err, item.pushed_at, "this is `%s`, expected `%s`", idx_str, index_name)
		return {}, err
	}

	return item, nil
}

@(require_results)
check_expr_store :: proc(t: ^Typechecker, expr: ^Expr_Store) -> (err: Error) {
	assert(!expr.symbol.as_ptr)

	resolved := symbol_resolve_members(t.state, expr.symbol.members[:], expr.symbol.span) or_return

	expect: Type
	short_addr := false
	is_data := false

	#partial switch s in resolved.symbol {
	case ^Symbol_Var:
		expect = to_store_type(resolved.type, expr.symbol.span) or_return
		short_addr = s.in_rom
	case ^Symbol_Data:
		if !resolved.as_array {
			// TODO: but why?
			err := problemf(expr.symbol.span, "consider storing a single byte")
			problem_notef(&err, expr.symbol.span, "try prepending `[]` after the name")
			return err
		}

		expect = Type_Byte{}
		short_addr = true
		is_data = true
	case:
		MSG :: "can't store into a %s, expected either a variable or a data"
		err := problemf(expr.symbol.span, MSG, symbol_kind_str(resolved.symbol))
		problem_notef(&err, symbol_defined_at(resolved.symbol), "defined here")
		return err
	}

	if resolved.as_array {
		if len(t.ws.items) < 2 {
			// TODO: show the expected and the actual stacks.
			// TODO: show store syntax example
			MSG :: "expected a value and an index on the working stack, but got %s"
			err := problemf(expr.span, MSG, msg_n_values(len(t.ws.items)))
			return err
		}

		_ = _pop_index(t, short_addr, expr.span) or_return
	} else {
		if len(t.ws.items) < 1 {
			// TODO: show the expected and the actual stacks.
			// TODO: show store syntax example
			MSG :: "expected a `%s` value on the working stack, but got nothing"
			err := problemf(expr.span, MSG, type_tprint(expect))
			return err
		}
	}

	value := stack_pop(&t.ws)
	if !type_eq(expect, value.type) && !type_eq(expect, type_downcast(value.type)) {
		// TODO: show the expected and the actual stacks.
		// TODO: but why?
		msg := "expected a `%s` on the working stack, the given `%s` can't be stored into the %s `%s`"

		value_str := type_tprint(value.type)
		expect_str := type_tprint(expect)
		err := problemf(
			expr.span,
			msg,
			expect_str,
			value_str,
			symbol_kind_str(resolved.symbol),
			symbol_name(resolved.symbol),
		)
		problem_notef(&err, value.pushed_at, "this is `%s`, expected `%s`", expect_str, value_str)
		return err
	}

	return nil
}

@(require_results)
check_expr_bind :: proc(t: ^Typechecker, expr: ^Expr_Bind) -> (err: Error) {
	n := len(expr.names)
	if len(t.ws.items) < n {
		// TODO: show the working stack signature.
		return problemf(
			expr.span,
			"trying to name %s, but %s",
			msg_n_values(n),
			msg_there_n_values_on_stack(&t.ws),
		)
	}

	for name, idx in expr.names {
		t.ws.items[len(t.ws.items) - n + idx].name = name.s
	}

	return nil
}

@(require_results)
check_expr_expect :: proc(t: ^Typechecker, expr: ^Expr_Expect) -> (err: Error) {
	n := len(expr.names)

	if len(t.ws.items) < n {
		// TODO: show the working stack signature.
		return problemf(
			expr.span,
			"expected at least %s, but %s",
			msg_n_values(n),
			msg_there_n_values_on_stack(&t.ws),
		)
	}

	notes := make([dynamic]Note, t.state.allocator)

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
		return err
	}

	return nil
}

@(require_results)
check_expr_cast :: proc(t: ^Typechecker, expr: ^Expr_Cast) -> (err: Error) {
	count := len(t.ws.items)
	if count > len(expr.types) && !expr.force {
		// TODO: show size of the casting and actual stacks.
		MSG :: "you are trying to cast %s into %d, is this what you want?"
		err := problemf(expr.span, MSG, msg_n_values(count), len(expr.types))
		// TODO: why it is like that?
		problem_notef(
			&err,
			expr.keyword_span,
			"...if it is, try appending `!` after the keyword `as`",
		)
		return err
	}

	stack_size: u32 = 0
	cast_size: u32 = 0
	left_bytes: u32 = 0
	for type in expr.types {
		cast_size += type_size(type.x)
	}

	last_item: Item
	left_bytes = cast_size
	for left_bytes > 0 {
		found: bool
		last_item, found = stack_pop_safe(&t.ws)
		if !found {
			// TODO: show size of the casting and actual stacks.
			// TODO: how casting works?
			MSG :: "not enough bytes no the working stack to cast %s, got %s"
			return problemf(expr.span, MSG, msg_n_bytes(cast_size), msg_n_bytes(stack_size))
		}

		item_size := type_size(last_item.type)
		stack_size += item_size

		if item_size > left_bytes do break

		left_bytes -= item_size
	}

	if left_bytes > 0 {
		// TODO: show size of the casting and actual stacks.
		// TODO: but why should i handle everything?
		MSG :: "%d of %s are unhandled while casting"
		err := problemf(expr.span, MSG, left_bytes, msg_n_bytes(stack_size))
		problem_notef(&err, last_item.pushed_at, "size is %d", type_size(last_item.type))
		return err
	}

	// Push casted types onto the working stack.
	for type in expr.types {
		stack_push(t, &t.ws, type.x, type.span)
	}

	return nil
}

@(require_results)
check_expr_if :: proc(t: ^Typechecker, expr: ^Expr_If) -> (err: Error) {
	allocr := t.state.allocator
	span := expr.if_block.keyword_span

	@(require_results)
	check_stack_len :: proc(s: ^Stack, expect: int, span: Span) -> Error {
		// TODO: why is this bad?
		// TODO: show expected and actual stack.
		diff := math.abs(len(s.items) - expect)
		if len(s.items) < expect {
			MSG :: "this conditional block disbalances the %s stack by consuming %s"
			err := problemf(span, MSG, stack_name(s.kind), msg_n_values(diff))
			// TODO: "consumed by" notes.
			return err
		} else if len(s.items) > expect {
			MSG :: "this conditional block disbalances the %s stack by spitting %s"
			err := problemf(span, MSG, stack_name(s.kind), msg_n_values(diff))
			stack_notes_caused_by(s, &err, diff)
			return err
		}
		return nil
	}
	@(require_results)
	check_stack_signature :: proc(
		s: ^Stack,
		expect: []Item,
		span: Span,
		allocator := context.allocator
	) -> Error {
		assert(len(s.items) == len(expect))

		context.allocator = allocator
		notes := make([dynamic]Note, allocator)

		for i in 0 ..< len(s.items) {
			if !type_eq(s.items[i].type, expect[i].type) {
				MSG :: "this is `%s`, expected `%s`"
				type_str := type_tprint(s.items[i].type)
				expect_str := type_tprint(expect[i].type)
				note := notef(s.items[i].pushed_at, MSG, type_str, expect_str)
				append(&notes, note)
			} else if s.items[i].name != expect[i].name {
				MSG :: `name is "%s", expected "%s"`
				note := notef(s.items[i].pushed_at, MSG, item_name(s.items[i]), item_name(expect[i]))
				append(&notes, note)
			}
		}
		
		if len(notes) > 0 {
			// TODO: why is this bad?
			// TODO: show expected and actual stacks.
			MSG :: "this conditional block alters signature of the %s stack"
			err := problemf(span, MSG, stack_name(s.kind))
			err.notes = notes
			return err
		}
		return nil
	}
	@(require_results)
	check_stack :: #force_inline proc(s: ^Stack, expect: []Item, span: Span, allocator := context.allocator) -> Error {
		check_stack_len(s, len(expect), span) or_return
		check_stack_signature(s, expect, span, allocator) or_return
		return nil
	}
	@(require_results)
	check_stacks :: #force_inline proc(
		t: ^Typechecker,
		ws_expect,
		rs_expect: []Item,
		span: Span,
		allocator := context.allocator
	) -> Error {
		check_stack(&t.ws, ws_expect[:], span, allocator) or_return
		check_stack(&t.rs, rs_expect[:], span, allocator) or_return
		return nil
	}

	// Check a condition byte.
	cond, found := stack_pop_safe(&t.ws)
	if !found {
		return problemf(span, "expected a `byte` condition on the working stack, but got nothing")
	}
	_, is_byte := cond.type.(Type_Byte)
	if !is_byte {
		// TODO: suggest comparing values.
		MSG :: "condition must be a `byte`, but got a `%s`"
		type_str := type_tprint(cond.type)
		err := problemf(span, MSG, type_str)
		problem_notef(&err, cond.pushed_at, "this is `%s`, expected `byte`", type_str)
		return err
	}

	if_block := expr.if_block
	else_block, has_else := expr.else_block.?

	if_span := if_block.body.end
	else_span := else_block.body.end

	if has_else {
		// `if {} else {}`
		// `if {} elif... {} else {}`
		ws_before, rs_before := checker_save_stacks(t)

		check_nodes(t, if_block.body.nodes[:]) or_return

		ws_expect, rs_expect := checker_save_stacks(t)
		checker_restore_stacks(t, ws_before[:], rs_before[:])

		// Check the `elif` blocks.
		for elif_block in expr.elif_blocks {
			check_nodes(t, elif_block.body.nodes[:]) or_return
			check_stacks(t, ws_expect[:], rs_expect[:], elif_block.body.end, allocr) or_return

			checker_restore_stacks(t, ws_before[:], rs_before[:])
		}

		// Check the `else` block.
		check_nodes(t, else_block.body.nodes[:]) or_return
		check_stacks(t, ws_expect[:], rs_expect[:], else_span, allocr) or_return
	} else {
		// `if {}`
		// `if {} elif... {}`
		ws_before, rs_before := checker_save_stacks(t)

		// Check the `if` block.
		check_nodes(t, if_block.body.nodes[:]) or_return
		check_stacks(t, ws_before[:], rs_before[:], if_span, allocr) or_return

		// Check the `elif` blocks.
		for elif_block in expr.elif_blocks {
			checker_restore_stacks(t, ws_before[:], rs_before[:])

			check_nodes(t, elif_block.body.nodes[:]) or_return
			check_stacks(t, ws_before[:], rs_before[:], elif_block.body.end, allocr) or_return
		}
	}

	return nil
}

// Clone list of items of the working and the return stacks into
// the `Typechecker.temp_allocator`.
checker_save_stacks :: proc(t: ^Typechecker) -> (ws: [dynamic]Item, rs: [dynamic]Item) {
	ws = slice.to_dynamic(t.ws.items[:], t.temp_allocator)
	rs = slice.to_dynamic(t.rs.items[:], t.temp_allocator)
	return
}

checker_restore_stacks :: proc(t: ^Typechecker, ws: []Item, rs: []Item) {
	resize(&t.ws.items, len(ws))
	resize(&t.rs.items, len(rs))
	copy(t.ws.items[:], ws[:])
	copy(t.rs.items[:], rs[:])
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
