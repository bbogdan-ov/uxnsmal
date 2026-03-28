package uxnsmal

Typechecker :: struct {
	state:   ^State,
	symbols: map[string]Symbol,
	// Working stack.
	ws:      Stack,
	// Return stack.
	rs:      Stack,
}

// Stack item.
Item :: struct #all_or_none {
	type:      Type,
	name:      Maybe(string),
	pushed_at: Span,
}
Stack :: struct {
	items:       [dynamic]Item,
	keep:        bool,
	keep_cursor: int,
}

stack_push :: proc(s: ^Stack, type: Type, pushed_at: Span, name: Maybe(string) = nil) {
	item := Item{type, name, pushed_at}
	// TODO: warn if the size of a stack exceeds the limit (256 bytes by default).
	append(&s.items, item)
	s.keep_cursor = 0
}
stack_pop :: proc(s: ^Stack) -> (item: Item, ok: bool) {
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
// Get a slice of the last N items in a stack.
stack_last :: proc(s: ^Stack, n: int) -> []Item {
	l := len(s.items)
	return s.items[l - n:]
}
stack_notes_caused_by :: proc(s: ^Stack, p: ^Problem, n: int) {
	caused := stack_last(s, n)
	for i in 1 ..= n {
		// TODO: "spits N items" note on function and intrinsic calls.
		problem_notef(p, caused[n - i].pushed_at, "caused by this")
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
	id:        ID,
	name:      Name,
	signature: Signature,
}
Symbol_Var :: struct #all_or_none {
	id:   ID,
	name: Name,
	type: Type,
}
Symbol_Const :: struct #all_or_none {
	id:   ID,
	name: Name,
	type: Type,
}
Symbol_Data :: struct #all_or_none {
	id:   ID,
	name: Name,
}

Symbol_User_Type :: union #no_nil {
	User_Type_Alias,
	User_Type_Enum,
	User_Type_Struct,
}
User_Type_Alias :: struct #all_or_none {
	id:   ID,
	name: Name,
	base: Type,
}
User_Type_Enum :: struct #all_or_none {
	id:       ID,
	name:     Name,
	variants: map[string]Span,
}
User_Type_Struct :: struct #all_or_none {
	id:     ID,
	name:   Name,
	fields: map[string]Struct_Field,
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

// Initializes a `Typechecker` and prerforms type-checking on an AST.
@(require_results)
typecheck :: proc(state: ^State) -> (ok: bool) {
	context.allocator = state.allocator

	t: Typechecker
	t.state = state
	t.symbols = make(map[string]Symbol)
	t.ws.items = make([dynamic]Item)
	t.rs.items = make([dynamic]Item)

	// Collect symbols.
	err := collect(&t, state.nodes[:])
	if problem, ok := err.(Problem); ok {
		append(&state.problems, problem)
		return false
	}

	// Check top-level nodes.
	check_nodes(&t, state.nodes[:]) or_return

	return true
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
				id        = def.id,
				name      = def.name,
				signature = def.signature,
			}
			define_symbol(t, symbol) or_return
		case Def_Var:
			for pair in def.pairs {
				symbol := Symbol_Var {
					id   = pair.id,
					name = pair.name,
					type = pair.type,
				}
				define_symbol(t, symbol) or_return
			}
		case Def_Const:
			symbol := Symbol_Const {
				id   = def.id,
				name = def.name,
				type = def.type,
			}
			define_symbol(t, symbol) or_return
		case Def_Data:
			symbol := Symbol_Data {
				id   = def.id,
				name = def.name,
			}
			define_symbol(t, symbol) or_return
		case Def_Type_Alias:
			symbol := User_Type_Alias {
				id   = def.id,
				name = def.name,
				base = def.base,
			}
			define_symbol(t, Symbol_User_Type(symbol)) or_return
		case Def_Enum:
			symbol := User_Type_Enum {
				id       = def.id,
				name     = def.name,
				variants = make(map[string]Span),
			}
			for vari in def.variants {
				_, _, found := map_upsert(&symbol.variants, vari.name.s, vari.name.span)
				if found {
					panic("TODO: 'variant names collision' error")
				}
			}
			define_symbol(t, Symbol_User_Type(symbol)) or_return
		case Def_Struct:
			symbol := User_Type_Struct {
				id     = def.id,
				name   = def.name,
				fields = make(map[string]Struct_Field),
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
			define_symbol(t, Symbol_User_Type(symbol)) or_return
		}
	}

	return nil
}

@(require_results)
define_symbol :: proc(t: ^Typechecker, symbol: Symbol) -> (err: Error) {
	name := symbol_name(symbol).s
	_, _, found := map_upsert(&t.symbols, name, symbol)
	if found {
		panic("TODO: 'symbol redefinition' error")
	}
	return nil
}

@(require_results)
check_nodes :: proc(t: ^Typechecker, nodes: []Node) -> (ok: bool) {
	for &node in nodes {
		check_node(t, &node) or_return
	}
	return true
}

@(require_results)
check_node :: proc(t: ^Typechecker, node: ^Node) -> (ok: bool) {
	switch &n in node {
	case Def_Type_Alias, Def_Struct: // skip

	case Def_Func:
		check_def_func(t, &n) or_return
	case Def_Var:
		panic("TODO: check Def_Var")
	case Def_Const:
		panic("TODO: check Def_Const")
	case Def_Data:
		panic("TODO: check Def_Data")
	case Def_Enum:
		check_def_enum(t, &n) or_return

	case Expr_Symbol:
		panic("TODO: check Expr_Symbol")
	case Expr_Intr:
		panic("TODO: check Expr_Intr")
	case Expr_Byte:
		stack_push(&t.ws, make_type(Type_Byte{}), n.span)
	case Expr_Short:
		stack_push(&t.ws, make_type(Type_Short{}), n.span)
	case Expr_String:
		// Push `*[]byte`
		base := make_type(Type_Byte{})
		type := make_short_ptr(make_unsized_arr(base))
		stack_push(&t.ws, type, n.span)

		panic("TODO: define a data with this string contents.")
	case Expr_Store:
		panic("TODO: check Expr_Store")
	case Expr_Bind:
		panic("TODO: check Expr_Bind")
	case Expr_Expect:
		panic("TODO: check Expr_Expect")
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
			stack_push(&t.ws, input.type, input.name.span, input.name.s)
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
				"the %v stack is not empty at the end of the function `%v`",
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
			"the return stack is not empty at the end of the function `%v`",
			def.name.s,
		)
		stack_notes_caused_by(&t.rs, &err, len(t.rs.items))
		return error(t, err)
	}

	notes := make([dynamic]Note)

	// Check stack item types.
	for &item, idx in t.ws.items {
		output := &sig.outputs[idx]

		if !type_eq(item.type, output.type) {
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
check_def_enum :: proc(t: ^Typechecker, def: ^Def_Enum) -> (ok: bool) {
	all_ok := true

	for vari in def.variants {
		if body, ok := vari.body.?; ok {
			checker_reset(t)
			ok = check_nodes(t, body.nodes[:])
			all_ok &&= ok
		}
	}

	return all_ok
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
	append(&t.state.problems, problem)
	return false
}
