package uxnsmal

import "core:fmt"
import "core:math"
import "core:strings"

Error :: Maybe(Problem)

Problem_Kind :: enum {
	Error,
	Warn,
}

Note_Specific :: struct {
	msg:  string,
	span: Span,
}

Note_General :: struct {
	msg:  string,
}

Note :: union {
	Note_Specific,
	Note_General,
}

Problem :: struct {
	kind:  Problem_Kind,
	msg:   string,
	notes: [dynamic]Note,
	span:  Span,
}

// TODO: problems should live somewhere else in memory, not in the `State` arena allocator.
problemf :: proc(
	span: Span,
	format: string,
	args: ..any,
	kind := Problem_Kind.Error,
	loc := #caller_location,
) -> Problem {
	assert(span_valid(span), loc = loc)
	notes := make([dynamic]Note)
	return Problem{kind, fmt.aprintf(format, ..args), notes, span}
}

notef :: proc(span: Span, format: string, args: ..any, loc := #caller_location) -> Note {
	assert(span_valid(span), loc = loc)
	return Note_Specific{fmt.aprintf(format, ..args), span}
}

problem_notef :: proc(
	problem: ^Problem,
	span: Span,
	format: string,
	args: ..any,
	loc := #caller_location,
) {
	assert(span_valid(span), loc = loc)
	append(&problem.notes, notef(span, format, ..args))
}

problem_note_stack :: proc(
	problem: ^Problem,
	items: []Item,
	label: string,
	include_name := true,
) {
	sb := strings.builder_make()
	strings.write_string(&sb, label)
	strings.write_string(&sb, " ( ")
	for item in items {
		item_sbprint(&sb, item, include_name)
		strings.write_rune(&sb, ' ')
	}
	strings.write_string(&sb, ")")
	append(&problem.notes, Note_General{strings.to_string(sb)})
}

problem_note_expected_stacks :: proc(
	problem: ^Problem,
	expected, got: []Item,
	include_name := true
) {
	problem_note_stack(problem, expected, "expected:", include_name)
	problem_note_stack(problem, got, "     got:", include_name)
}

// ------------------------------
// Error helper functions.
// ------------------------------

err_symbol :: proc(span, defined_at: Span, format: string, args: ..any) -> Problem {
	err := problemf(span, format, ..args)
	problem_notef(&err, defined_at, "defined here")
	return err
}

// ------------------------------
// Message generation helper functions.
// These functions generate human readable problem messages and allocate them
// on the context.temp_allocator.
// ------------------------------

msg_n_values :: proc(#any_int n: int) -> string {
	if n == 1 {
		return "1 value"
	} else {
		return fmt.tprintf("%d values", n)
	}
}
msg_values_diff :: proc(#any_int diff: int) -> string {
	n := math.abs(diff)
	if diff > 0 {
		if n == 1 do return "spitting 1 value"
		else do return fmt.tprintf("spitting %d values", n)
	} else if diff < 0 {
		if n == 1 do return "consuming 1 value"
		else do return fmt.tprintf("consuming %d values", n)
	} else {
		return "0 values"
	}
}

msg_n_bytes :: proc(#any_int n: int) -> string {
	if n == 1 {
		return "1 byte"
	} else {
		return fmt.tprintf("%d bytes", n)
	}
}

msg_n_types :: proc(#any_int n: int) -> string {
	if n == 1 {
		return "1 type"
	} else {
		return fmt.tprintf("%d types", n)
	}
}

msg_n_names :: proc(#any_int n: int) -> string {
	if n == 1 {
		return "1 name"
	} else {
		return fmt.tprintf("%d names", n)
	}
}

msg_n_inputs :: proc(#any_int n: int) -> string {
	if n == 1 {
		return "1 input"
	} else {
		return fmt.tprintf("%d inputs", n)
	}
}

msg_there_n_values_on_stack :: proc(s: ^Stack) -> string {
	n := len(s.items)
	name := stack_name(s.kind)
	if n == 0 {
		return fmt.tprintf("there are no values on the %s stack", name)
	} else if n == 1 {
		return fmt.tprintf("there is 1 value on the %s stack", name)
	} else {
		return fmt.tprintf("there are %d values on the %s stack", n, name)
	}
}

msg_stack :: proc(items: []Item, include_name := true) -> string {
	sb := strings.builder_make(context.temp_allocator)
	strings.write_string(&sb, "( ")
	for item in items {
		item_sbprint(&sb, item, include_name)
		strings.write_rune(&sb, ' ')
	}
	strings.write_string(&sb, ")")
	return strings.to_string(sb)
}
