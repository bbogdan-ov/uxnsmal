package uxnsmal

import "core:fmt"

Error :: Maybe(Problem)

Problem_Kind :: enum {
	Error,
	Warn,
}

Note :: struct {
	msg:  string,
	span: Span,
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
	return Note{fmt.aprintf(format, ..args), span}
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
// on the temp allocator.
// ------------------------------

msg_n_values :: proc(n: int) -> string {
	if n == 0 {
		return "nothing"
	} else if n == 1 {
		return "1 value"
	} else {
		return fmt.tprintf("%d values", n)
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
