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
problemf :: proc(span: Span, format: string, args: ..any, kind := Problem_Kind.Error) -> Problem {
	notes := make([dynamic]Note)
	return Problem{kind, fmt.aprintf(format, ..args), notes, span}
}

notef :: proc(span: Span, format: string, args: ..any) -> Note {
	return Note{fmt.aprintf(format, ..args), span}
}

problem_notef :: proc(problem: ^Problem, span: Span, format: string, args: ..any) {
	append(&problem.notes, notef(span, format, ..args))
}

// ------------------------------
// Message generation functions.
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
