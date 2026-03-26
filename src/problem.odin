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
