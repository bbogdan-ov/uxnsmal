#+vet explicit-allocators

package uxnsmal

import "core:fmt"
import "core:strings"

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
problem :: proc(span: Span, msg: string, kind := Problem_Kind.Error) -> Problem {
	notes := make([dynamic]Note, context.allocator)
	return Problem{kind, strings.clone(msg, context.allocator), notes, span}
}
problemf :: proc(span: Span, format: string, args: ..any, kind := Problem_Kind.Error) -> Problem {
	notes := make([dynamic]Note, context.allocator)
	return Problem{kind, fmt.aprintf(format, ..args, allocator = context.allocator), notes, span}
}
