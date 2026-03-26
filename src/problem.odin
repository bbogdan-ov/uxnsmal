#+vet explicit-allocators

package uxnsmal

import "core:fmt"
import "core:strings"

Error :: Maybe(Problem)

Problem_Kind :: enum {
	Error,
	Warn,
}

Problem :: struct {
	kind: Problem_Kind,
	msg:  string,
	span: Span,
}

problem :: proc(span: Span, msg: string, kind := Problem_Kind.Error) -> Problem {
	return Problem{kind, strings.clone(msg, context.allocator), span}
}
problemf :: proc(span: Span, format: string, args: ..any, kind := Problem_Kind.Error) -> Problem {
	return Problem{kind, fmt.aprintf(format, ..args, allocator = context.allocator), span}
}
