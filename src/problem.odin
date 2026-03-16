package uxnsmal

import "core:fmt"

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
	return Problem{kind, msg, span}
}
problemf :: proc(span: Span, format: string, args: ..any, kind := Problem_Kind.Error) -> Problem {
	return problem(span, fmt.aprintf(format, ..args, allocator = context.allocator), kind)
}
