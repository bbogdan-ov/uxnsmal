package uxnsmal

import "core:fmt"
import "core:strings"

// TODO: allow change the file descriptor for outputing.
// TODO: allow disable the ansi escape codes.

ESC :: "\x1b["
GRAY :: "\x1b[37m"
BRED :: "\x1b[91m"
BYELLOW :: "\x1b[93m"
BCYAN :: "\x1b[96m"
RESET :: "\x1b[0m"

Reporter_Line :: struct {
	s:        string,
	number:   int,
	hl_start: int,
	hl_end:   int,
}

reporter_line_delete :: proc(l: Reporter_Line) {
	delete(l.s)
}

// Pretty print problems into the stdout.
report_problems :: proc(problems: []Problem, source: string) {
	for p in problems {
		report_problem(p, source)
	}
}

// Pretty print a single problem into the stdout.
report_problem :: proc(problem: Problem, source: string) {
	switch problem.kind {
	case .Error:
		_print_msg("error", BRED, problem.msg, problem.span)
		_print_source(source, BRED, problem.span)
	case .Warn:
		_print_msg("warning", BYELLOW, problem.msg, problem.span)
		_print_source(source, BYELLOW, problem.span)
	}

	for note in problem.notes {
		_print_msg("note", BCYAN, note.msg, note.span)
		_print_source(source, BCYAN, note.span)
	}

	fmt.println()
}

@(private)
_print_msg :: proc(label, color, msg: string, span: Span) {
	fmt.printfln("%d:%d %s%s\x1b[0m: %s", span.line + 1, span.column + 1, color, label, msg)
}

@(private)
_print_source :: proc(source: string, color: string, span: Span) {
	lines := _format_source(source, color, span)
	defer delete(lines)

	for line in lines {
		fmt.printf("\x1b[37m% 4d|\x1b[0m ", line.number, flush = false)
		fmt.println(line.s)

		fmt.printf("    \x1b[37m| %s", color, flush = false)

		for _ in 0 ..< line.hl_start {
			fmt.print(' ', flush = false)
		}
		for _ in 0 ..< line.hl_end - line.hl_start {
			fmt.print('^', flush = false)
		}
		fmt.println("\x1b[0m")
	}

	for line in lines {
		reporter_line_delete(line)
	}
}

@(private)
_format_source :: proc(source: string, color: string, span: Span) -> [dynamic]Reporter_Line {
	assert(span.start <= span.end)

	lines := make([dynamic]Reporter_Line)
	sb := strings.builder_make()
	defer strings.builder_destroy(&sb)

	source_bytes := transmute([]u8)source

	line_started := true
	line_idx := 0
	line_offset := 0
	hl_start := -1
	hl_end := -1

	loop: for byte, idx in source_bytes {
		if line_idx < span.line {
			if byte == '\n' {
				line_idx += 1
				line_started = true
			}
			continue
		}
		if line_started {
			line_started = false
			line_offset = 0
			inner: for jb, j in source_bytes[idx:] {
				if idx + j <= span.end {
					break inner
				}
				if jb == '\n' {
					break loop
				}
			}
		}

		if hl_start < 0 && idx >= span.start {
			hl_start = line_offset
		}
		if idx <= span.end {
			hl_end = line_offset
		}

		if byte == '\n' {
			assert(hl_start >= 0)
			assert(hl_end >= 0)

			s := strings.clone(strings.to_string(sb))
			append(&lines, Reporter_Line{s, line_idx + 1, hl_start, hl_end})
			strings.builder_reset(&sb)

			line_idx += 1
			line_started = true
			hl_start = -1
			hl_end = -1
		} else if byte == '\t' {
			strings.write_string(&sb, "    ")
			line_offset += 4
		} else {
			strings.write_rune(&sb, rune(byte))
			line_offset += 1
		}
	}

	return lines
}
