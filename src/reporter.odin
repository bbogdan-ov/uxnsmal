package uxnsmal

import "core:fmt"
import "core:strings"
import "core:unicode/utf8"

// TODO: allow change the file descriptor for outputing.
// TODO: allow disable the ansi escape codes.

ESC :: "\x1b["
GRAY :: "\x1b[37m"
BRED :: "\x1b[91m"
BYELLOW :: "\x1b[93m"
BCYAN :: "\x1b[96m"
RESET :: "\x1b[0m"

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

	fmt.println()
}

@(private)
_print_msg :: proc(label, color, msg: string, span: Span) {
	fmt.printfln("%d:%d %s%s\x1b[0m: %s", span.line + 1, span.column + 1, color, label, msg)
}

@(private)
_print_source :: proc(source: string, color: string, span: Span) {
	assert(span.start <= span.end)

	line_start, line_end := 0, 0
	line_idx := 0

	// FIXME!: this code won't correctly display lines and underlines if span
	// takes up multiple of them.

	loop: for {
		// Iterate over lines
		newline_idx := strings.index_byte(source[line_start:], '\n')
		if newline_idx < 0 {
			line_end = line_start
		} else {
			line_end = line_start + newline_idx
		}

		skip: {
			if line_idx < span.line do break skip

			// Render the line which contains the span.
			line := source[line_start:line_end]
			trimmed := strings.trim_left_space(line)
			len_diff := len(line) - len(trimmed)
			fmt.printfln("\x1b[37m% 4d|\x1b[0m %s", line_idx + 1, trimmed)

			// Render underline.
			under_len := max(utf8.rune_count(source[span.start:span.end]), 1)
			fmt.print("    \x1b[37m|\x1b[0m \x1b[91m")
			for _ in 0 ..< span.column - len_diff {
				fmt.print(" ")
			}
			for _ in 0 ..< under_len {
				fmt.print("^")
			}
			fmt.println("\x1b[0m")

			if line_idx >= span.line do break loop
		}

		if newline_idx < 0 do break

		line_idx += 1
		line_start = line_end + 1
	}
}
