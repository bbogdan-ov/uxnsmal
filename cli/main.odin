package main

import "core:fmt"
import "core:os"
import "core:slice"
import "core:unicode/utf8"

import smal "../src"

main :: proc() {
	file_path, ok := slice.get(os.args, 1)
	if !ok {
		fmt.eprintln("ERROR: no input file")
		os.exit(1)
	}

	data, read_err := os.read_entire_file_from_path(file_path, context.allocator)
	if read_err != nil {
		fmt.eprintfln("ERROR: Failed to read %s: %s", file_path, read_err)
		os.exit(1)
	}

	source := string(data)
	if !utf8.valid_string(source) {
		fmt.eprintln("ERROR: Source file is not a valid UTF-8")
		os.exit(1)
	}

	//

	parser: smal.Parser
	err := smal.parse(&parser, source)
	if problem, ok := err.(smal.Problem); ok {
		smal.report_problem(problem, source)
		os.exit(1)
	}

	fmt.printfln("%#w", parser.file.nodes[:])
}
