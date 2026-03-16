package main

import "core:fmt"
import "core:os"
import "core:slice"
import "core:unicode/utf8"

import ast "../src/ast"

main :: proc() {
	file_path, ok := slice.get(os.args, 1)
	if !ok {
		fmt.eprintln("ERROR: no input file")
		os.exit(1)
	}

	data, err := os.read_entire_file_from_path(file_path, context.allocator)
	if err != nil {
		fmt.eprintfln("ERROR: Failed to read %s: %s", file_path, err)
		os.exit(1)
	}

	source := string(data)
	if !utf8.valid_string(source) {
		fmt.eprintln("ERROR: Source file is not a valid UTF-8")
		os.exit(1)
	}

	//

	parser: ast.Parser
	ast.parse_file(&parser, source)

	fmt.println("OK")
}
