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

	state: smal.State
	defer smal.destroy(&state)
	ok = compile(&state, source)
	if !ok {
		smal.report_problems(state.problems[:], source)
		os.exit(1)
	}

	fmt.printfln("OK")
}

compile :: proc(state: ^smal.State, source: string) -> (ok: bool) {
	smal.init(state, source)

	smal.parse(state) or_return
	smal.typecheck(state) or_return

	return true
}
