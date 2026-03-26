package uxnsmal

import "base:runtime"

State :: struct #all_or_none {
	// Immutable reference to a UXNSMAL source code string.
	source:    string,
	nodes:     [dynamic]Node,
	problems:  [dynamic]Problem,

	// Arena allocator for everything except problems.
	// TODO: allow specify a custom allocator for problem message strings
	arena:     runtime.Arena,
	allocator: runtime.Allocator,
}

init :: proc(s: ^State, source: string) {
	s.source = source
	s.allocator = runtime.arena_allocator(&s.arena)
	s.nodes = make([dynamic]Node, s.allocator)
	s.problems = make([dynamic]Problem, s.allocator)
}

destroy :: proc(s: ^State) {
	free_all(s.allocator)
	clear(&s.nodes)
	clear(&s.problems)

	s.nodes = nil
	s.problems = nil
}
