package uxnsmal

import "base:runtime"

// Unique symbol definition ID.
// Should never be <= 0.
ID :: distinct u32

State :: struct #all_or_none {
	// Immutable reference to a UXNSMAL source code string.
	source:    string,
	nodes:     [dynamic]Node,
	problems:  [dynamic]Problem,
	id_count:  u32,

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
	runtime.arena_destroy(&s.arena)

	s.nodes = nil
	s.problems = nil
}

// Create a new unique ID.
@(require_results)
make_id :: proc(s: ^State) -> ID {
	// NOTE: increment first so ID is never 0.
	s.id_count += 1
	return ID(s.id_count)
}
