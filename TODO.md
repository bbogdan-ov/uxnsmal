TODO: add `shl` (shift left) and `shr` (shift right) intrisincs as an replacement/addition to `shift`.

FIXME: fix "structs cannot be structs" error when trying to access a field of a struct type.

TODO: replace `untyped` keyword with `alias` so you can define alias enums and
alias types with no need in a dedicated syntax for both.

TODO: add `raw` block which allows you to write UXNTAL assembly and can
interact with symbols from the outside (call functions, take pointers, etc).
It also should accept a signature just like functions because it may modify the stack.
Example:
```smal
fun on-reset ( -> ) {
	raw ( -- byte ) {
		2 0x11 ADD
		// But no UXNTAL labels i think?..
		// @label &inner-label
	}
	raw ( -- ) {
		0xabcd* 2* MUL my-proc // call my-proc
	}
}
fun my-proc ( short -- ) { /* ... */ }
```
