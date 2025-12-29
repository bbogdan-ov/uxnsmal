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


TODO: `as (...)` should expect stack items to be of the same size as types in
the (), (e.g. `10 20 as (short)` should error) but if you really want your
bytes to become a single short you should do `10 20 as! (short)`.
(or come up with a different syntax)


TODO: replace binding syntax `-> (a b)` to `: (a b)`.
I think it looks more consistant with functions signature `( byte:a byte:b -- short:c )`


TODO: add `switch` construction as a replacement to `if {} elif {} else {}` chain.
Example:
```smal
13 switch {
	// `case` implicitly duplicates 13
	case 'a'       eq  { pop /* ... */ }
	case 'b'       neq { pop /* ... */ }
	case 'c'       gth { pop /* ... */ }
	case func-call eq  { pop /* ... */ }
	else { /* none of the cases above executed */ }
}
```
