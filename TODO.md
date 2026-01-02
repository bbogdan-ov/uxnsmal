TODO: add `shl` (shift left) and `shr` (shift right) intrisincs as an replacement/addition to `shift`.


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


TODO: add `switch` construction as an addition to `if {} elif {} else {}` chain.
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


TODO: allow initialize rom variables just like data blocks.
Example:
```smal
rom var [100]byte my-var // zero-initialized
rom var [100]byte my-var { 1 2 0xabcd* 'a' "string" /* other bytes are zeroed */ }
rom var [10]Enemy enemies { /* but what about structs?.. */ }
```


TODO: introduce fixed-point numbers.
Example:
```smal
fun on-reset ( -> ) {
	12.00 add-2 // => 14.00

	// `mul` and `div` should generate different IR based on the number of
	// digits in the fractional part of the number.
	2.00 3.00 mul // => 6.00
	3.00 2.00 div // => 1.50

	25.5  // ok, `byte.1`
	2.55  // ok, `byte.2`
	0.255 // ok, `byte.3`

	6.5535*  // ok, `short.4`
	0.65535* // ok, `short.5`

	1.255    // errors because exceeds 1 byte limit.
	1.65535* // errors because exceeds 2 byte limit of short.
}

// Function that accepts a short with 2 digits after the dot.
fun add-2 ( short.2 -- short.2 ) {
	2.00* add
}
```


TODO: introduce bit-structs, don't really come up with the syntax yet.
Need to steal the syntax from other languages.
