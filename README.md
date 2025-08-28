# UXNSMAL

> [!WARNING]
> **WIP**
> This language is very experimental, anything can be changed or removed without notice!!!
> So i don't recommend you to use it for your projects untill it is ready. Have fun

UXNSMAl or SMAL is a [concatenative][] [stack-oriented][] and staticaly typed
programming language made for [UXN][] virtual machine

[concatenative]: https://en.wikipedia.org/wiki/Concatenative_programming_language
[stack-oriented]: https://en.wikipedia.org/wiki/Stack-oriented_programming
[UXN]: https://100r.co/site/uxn.html

## TODO

List of features i want to implement

- [ ] Syntax sugar
	- [ ] If-else and While blocks
	      Currently only blocks and infinite loops are available
	- [ ] Enums
	- [ ] Including/importing any file in any place
- [ ] Better error reporting
	- [ ] Collect as many errors as possible before exiting.
	      Currently only one error is being reported
	- [ ] Help messages with small examples based on the error context
- [ ] Code optimization
      Currently there is no optimizations at all
	- [ ] Dead code elimination (code that will never be executed)
	- [ ] Function inlining
	- [ ] Compile-time evaluation
	- [ ] [Peephole optimization][]
- [ ] [Metaprogramming][]?
- [ ] Something else?...

[Peephole optimization]: https://en.wikipedia.org/wiki/Peephole_optimization
[Metaprogramming]: https://en.wikipedia.org/wiki/Metaprogramming

## Building

```console
$ cargo build --release
$ cp ./target/release/uxnsmal-cli ./uxnsmal
$ ./uxnsmal examples/hello.smal
$ uxnemu output.rom
```

or

```console
$ cargo run --release -- examples/hello.smal
$ uxnemu output.rom
```

## Examples

```uxnsmal
// HELLO WORLD example

// VARVARA console device
// Dots are allowed in symbol names
const byte Console.write { 0x18 }

// 'on-reset' vector function is always required
fun on-reset ( -> ) {
	// Push string address onto the working stack
	// It will be stored in the output ROM
	"Hello world!!\n\0" -> (str-ptr)

	loop @break {
		// Break if the current char is equal to 0
		load-k 0 eq jumpif @break

		// Load the current char without consuming the string pointer
		load-k -> (char)
		// Print it!
		char Console.write output

		// Increment the pointer so it points to a next char
		str-ptr inc
	}

	// Clean up
	str-ptr pop
}
```

```uxnsmal
// SPRITE example
// See examples/sprite.smal for more explanation

/// VARVARA system device
const byte System.r { 0x08 }
const byte System.g { 0x0a }
const byte System.b { 0x0c }

/// VARVARA screen device
const byte Screen.vector { 0x20 }
const byte Screen.width  { 0x22 }
const byte Screen.height { 0x24 }
const byte Screen.auto   { 0x26 }
const byte Screen.x      { 0x28 }
const byte Screen.y      { 0x2a }
const byte Screen.addr   { 0x2c }
const byte Screen.pixel  { 0x2e }
const byte Screen.sprite { 0x2f }

fun on-reset ( -> ) {
	// Set color palette
	0xf07f* System.r output
	0xf0d6* System.g output
	0xf0b2* System.b output

	// Set window size
	64* Screen.width output
	64* Screen.height output

	// Set current sprite address
	&my-sprite Screen.addr output
	// Place the sprite somewhere
	16* Screen.x output
	32* Screen.y output
	// Draw it!
	0b00000011 Screen.sprite output
}

// 8x8 1bit sprite
data my-sprite {
	0b01111110
	0b11111111
	0b10111101
	0b10111101
	0b11111111
	0b10111101
	0b11000011
	0b01111110
}
```

![SPRITE example](./res/sprite-example.png)

## Reference

TODO:

## Resources

- [UXN reference](https://wiki.xxiivv.com/site/uxntal_reference.html)
- [WebAssembly type-checking](https://binji.github.io/posts/webassembly-type-checking)
- [PORTH](https://gitlab.com/tsoding/porth)
- [PORTH development series](https://youtube.com/playlist?list=PLpM-Dvs8t0VbMZA7wW9aR3EtBqe2kinu4&si=7HwCcRhAZqfkGGC_)
